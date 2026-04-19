/* stackvm.c - small demonstration language */
/* PUBLIC DOMAIN - Jon Mayo
 * original: June 23, 2011
 * updated: November 10, 2019 */
#include <assert.h>
#include <ctype.h>
#include <errno.h>
#include <inttypes.h>
#include <limits.h>
#include <math.h>
#include <stdarg.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "stackvm.h"

#if 0 /* useful for debugging */
#include "hexdump.c"
#endif

int stackvm_verbose = 0;

/* logging macros */
#define error(format, ...) fprintf(stderr, "ERROR:%s():%d:" format, __func__, __LINE__, ## __VA_ARGS__)
#define warn(format, ...) fprintf(stderr, "WARN:" format, ## __VA_ARGS__)
#define info(format, ...) do { if (stackvm_verbose > 0) fprintf(stderr, "INFO:" format, ## __VA_ARGS__); } while(0)
#ifdef DEBUG_ENABLED
#define debug(format, ...) fprintf(stderr, "DEBUG:%s():%d:" format, __func__, __LINE__, ## __VA_ARGS__)
#define trace(format, ...) fprintf(stderr, "TRACE:%s():%d:" format, __func__, __LINE__, ## __VA_ARGS__)
#else
#define debug(format, ...) /* disabled debug messages */
#define trace(format, ...) /* disabled trace messages */
#endif

#define vm_error_set(vm, flag) do { \
		trace("set error:%#x\n", (flag)); \
		(vm)->status |= (flag); \
	} while(0)

/* #define strcasecmp stricmp */

#define ARRAY_SIZE(a) (sizeof(a) / sizeof *(a))

#define VM_STACK_SIZE 1024
#define PROGRAM_STACK_SIZE 0x10000
#define MAX_VMMAIN_ARGS 13

struct vm;

/* environment holds infomation common to multiple VMs */
struct vm_env {
	unsigned nr_syscalls;
	void (**syscalls)(struct vm *vm);
};

struct vm {
	const struct vm_env *env;
	void *extra;
	int yield; /* set if we run_slice should yield after system calls */
	/* code is a read-only raw byte stream of the CODE segment.
	 * pc is a byte offset into this buffer. */
	uint8_t *code;
	size_t code_len;
	/* map instruction-index → byte offset within code.
	 * Q3VM bytecode encodes branch/call targets as instruction ordinals,
	 * not byte offsets, so every target that enters PC is translated here. */
	uint32_t *instr_to_byte;
	size_t nr_instructions;
	/* heap is the RAM area for data */
	union {
		vmword_t *words;
		uint16_t *halfs;
		uint8_t *bytes;
	} heap;
	size_t heap_len;
	size_t heap_mask;
	int status; /* stop loop when non-zero */
	vmword_t pc; /* program counter */
	vmword_t psp; /* program stack pointer */
	vmword_t stack_bottom; /* end of the program stack */ // TODO: rename this
	vmword_t stack[VM_STACK_SIZE] __attribute__ ((aligned (__BIGGEST_ALIGNMENT__))); /* op stack */
	unsigned op_stack;
	/* bootstrap and input parameters */
	char *vm_filename;
};

static char *opcode_to_name[] = {
	"UNDEF", "IGNORE", "BREAK", "ENTER",
	"LEAVE", "CALL", "PUSH", "POP",
	"CONST", "LOCAL", "JUMP", "EQ",
	"NE", "LTI", "LEI", "GTI",
	"GEI", "LTU", "LEU", "GTU",
	"GEU", "EQF", "NEF", "LTF",
	"LEF", "GTF", "GEF", "LOAD1",
	"LOAD2", "LOAD4", "STORE1", "STORE2",
	"STORE4", "ARG", "BLOCK_COPY", "SEX8",
	"SEX16", "NEGI", "ADD", "SUB",
	"DIVI", "DIVU", "MODI", "MODU",
	"MULI", "MULU", "BAND", "BOR",
	"BXOR", "BCOM", "LSH", "RSHI",
	"RSHU", "NEGF", "ADDF", "SUBF",
	"DIVF", "MULF", "CVIF", "CVFI",
};

struct vm_env *vm_env_new(unsigned nr_syscalls)
{

	struct vm_env *env = calloc(1, sizeof(*env));
	assert(env != NULL);
	env->nr_syscalls = nr_syscalls;
	env->syscalls = calloc(sizeof(*env->syscalls), nr_syscalls);
	assert(env->syscalls != NULL);
	return env;
}

int vm_env_register(struct vm_env *env, int syscall_num, void (*sc)(struct vm *vm))
{
	assert(syscall_num < 0);
	unsigned ofs = -1 - syscall_num;
	if (ofs >= env->nr_syscalls)
		return -1;
	env->syscalls[ofs] = sc;
	return 0;
}

static inline vmword_t dread4(struct vm *vm, vmword_t ofs);
static inline int check_stack_bounds(struct vm *vm);

/* return 0 if returning normally, or 1 if from a syscall */
static int vm_leave(struct vm *vm, unsigned local_size)
{
	vm->psp += local_size; /* remove the frame added by ENTER */
	vmword_t psp = vm->psp;
	vmword_t pc = dread4(vm, psp);
	trace("LEAVE to %d (%#x) from %d (%#x)\n", pc, pc, vm->pc, vm->pc);
	trace("LEAVE stack=%d\n", vm->op_stack);
	assert(pc != 0xdeadbeef);
	vm->pc = pc;
	if ((int)pc == -1) {
		/* re-entrant call's prepare_call saved caller psp at psp+4 */
		vm->psp = dread4(vm, psp + 4);
		info("%s:finished or returning to call\n", vm->vm_filename);
		return 1;
	}
	return 0;
}

static void opush(struct vm *vm, vmword_t val);

static int vm_env_call(const struct vm_env *env, int syscall_num, struct vm *vm)
{
	fprintf(stderr, "======== VM Call #%d : Start ========\n",
		-1 - syscall_num);
	debug("pc=%d (%#x) psp=%d (%#x)\n", vm->pc, vm->pc, vm->psp, vm->psp);
	assert(syscall_num < 0);
	unsigned ofs = -1 - syscall_num;
	if (ofs >= env->nr_syscalls)
		goto out_error;
	void (*sc)(struct vm *vm) = env->syscalls[ofs];
	if (!sc) // TODO: catch this as an error
		goto out_error;
	/* syscalls don't use the VM frame convention: no ENTER/LEAVE.
	 * caller (CALL dispatch) saves/restores vm->pc around this. */
	unsigned old_stack = vm->op_stack;
	sc(vm); // TODO: check for errors
	if (vm->status)
		goto out_error;
	if (vm->op_stack != old_stack + 1) {
		trace("syscall did not leave correct amount of data on stack. old=%d new=%d\n",
			old_stack, vm->op_stack);
		vm->op_stack = old_stack;
		opush(vm, 0);
		// TODO: set an error flag instead of trying to fix it.
	}
	fprintf(stderr, "======== VM Call #%d : Success ========\n", ofs);
	debug("pc=%d (%#x) psp=%d (%#x)\n", vm->pc, vm->pc, vm->psp, vm->psp);
	return 0;
out_error:
	fprintf(stderr, "======== VM Call #%d : Error ========\n", ofs);
	debug("pc=%d (%#x) psp=%d (%#x)\n", vm->pc, vm->pc, vm->psp, vm->psp);
	return -1;
}

/* returns number of bytes an opcode will consume.
 * 0 if an unknown or illegal opcode. */
static unsigned opcode_length(unsigned char op)
{
	unsigned len = 1;

	switch (op) {
	case 0x00: /* UNDEF*/
	case 0x01: /* IGNORE */
	case 0x02: /* BREAK */
		break;
	case 0x03: /* ENTER */
	case 0x04: /* LEAVE */
		len = 5;
		break;
	case 0x05: /* CALL */
	case 0x06: /* PUSH */
	case 0x07: /* POP */
		break;
	case 0x08: /* CONST x */
	case 0x09: /* LOCAL x */
		len = 5;
		break;
	case 0x0a: /* JUMP */
		break;
	case 0x0b: /* EQ x */
	case 0x0c: /* NE x */
	case 0x0d: /* LTI x */
	case 0x0e: /* LEI x */
	case 0x0f: /* GTI x */
	case 0x10: /* GEI x */
	case 0x11: /* LTU x */
	case 0x12: /* LEU x */
	case 0x13: /* GTU x */
	case 0x14: /* GEU x */
	case 0x15: /* EQF x */
	case 0x16: /* NEF x */
	case 0x17: /* LTF x */
	case 0x18: /* LEF x */
	case 0x19: /* GTF x */
	case 0x1a: /* GEF x */
		len = 5;
		break;
	case 0x1b: /* LOAD1 */
	case 0x1c: /* LOAD2 */
	case 0x1d: /* LOAD4 */
	case 0x1e: /* STORE1 */
	case 0x1f: /* STORE2 */
	case 0x20: /* STORE4 */
		break;
	case 0x21: /* ARG x */
		len = 2;
		break;
	case 0x22: /* BLOCK_COPY x */
	case 0x23: /* SEX8 */
	case 0x24: /* SEX16 */
	case 0x25: /* NEGI */
	case 0x26: /* ADD */
	case 0x27: /* SUB */
	case 0x28: /* DIVI */
	case 0x29: /* DIVU */
	case 0x2a: /* MODI */
	case 0x2b: /* MODU */
	case 0x2c: /* MULI */
	case 0x2d: /* MULU */
	case 0x2e: /* BAND */
	case 0x2f: /* BOR */
	case 0x30: /* BXOR */
	case 0x31: /* BCOM */
	case 0x32: /* LSH */
	case 0x33: /* RSHI */
	case 0x34: /* RSHU */
	case 0x35: /* NEGF */
	case 0x36: /* ADDF */
	case 0x37: /* SUBF */
	case 0x38: /* DIVF */
	case 0x39: /* MULF */
	case 0x3a: /* CVIF */
	case 0x3b: /* CVFI */
		break;
	default:
		return 0; /* failure */
	}

	return len;
}

static inline uint32_t read_imm4(const uint8_t *p)
{
	return (uint32_t)p[0]
	     | ((uint32_t)p[1] << 8)
	     | ((uint32_t)p[2] << 16)
	     | ((uint32_t)p[3] << 24);
}

static inline uint8_t read_imm1(const uint8_t *p)
{
	return p[0];
}

/* translate a Q3VM instruction-index address to a byte offset in vm->code.
 * sets VM_ERROR_OUT_OF_BOUNDS and returns 0 on an out-of-range index. */
static vmword_t pc_from_addr(struct vm *vm, vmword_t addr)
{
	if (addr >= vm->nr_instructions) {
		vm_error_set(vm, VM_ERROR_OUT_OF_BOUNDS);
		return 0;
	}
	return vm->instr_to_byte[addr];
}

/* format a single opcode at byte offset `ofs` within `code`.
 * if the opcode is illegal or truncated, returns a best-effort string. */
static const char *disassemble_opcode(const uint8_t *code, size_t ofs, size_t code_len)
{
	static char buf[256];
	unsigned b = code[ofs];
	unsigned len = opcode_length(b);

	if (len == 0 || b >= ARRAY_SIZE(opcode_to_name)) {
		snprintf(buf, sizeof(buf), "0x%02x (bad)", b & 255);
		return buf;
	}

	if (len > code_len - ofs) {
		snprintf(buf, sizeof(buf), "%s [0x%02x] (truncated)",
		         opcode_to_name[b], b);
		return buf;
	}

	if (len == 1) {
		snprintf(buf, sizeof(buf), "%s [0x%02x]",
		         opcode_to_name[b], b);
	} else if (len == 2) {
		unsigned p = read_imm1(code + ofs + 1);
		snprintf(buf, sizeof(buf), "%s %d [0x%02x %#x]",
		         opcode_to_name[b], p, b, p);
	} else if (len == 5) {
		uint32_t p = read_imm4(code + ofs + 1);
		snprintf(buf, sizeof(buf), "%s %d [0x%02x %#x]",
		         opcode_to_name[b], (int)p, b, p);
	} else {
		snprintf(buf, sizeof(buf), "%s [0x%02x] (bad len=%u)",
		         opcode_to_name[b], b, len);
	}

	return buf;
}

static void disassemble(FILE *out, const uint8_t *code, size_t code_len, vmword_t baseaddr)
{
	fprintf(out, "---8<--- start of disassembly (bytes=%zd) ---8<---\n", code_len);

	size_t p = 0;
	while (p < code_len) {
		unsigned len = opcode_length(code[p]);
		fprintf(out, "%06x: %s\n",
		        baseaddr + (unsigned)p,
		        disassemble_opcode(code, p, code_len));
		if (len == 0 || len > code_len - p)
			break; /* cannot safely advance */
		p += len;
	}

	fprintf(out, "---8<--- end of disassembly ---8<---\n");
}

/* round up len to next power of two minus one */
static size_t make_mask(size_t len)
{
	size_t ret = 0;

	while (ret + 1 < len)
		ret = (ret << 1) | 1;

	return ret;
}

static inline int _check_code_bounds(const char *func, unsigned line, struct vm *vm, vmword_t ofs)
{
	if (ofs >= vm->code_len) {
		error("%s():%d:ofs=%d (%#x)\n", func, line, ofs, ofs);
		vm_error_set(vm, VM_ERROR_OUT_OF_BOUNDS);
		return -1;
	}

	return 0;
}

#define check_code_bounds(vm, ofs) do { \
	if ((ofs) >= (vm)->code_len) { \
		vm_error_set(vm, VM_ERROR_OUT_OF_BOUNDS); \
	} } while (0)

static inline int check_data_bounds(struct vm *vm, vmword_t ofs)
{
	if (ofs & ~vm->heap_mask) {
		vm_error_set(vm, VM_ERROR_OUT_OF_BOUNDS);
		return -1;
	}

	return 0;
}

static inline int check_stack_bounds(struct vm *vm)
{
	if (vm->psp < vm->stack_bottom) {
		vm_error_set(vm, VM_ERROR_STACK_OVERFLOW);
		return -1;
	}

	return check_data_bounds(vm, vm->psp);
}

/* push a value onto the op stack */
static void opush(struct vm *vm, vmword_t val)
{
	trace("%s:PUSH %d\n", vm->vm_filename, val);

	if (vm->op_stack < ARRAY_SIZE(vm->stack))
		vm->stack[vm->op_stack++] = val;
	else
		vm_error_set(vm, VM_ERROR_STACK_OVERFLOW);
}

#if 0
/* peek a value from the op stack
 * negative numbers start from most recent entry. (-1 = newest)
 * positive numbers start from oldest entry on stack. (0 = oldest) */
static vmword_t opeek(struct vm *vm, int index)
{
	unsigned ofs = index < 0 ? vm->op_stack + index : (unsigned)index;

	if (ofs < vm->op_stack)
		return vm->stack[ofs];

	vm_error_set(vm, VM_ERROR_STACK_UNDERFLOW);
	return 0xdeadbeef;
}
#endif

/* pop a value from the op stack */
static vmword_t opop(struct vm *vm)
{
	if (vm->op_stack) {
		vmword_t val = vm->stack[--vm->op_stack];
		trace("%s:POP %d\n", vm->vm_filename, val);
		return val;
	}

	vm_error_set(vm, VM_ERROR_STACK_UNDERFLOW);
	return 0xdeadbeef;
}

/* push a value onto the op stack */
static void opushf(struct vm *vm, vmsingle_t val)
{
	static_assert(sizeof(val) == sizeof(vmword_t), "vmword_t and vmsingle_t must be of equal size");
	if (vm->op_stack < ARRAY_SIZE(vm->stack)) {
		vmword_t bits;
		memcpy(&bits, &val, sizeof(bits));
		vm->stack[vm->op_stack++] = bits;
	} else {
		vm_error_set(vm, VM_ERROR_STACK_OVERFLOW);
	}
}

/* pop a value from the op stack */
static vmsingle_t opopf(struct vm *vm)
{
	if (vm->op_stack) {
		vmword_t bits = vm->stack[--vm->op_stack];
		vmsingle_t val;
		memcpy(&val, &bits, sizeof(val));
		return val;
	}

	vm_error_set(vm, VM_ERROR_STACK_UNDERFLOW);
	return NAN;
}

static inline void dwrite4(struct vm *vm, vmword_t ofs, vmword_t val)
{
	trace("%s:write %d (%#x) : %d\n", vm->vm_filename, ofs, ofs, val);

	if (check_data_bounds(vm, ofs) || check_data_bounds(vm, ofs + 3))
		return;

	if (ofs & 3) {
		vm_error_set(vm, VM_ERROR_UNALIGNED);
		return;
	}

	vm->heap.words[ofs >> 2] = val;
}

static inline void dwrite2(struct vm *vm, vmword_t ofs, uint16_t val)
{
	trace("%s:write %d (%#x) : %d\n", vm->vm_filename, ofs, ofs, val);

	if (check_data_bounds(vm, ofs) || check_data_bounds(vm, ofs + 1))
		return;

	if (ofs & 1) {
		vm_error_set(vm, VM_ERROR_UNALIGNED);
		return;
	}

	vm->heap.halfs[ofs >> 1] = val;
}

static inline void dwrite1(struct vm *vm, vmword_t ofs, uint8_t val)
{
	if (check_data_bounds(vm, ofs))
		return;
	vm->heap.bytes[ofs] = val;
}

static inline vmword_t dread4(struct vm *vm, vmword_t ofs)
{
	// TODO: use one function to check range
	if (check_data_bounds(vm, ofs) || check_data_bounds(vm, ofs + 3)) {
		vm_error_set(vm, VM_ERROR_OUT_OF_BOUNDS);
		return 0xdeadbeef;
	}

	if (ofs & 3) {
		vm_error_set(vm, VM_ERROR_UNALIGNED);
		return 0xdeadbeef;
	}

	vmword_t val = vm->heap.words[ofs >> 2];
//	trace("%s:read %d (%#x) : %d\n", vm->vm_filename, ofs, ofs, val);
	return val;
}

static inline uint16_t dread2(struct vm *vm, vmword_t ofs)
{
	// TODO: use one function to check range
	if (check_data_bounds(vm, ofs) || check_data_bounds(vm, ofs + 1)) {
		vm_error_set(vm, VM_ERROR_OUT_OF_BOUNDS);
		return 0xdead;
	}

	if (ofs & 1) {
		vm_error_set(vm, VM_ERROR_UNALIGNED);
		return 0xbeef;
	}

	return vm->heap.halfs[ofs >> 1];
}

static inline uint8_t *dmemptr(struct vm *vm, vmword_t ofs, size_t len)
{
	if (check_data_bounds(vm, ofs) ||
		(len > 0 && check_data_bounds(vm, ofs + len - 1))) {
		vm_error_set(vm, VM_ERROR_OUT_OF_BOUNDS);
		error("%s:ofs=%#x len=%d\n", vm->vm_filename, ofs, (int)len);
		return NULL;
	}
	return &vm->heap.bytes[ofs];
}

static inline uint8_t dread1(struct vm *vm, vmword_t ofs)
{
	if (check_data_bounds(vm, ofs)) {
		vm_error_set(vm, VM_ERROR_OUT_OF_BOUNDS);
		return 0xde;
	}

	return vm->heap.bytes[ofs];
}

#if 0
/* write value to program stack */
static void ppoke(struct vm *vm, int index, vmword_t val)
{
	// unsigned ofs = vm->psp - index - 4; // TODO: is this correct?
	unsigned ofs = vm->psp - index; // TODO: is this correct?

	if (check_data_bounds(vm, ofs))
		return;

	trace("%s:write %d (%#x) : %d\n", vm->vm_filename, ofs, ofs, val);
	dwrite4(vm, ofs, val);
}
#endif

void vm_disassemble(const struct vm *vm)
{
	disassemble(stdout, vm->code, vm->code_len, 0);
}

/* decode opcode + optional immediate at vm->pc, advancing vm->pc past them.
 * returns 1 on success, 0 on end-of-code, -1 on illegal/truncated opcode. */
static int fetch_op(struct vm *vm, uint8_t *out_op, vmword_t *out_param)
{
	if (vm->pc >= vm->code_len)
		return 0;

	uint8_t op = vm->code[vm->pc];
	unsigned len = opcode_length(op);

	if (len == 0 || len > vm->code_len - vm->pc)
		return -1;

	vmword_t param = 0;

	if (len == 2)
		param = read_imm1(&vm->code[vm->pc + 1]);
	else if (len == 5)
		param = read_imm4(&vm->code[vm->pc + 1]);

	vm->pc += len;
	*out_op = op;
	*out_param = param;
	return 1;
}

#if 0
static void vm_stacktrace(const struct vm *vm)
{
	abort(); // TODO: implement this
}
#endif

/* return 1 if finished (re-entrant), 0 if not finished, and -1 on error. */
int vm_run_slice(struct vm *vm)
{
	vmword_t a; /* scratch area */
	vmword_t b; /* scratch area */
	vmsingle_t af; /* scratch area */
	vmsingle_t bf; /* scratch area */
	int e;

	debug("code_len=0x%08zx\n", vm->code_len);
	debug("heap_mask=0x%08zx heap_len=0x%08zx\n",
	      vm->heap_mask, vm->heap_len);
	assert(vm->heap_mask == make_mask(vm->heap_len));

	while (!vm->status && !_check_code_bounds(__func__, __LINE__, vm, vm->pc)) {
		if (vm->pc >= vm->code_len) {
			vm_error_set(vm, VM_ERROR_OUT_OF_BOUNDS);
			break;
		}

		vmword_t op_pc = vm->pc;
		uint8_t op_byte;
		vmword_t param;
		int f = fetch_op(vm, &op_byte, &param);

		if (f == 0) {
			vm_error_set(vm, VM_ERROR_OUT_OF_BOUNDS);
			break;
		}
		if (f < 0) {
			vm_error_set(vm, VM_ERROR_INVALID_OPCODE);
			break;
		}

#ifdef DEBUG_ENABLED
		{ /* debug only */
			vmword_t top = ~0;

			if (vm->op_stack)
				top = vm->stack[vm->op_stack - 1];

			debug("PC:pc=%d (%#x) op=%s top=%d (%#x) psp=%d (%#x)\n",
			      op_pc, op_pc,
			      disassemble_opcode(vm->code, op_pc, vm->code_len),
			      top, top, vm->psp, vm->psp);
		}
#endif

		switch (op_byte) {
			;
		case 0x00: /* UNDEF*/
			break;
		case 0x01: /* IGNORE */
			break;
		case 0x02: /* BREAK */
			vm_error_set(vm, VM_ERROR_ABORT);
			e = -1;
			goto out;
		case 0x03: /* ENTER - increase program stack by amount */
			vm->psp -= param;
			break;
		case 0x04: /* LEAVE - shrink program stack by amount */
			if (vm_leave(vm, param)) {
				e = 1; /* finished - results on stack */
				goto out;
			}
			break;
		case 0x05: /* CALL */
			dwrite4(vm, vm->psp + 4, vm->psp); /* save the old SP */
			dwrite4(vm, vm->psp, vm->pc); /* save the old PC */
			a = opop(vm);

			if ((int32_t)a < 0) {
				vmword_t old_pc = vm->pc;
				// TODO: the original would store as byte offset, not instruction index
				// dwrite4(vm, vm->psp + 4, -1 - vm->pc); /* save the old PC */
				// TODO: do system call if program counter is negative
				vm->pc = 0xdeadbeef; /* system call better clean this up */
				if (vm->env) {
					vm->yield = 0;
					if (vm_env_call(vm->env, a, vm))
						vm_error_set(vm, VM_ERROR_BAD_SYSCALL);
					if (vm->yield) {
						e = 0; /* not finished - yielding */
						goto out;
					}
				} else {
					// TODO: catch this as an error
					error("%s:environment not set during system call (pc=%#x call=%d)\n",
						vm->vm_filename, old_pc, (int)a);
					vm_error_set(vm, VM_ERROR_BAD_ENVIRONMENT);
				}
				info("**** %s:restoring PC(%#x) to %#x\n",
					vm->vm_filename, vm->pc, old_pc);
				vm->pc = old_pc;
			} else {
				vm->pc = pc_from_addr(vm, a);
			}

			break;
		case 0x06: /* PUSH - push a 0 onto data stack */
			opush(vm, 0);
			break;
		case 0x07: /* POP - remove an item from data stack */
			opop(vm);
			break;
		case 0x08: /* CONST x */
			opush(vm, param);
			break;
		case 0x09: /* LOCAL x - get address of local */
			a = vm->psp + param;
			opush(vm, a);
			break;
		case 0x0a: /* JUMP */
			vm->pc = pc_from_addr(vm, opop(vm));
			break;
		case 0x0b: /* EQ x */
			a = opop(vm);
			b = opop(vm);

			if (b == a)
				vm->pc = pc_from_addr(vm, param);

			break;
		case 0x0c: /* NE x */
			a = opop(vm);
			b = opop(vm);

			if (b != a)
				vm->pc = pc_from_addr(vm, param);

			break;
		case 0x0d: /* LTI x */
			a = opop(vm);
			b = opop(vm);

			if ((int)b < (int)a)
				vm->pc = pc_from_addr(vm, param);

			break;
		case 0x0e: /* LEI x */
			a = opop(vm);
			b = opop(vm);

			if ((int)b <= (int)a)
				vm->pc = pc_from_addr(vm, param);

			break;
		case 0x0f: /* GTI x */
			a = opop(vm);
			b = opop(vm);

			if ((int)b > (int)a)
				vm->pc = pc_from_addr(vm, param);

			break;
		case 0x10: /* GEI x */
			a = opop(vm);
			b = opop(vm);

			if ((int)b >= (int)a)
				vm->pc = pc_from_addr(vm, param);

			break;
		case 0x11: /* LTU x */
			a = opop(vm);
			b = opop(vm);

			if (b < a)
				vm->pc = pc_from_addr(vm, param);

			break;
		case 0x12: /* LEU x */
			a = opop(vm);
			b = opop(vm);

			if (b <= a)
				vm->pc = pc_from_addr(vm, param);

			break;
		case 0x13: /* GTU x */
			a = opop(vm);
			b = opop(vm);

			if (b > a)
				vm->pc = pc_from_addr(vm, param);

			break;
		case 0x14: /* GEU x */
			a = opop(vm);
			b = opop(vm);

			if (b >= a)
				vm->pc = pc_from_addr(vm, param);

			break;
		case 0x15: /* EQF x */
			af = opopf(vm);
			bf = opopf(vm);

			if (bf == af)
				vm->pc = pc_from_addr(vm, param);

			break;
		case 0x16: /* NEF x */
			af = opopf(vm);
			bf = opopf(vm);

			if (bf != af)
				vm->pc = pc_from_addr(vm, param);

			break;
		case 0x17: /* LTF x */
			af = opopf(vm);
			bf = opopf(vm);

			if (bf < af)
				vm->pc = pc_from_addr(vm, param);

			break;
		case 0x18: /* LEF x */
			af = opopf(vm);
			bf = opopf(vm);

			if (bf <= af)
				vm->pc = pc_from_addr(vm, param);

			break;
		case 0x19: /* GTF x */
			af = opopf(vm);
			bf = opopf(vm);

			if (bf > af)
				vm->pc = pc_from_addr(vm, param);

			break;
		case 0x1a: /* GEF x */
			af = opopf(vm);
			bf = opopf(vm);

			if (bf >= af)
				vm->pc = pc_from_addr(vm, param);

			break;
		case 0x1b: /* LOAD1 */
			a = opop(vm);
			b = dread1(vm, a);
			opush(vm, b);
			break;
		case 0x1c: /* LOAD2 */
			a = opop(vm);
			b = dread2(vm, a);
			opush(vm, b);
			break;
		case 0x1d: /* LOAD4 */
			a = opop(vm);
			b = dread4(vm, a);
			trace("%s:LOAD4 (@%d) : %d\n", vm->vm_filename, a, b);
			opush(vm, b);
			break;
		case 0x1e: /* STORE1 */
			a = opop(vm);
			b = opop(vm);
			dwrite1(vm, b, a);
			break;
		case 0x1f: /* STORE2 */
			a = opop(vm);
			b = opop(vm);
			dwrite2(vm, b, a);
			break;
		case 0x20: /* STORE4 */
			a = opop(vm);
			b = opop(vm);
			trace("%s:STORE4 %d (@%d) : %d\n", vm->vm_filename, a, a, b);
			dwrite4(vm, b, a);
			break;
		case 0x21: /* ARG x - write value to program stack */
			a = opop(vm);
			b = vm->psp + param;
			trace("%s:ARG %d (@%d) : %d\n", vm->vm_filename, param, b, a);
			dwrite4(vm, b, a);
			break;
		case 0x22: /* BLOCK_COPY x - copy x bytes */
			a = opop(vm); /* src */
			b = opop(vm); /* dest */
#if 0 // TODO: implement this
			block_copy(vm, b, a, param);
#endif
			vm_error_set(vm, VM_ERROR_INVALID_OPCODE);
			e = -1;
			goto out;
		case 0x23: /* SEX8 */
			a = (int32_t)(int8_t)opop(vm);
			opush(vm, a);
			break;
		case 0x24: /* SEX16 */
			a = (int32_t)(int16_t)opop(vm);
			opush(vm, a);
			break;
		case 0x25: /* NEGI */
			a = opop(vm);
			/* -INT_MIN overflows signed negation; use unsigned
			 * two's-complement which is well-defined. */
			opush(vm, (vmword_t)0 - a);
			break;
		case 0x26: /* ADD */
			a = opop(vm);
			b = opop(vm);
			opush(vm, b + a);
			break;
		case 0x27: /* SUB */
			a = opop(vm);
			b = opop(vm);
			opush(vm, b - a);
			break;
		case 0x28: /* DIVI */
			a = opop(vm);
			b = opop(vm);

			if (!a)
				vm_error_set(vm, VM_ERROR_MATH_ERROR);
			else if ((int)a == -1 && (int)b == INT_MIN)
				opush(vm, (vmword_t)INT_MIN); /* wrap per two's-complement */
			else
				opush(vm, (int)b / (int)a);

			break;
		case 0x29: /* DIVU */
			a = opop(vm);
			b = opop(vm);

			if (a)
				opush(vm, b / a);
			else
				vm_error_set(vm, VM_ERROR_MATH_ERROR);

			break;
		case 0x2a: /* MODI */
			a = opop(vm);
			b = opop(vm);

			if (!a)
				vm_error_set(vm, VM_ERROR_MATH_ERROR);
			else if ((int)a == -1 && (int)b == INT_MIN)
				opush(vm, 0);
			else
				opush(vm, (int)b % (int)a);

			break;
		case 0x2b: /* MODU */
			a = opop(vm);
			b = opop(vm);

			if (a)
				opush(vm, b % a);
			else
				vm_error_set(vm, VM_ERROR_MATH_ERROR);

			break;
		case 0x2c: /* MULI */
			a = opop(vm);
			b = opop(vm);
			/* unsigned multiply wraps cleanly; reinterpret. */
			opush(vm, a * b);
			break;
		case 0x2d: /* MULU */
			a = opop(vm);
			b = opop(vm);
			opush(vm, b * a);
			break;
		case 0x2e: /* BAND */
			a = opop(vm);
			b = opop(vm);
			opush(vm, b & a);
			break;
		case 0x2f: /* BOR */
			a = opop(vm);
			b = opop(vm);
			opush(vm, b | a);
			break;
		case 0x30: /* BXOR */
			a = opop(vm);
			b = opop(vm);
			opush(vm, b ^ a);
			break;
		case 0x31: /* BCOM */
			a = opop(vm);
			opush(vm, ~a);
			break;
		case 0x32: /* LSH */
			a = opop(vm);
			b = opop(vm);
			opush(vm, b << (a & 31));
			break;
		case 0x33: /* RSHI */
			a = opop(vm);
			b = opop(vm);
			opush(vm, (int)b >> (a & 31));
			break;
		case 0x34: /* RSHU */
			a = opop(vm);
			b = opop(vm);
			opush(vm, (unsigned)b >> (a & 31));
			break;
		case 0x35: /* NEGF */
			af = opopf(vm);
			opushf(vm, -af);
			break;
		case 0x36: /* ADDF */
			af = opopf(vm);
			bf = opopf(vm);
			opushf(vm, bf + af);
			break;
		case 0x37: /* SUBF */
			af = opopf(vm);
			bf = opopf(vm);
			opushf(vm, bf - af);
			break;
		case 0x38: /* DIVF */
			af = opopf(vm);
			bf = opopf(vm);
			opushf(vm, bf / af);
			break;
		case 0x39: /* MULF */
			af = opopf(vm);
			bf = opopf(vm);
			opushf(vm, bf * af);
			break;
		case 0x3a: /* CVIF */
			af = (vmsingle_t)opop(vm);
			opushf(vm, af);
			break;
		case 0x3b: /* CVFI */
			{
				vmsingle_t f = opopf(vm);
				int32_t iv;
				if (isnan(f))
					iv = 0;
				else if (f >= (vmsingle_t)INT32_MAX)
					iv = INT32_MAX;
				else if (f <= (vmsingle_t)INT32_MIN)
					iv = INT32_MIN;
				else
					iv = (int32_t)f;
				opush(vm, (vmword_t)iv);
			}
			break;
		default:
			vm_error_set(vm, VM_ERROR_INVALID_OPCODE);
		}
	}

// finished: // TODO: LEAVE -1 could jump here instead of using flags
	if (vm->status)
		error("%s:error 0x%x (pc=0x%x)\n", vm->vm_filename, vm->status, vm->pc);
	else
		info("%s:not finished!\n", vm->vm_filename);
	e = vm->status ? -1 : 0;
out:
	trace("%s:run slice e=%d status=%#x\n", vm->vm_filename, e, vm->status);
	/* dump some of the stack on error */
	if (e < 0) {
		error("%s:pstack trace:\n", vm->vm_filename);
		debug("pc=%d (%#x) psp=%d (%#x) bottom=%#x op_stk=%d\n",
		      vm->pc, vm->pc, vm->psp, vm->psp, vm->stack_bottom, vm->op_stack);
		if (vm->pc >= vm->stack_bottom) {
			warn("PC is in stack region!\n");
		}
		int i;
		for (i = -16; i < 24; i += 4) {
			vmword_t a = dread4(vm, vm->psp + i);
			fprintf(stderr, "psp%+-4d: %d (%#x)\n",
				i, (int)a, (unsigned)a);
		}
	}
	return e;
}

static inline void arg_write(struct vm *vm, int i, vmword_t val)
{
	dwrite4(vm, vm->psp + 8 + (i * 4), val);
}

static int prepare_call(struct vm *vm, vmword_t entry, unsigned nr_args)
{
	assert(vm != NULL);
	if (nr_args > MAX_VMMAIN_ARGS) {
		error("%s:vm_call nr_args=%u exceeds MAX_VMMAIN_ARGS=%u\n",
		      vm->vm_filename, nr_args, MAX_VMMAIN_ARGS);
		vm_error_set(vm, VM_ERROR_BAD_ENVIRONMENT);
		return -1;
	}
	// TODO: turn this into a syscall if entry address is negative
	vm->pc = pc_from_addr(vm, entry);
	/* make space for args and return */
	vmword_t old_psp = vm->psp;
	vm->psp -= 8 + (4 * nr_args);
	if (check_stack_bounds(vm))
		return -1;
	/* store return address and old stack. -1 signals "finished" to
	 * vm_leave; old_psp is restored there so the host's psp survives
	 * the re-entrant call. */
	dwrite4(vm, vm->psp, -1);
	dwrite4(vm, vm->psp + 4, old_psp);
	return 0;
}

void vm_call(struct vm *vm, vmword_t entry, unsigned nr_args, ...)
{
	va_list ap;
	unsigned i;

	if (prepare_call(vm, entry, nr_args))
		return;
	va_start(ap, nr_args);
	/* store args */
	for (i = 0; i < nr_args; i++) {
		vmword_t val = va_arg(ap, vmword_t);
		arg_write(vm, i, val);
	}
	va_end(ap);
	// TODO: optionally vm_run() until complete and return result
}

void vm_call_array(struct vm *vm, vmword_t entry, unsigned nr_args, const vmword_t args[])
{
	unsigned i;

	assert(vm != NULL);
	assert(args != NULL);
	if (prepare_call(vm, entry, nr_args))
		return;
	/* store args */
	for (i = 0; i < nr_args; i++)
		arg_write(vm, i, args[i]);
	// TODO: optionally vm_run() until complete and return result
}

static inline unsigned roundup_pow2(unsigned n)
{
	n--;
	n |= n >> 1;
	n |= n >> 2;
	n |= n >> 4;
	n |= n >> 8;
	n |= n >> 16;
	n++;
	return n;
}

struct vm_header {
#define VM_MAGIC 0x12721444
#define VM_MAGIC_VER2   0x12721445
	uint32_t magic;
	int32_t instruction_count;
	uint32_t code_offset;
	int32_t code_length;
	uint32_t data_offset;
	int32_t data_length;
	int32_t lit_length;
	int32_t bss_length;
	int32_t jtrg_length; /* jump table target */
};

static int load_data_segment(struct vm *vm, FILE *f, const char *filename, const struct vm_header *header)
{
	uint32_t heap_len = header->data_length + header->lit_length + header->bss_length;
	const unsigned data_length = header->data_length + header->lit_length;
	const unsigned data_offset = header->data_offset;
	heap_len = roundup_pow2(heap_len);

	if (data_length > heap_len) {
		error("%s:data segment (%u) larger than heap (%u)\n",
		      filename, data_length, heap_len);
		return -1;
	}

	vm->heap_len = heap_len;
	vm->heap_mask = heap_len ? heap_len - 1 : 0;
	vm->heap.bytes = malloc(vm->heap_len);

	if (!vm->heap.bytes) {
		error("out of memory allocating heap (%zu bytes)\n", vm->heap_len);
		return -1;
	}

	if (fseek(f, data_offset, SEEK_SET))
		goto failure_perror;

	if (fread(vm->heap.bytes, 1, data_length, f) != (size_t)data_length)
		goto failure_perror; // TODO: check errno and print short read msg

	memset(vm->heap.bytes + data_length, 0x00,
	       vm->heap_len - data_length);
	return 0;
failure_perror:
	perror(filename);
	return -1;
}

void vm_free(struct vm *vm)
{
	if (!vm)
		return;

	free(vm->vm_filename);
	vm->vm_filename = NULL;
	free(vm->heap.bytes);
	vm->heap.bytes = NULL;
	vm->heap_len = vm->heap_mask = 0;
	free(vm->code);
	vm->code = NULL;
	vm->code_len = 0;
	free(vm->instr_to_byte);
	vm->instr_to_byte = NULL;
	vm->nr_instructions = 0;
	free(vm);
}

struct vm *vm_new(const struct vm_env *env)
{
	struct vm *vm = calloc(1, sizeof(*vm));
	vm->env = env;
	return vm;
}

/* return 1 on success, 0 on failure */
int vm_load(struct vm *vm, const char *filename)
{
	struct vm_header header;
	FILE *f;
	size_t header_len;
	unsigned header_version;

	if (!vm)
		return 0;

	/* erase everything except the environment. */
	const struct vm_env *env = vm->env;
	memset(vm, 0, sizeof(*vm));
	vm->env = env;

	f = fopen(filename, "rb");
	if (!f) {
		perror(filename);
		return 0;
	}

	vm->vm_filename = strdup(filename);

	header_len = fread(&header, 1, sizeof(header), f);

	if (header_len >= 36 && header.magic == VM_MAGIC_VER2) {
		header_version = 2;
	} else if (header_len >= 32 && header.magic == VM_MAGIC) {
		header_version = 1;
	} else {
		error("%s:not a valid VM file (magic=0x%08" PRIx32 " len=%zd)\n",
		      filename, header.magic, header_len);
		goto failure;
	}

	info("code_length=%d data_length=%d lit_length=%d bss_length=%d\n",
	     header.code_length, header.data_length, header.lit_length,
	     header.bss_length);

	/* validate */

	/* checks that none of the sizes are negative
	 * checks that bss_length has room for PROGRAM_STACK_SIZE.
	 */
	if (header.code_length < 0 || header.data_length < 0 || header.lit_length < 0
	                || header.bss_length < PROGRAM_STACK_SIZE
	                || (header_version >= 2 && header.jtrg_length < 0)) {
		goto failure;
	}

	/* TODO: validate these:
	instruction_count;
	code_offset;
	data_offset;
	*/


	/* load data segment */
	int e;
	e = load_data_segment(vm, f, filename, &header);

	if (e)
		goto failure_freevm;

	/* load code segment: keep the raw byte stream; pc is a byte offset. */
	size_t codebuf_len = header.code_length;
	unsigned char *codebuf = malloc(codebuf_len);

	if (!codebuf) {
		error("out of memory allocating code buffer (%zd bytes)\n",
		      codebuf_len);
		goto failure_freevm;
	}

	if (fseek(f, header.code_offset, SEEK_SET))
		goto failure_perror;

	if (fread(codebuf, 1, codebuf_len, f) != codebuf_len)
		goto failure_perror; // TODO: check errno and print short msg

	/* validate opcode stream end-to-end and build instruction-index table.
	 * Q3VM encodes call/branch targets as ordinals, so we need the map
	 * to translate them to byte offsets at dispatch time. */
	trace("codebuf=%p codebuf_len=%zd\n", codebuf, codebuf_len);
	uint32_t *instr_to_byte = NULL;
	size_t nr_instructions = 0;
	{
		/* worst case one instruction per byte */
		instr_to_byte = malloc(sizeof(*instr_to_byte) * (codebuf_len + 1));
		if (!instr_to_byte) {
			error("out of memory allocating instruction table\n");
			goto failure_freecodebuf;
		}
		size_t n = 0;
		while (n < codebuf_len) {
			unsigned oplen = opcode_length(codebuf[n]);

			if (oplen == 0) {
				error("invalid opcode 0x%02x at offset %zd!\n",
				      codebuf[n], n);
				free(instr_to_byte);
				goto failure_freecodebuf;
			}

			if (oplen > codebuf_len - n) {
				error("truncated opcode sequence at offset %zd!\n", n);
				free(instr_to_byte);
				goto failure_freecodebuf;
			}

			instr_to_byte[nr_instructions++] = (uint32_t)n;
			n += oplen;
		}
	}

	vm->code = codebuf;
	vm->code_len = codebuf_len;
	vm->instr_to_byte = instr_to_byte;
	vm->nr_instructions = nr_instructions;
	debug("%zu instructions in %zd code bytes\n",
	      nr_instructions, codebuf_len);
	debug("Loaded %zd code bytes\n", codebuf_len);

	fclose(f);

	/* initialize fields */
	vm->pc = 0;
	vm->psp = (vm->heap_mask + 1) - 4; /* points to the last word */
	vm->stack_bottom = vm->psp - PROGRAM_STACK_SIZE;
	vm->status = 0;

	return 1;
failure_perror:
	perror(filename);
failure_freecodebuf:
	free(codebuf);
failure_freevm:
	free(vm->heap.bytes);
	vm->heap.bytes = NULL;
	free(vm->code);
	vm->code = NULL;
	free(vm->instr_to_byte);
	vm->instr_to_byte = NULL;
failure:
	fclose(f);
	error("%s:could not load file\n", filename);
	return 0;
}

int vm_status(const struct vm *vm)
{
	return vm ? vm->status : VM_ERROR_NOT_INITIALIZED;
}

const char *vm_filename(const struct vm *vm)
{
	return vm ? vm->vm_filename : NULL;
}

vmword_t vm_pop(struct vm *vm)
{
	return opop(vm);
}

vmsingle_t vm_popf(struct vm *vm)
{
	return opopf(vm);
}

void vm_push(struct vm *vm, vmword_t n)
{
	opush(vm, n);
}

void vm_pushf(struct vm *vm, vmsingle_t f)
{
	opushf(vm, f);
}

/* return arg on the current call frame */
vmword_t vm_arg(struct vm *vm, int num)
{
	// TODO: num += 0 / 4; // use local_size to adjust
	vmword_t arg = dread4(vm, vm->psp + 8 + (num * 4));
	trace("%s:arg[%d]=%#x\n", vm->vm_filename, num, arg);
	return arg;
}

/* get address of a C style string */
char *vm_string(struct vm *vm, vmword_t addr, size_t *len)
{
	trace("%s:addr=%#x\n", vm->vm_filename, addr);
	uint8_t *s = dmemptr(vm, addr, 0);
	if (!s) {
		error("%s:cannot access string:addr=%#x status=%#x\n", vm->vm_filename, addr, vm->status);
		assert(vm->status != 0);
		return NULL;
	}
	assert(addr < vm->heap_len);
	uint8_t *e = memchr(s, 0, vm->heap_len - addr);
	if (!e) {
		// TODO: print some useful diagnostic message. pc=%#x syscall=%d
		error("%s:string not null terminated:addr=%#x\n", vm->vm_filename, addr);
		vm_error_set(vm, VM_ERROR_OUT_OF_BOUNDS);
		return NULL;
	}
	if (len)
		*len = e - s; /* length does not include the null termination */
	info("%s:success:len=%d s=%s\n", vm->vm_filename, (int)(e - s), s);
	return (char*)s;
}

/* terminates the current VM */
void vm_abort(struct vm *vm)
{
	vm_error_set(vm, VM_ERROR_ABORT);
	info("%s:ABORTED!\n", vm->vm_filename);
	// TODO: print pc=%#x and syscall=%d
}

void *vm_get_extra(struct vm *vm)
{
	return vm->extra;
}

void *vm_set_extra(struct vm *vm, void *p)
{
	void *old = vm->extra;
	vm->extra = p;
	return old;
}

void vm_yield(struct vm *vm)
{
	vm->yield = 1;
}
