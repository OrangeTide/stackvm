# requires GNU Make to build

CFLAGS += -Wall -W -g
# CFLAGS += -O3
# LDFLAGS += -Wl,-Map=stackvm.map
# LDFLAGS += -rdynamic
CPPFLAGS += -D_XOPEN_SOURCE=700 -D_POSIX_C_SOURCE=200809L -D_GNU_SOURCE -I../

all ::
clean ::
clean-all :: clean
tests ::

## Kernel
S.kernel := kernel.c task.c prioq.c
O.kernel := $(S.kernel:%.c=%.o)
kernel : $(O.kernel) ../libstackvm.a
all :: kernel
clean :: ; $(RM) kernel $(O.kernel)
tests :: test-kernel
test-kernel : | kernel hello.qvm test2.qvm
	./kernel hello.qvm test2.qvm

## Programs
all :: hello.qvm
clean :: ; $(RM) hello.qvm hello.asm
hello.qvm : hello.asm

## Programs
all :: test2.qvm
clean :: ; $(RM) test2.qvm test2.asm
test2.qvm : test2.asm

# TOOLSDIR := ../../stackvm-tools/
Q3ASM := $(TOOLSDIR)q3asm
Q3LCC := $(TOOLSDIR)q3lcc

%.qvm : %.asm
	$(Q3ASM) -o $@ $^ syscalls.asm

%.asm : %.c
	$(Q3LCC) $^

.PRECIOUS: %.asm
