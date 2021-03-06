/* task.c - task and channel scheduling */
/* PUBLIC DOMAIN - June 15, 2020 - Jon Mayo */
/* TODO:
 * - make it clear which channel a task is waiting in.
 * - STAILQ vs TAILQ - doesn't seem we strictly need TAILQ_REMOVE() and STAILQ_REMOVE_HEAD() is good enough
 */
#include "task.h"
#include <stdlib.h>
#include <string.h>
#include <sys/queue.h>

#if 1
#include <stdio.h>
#define TRACEF(fmt, ...) fprintf(stderr, ">>> %s():" fmt "\n", __func__, ## __VA_ARGS__)
#else
#define TRACEF(fmt, ...) /* ignored */
#endif

struct task {
	TAILQ_ENTRY(task) tailq;
	void *context;
	void (*run)(void *context);
	void (*free)(void *context);
	char id[16];
	struct task_channel *chan;
};

struct task_channel {
	char id[16];
	TAILQ_HEAD(task_head, task) task_head;
};

struct task *
task_new(const char *id, void *extra, void (*run)(void*), void (*free)(void*))
{
	struct task *t = calloc(1, sizeof(*t));
	if (!t)
		return NULL;

	strncpy(t->id, id, sizeof(t->id));
	t->free = free;
	t->context = extra;
	t->run = run;
	t->chan = NULL;

	return t;
}

struct task_channel *
task_channel_new(const char *id)
{
	struct task_channel *ch = calloc(1, sizeof(*ch));
	if (!ch)
		return NULL;

	strncpy(ch->id, id, sizeof(ch->id));
	TAILQ_INIT(&ch->task_head);

	return ch;
}

void *
task_extra(struct task *task)
{
	return task ? task->context : NULL;
}

int
task_empty(struct task *task)
{
	return task ? TAILQ_NEXT(task, tailq) != NULL : 0;
}

void
task_free(struct task *task)
{
	if (!task)
		return;

	/* remove if still on a channel */
	if (task->chan)
		TAILQ_REMOVE(&task->chan->task_head, task, tailq);

	/* double-check that item is completely unlinked */
	if (TAILQ_NEXT(task, tailq))
		return; // ERROR! cannot free if still on a list

	/* run the free handler, if present */
	if (task->free)
		task->free(task);

	free(task);
}

int
task_schedule(struct task *task, struct task_channel *chan)
{
	TRACEF("task=%.*s chan=%.*s", sizeof(task->id), task ? task->id : "(None)", sizeof(chan->id), chan ? chan->id : "(None)");
	if (!chan || !task)
		return -1; // EINVAL
	if (TAILQ_NEXT(task, tailq)) {
		// TODO: TAILQ_REMOVE(task->chan->task_head, task, tailq);
		TRACEF("ERROR:%s():task=%.*s oldchan=%.*s:task already scheduled!", __func__, sizeof(task->id), task->id, sizeof(task->chan->id), task->chan->id);
		return -1; // Error: already in a channel
	}

	TAILQ_INSERT_TAIL(&chan->task_head, task, tailq);
	task->chan = chan;

	return 0;
}

int
task_remove_channel(struct task *task)
{
	if (!task)
		return -1; /* EINVAL */

	struct task_channel *chan = task->chan;
	if (!chan)
		return 0; /* ignored */

	TAILQ_REMOVE(&chan->task_head, task, tailq);
	task->tailq.tqe_next = NULL;
	task->tailq.tqe_prev = NULL;

	task->chan = NULL; /* leaving the channel */

	return 0;
}

struct task *
task_channel_next(struct task_channel *chan)
{
	struct task *task = TAILQ_FIRST(&chan->task_head);

	if (!task)
		return NULL;

	task_remove_channel(task);

	return task;
}
