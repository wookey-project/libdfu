#ifndef QUEUE_H
# define QUEUE_H
#include "api/stdio.h"
#include "api/nostd.h"
#include "api/malloc.h"
#include "api/regutils.h"

struct node {
	struct node *next;
	struct node *prev;
	void *data;
};

struct queue {
	struct node *head;
	struct node *tail;
	uint32_t size;
	uint32_t max;
};

/**
 * queue_create - Create an empty queue
 * @capacity: Maximum number of elements in the queue. If @capacity is 0, the
 * capacity of the queue is unlimited.
 * Return: a pointer to the new queue
 */
struct queue *queue_create(uint32_t capacity);

/**
 * queue_enqueue - Add an element in the queue
 * @q: The queue to work on.
 * @data: payload to add in the queue
 * Return: 0 if success, -1 if the queue is full if OOM
 */
int queue_enqueue(struct queue *q, void *data);

/**
 * queue_next_element - Get the next element of the queue
 * @q: The queue to work on.
 *
 * This function returns the next element of the queue that will be removed
 * from the queue but it *does not remove* this element from the queue. See
 * @queue_dequeue which return the next element and remove it from the queue.
 *
 * Return: A pointer to the payload of the next element out of the queue (the
 * caller should not free it).
 */
void *queue_next_element(struct queue *q);

/**
 * queue_dequeue - Dequeue the next element
 * @q: The queue to work on.
 *
 * This function remove the next element from the queue and returns it.
 *
 * Return: The next element which is removed from the queue (the caller can
 * free it).
 */
void *queue_dequeue(struct queue *q);

/**
 * queue_is_empty - Return the status of the queue
 * @q: The queue to work on.
 * Return: True if the queue is empty, false otherwise
 */
int queue_is_empty(struct queue *q);

/**
 * queue_available_space - Get the remaining slots count
 * @q: The queue to work on.
 * Return: The number of elements is it possible to enqueue.
 */
uint32_t queue_available_space(struct queue *q);

# if DUMP_STATS
void queue_dump_stats(struct queue *q);
# endif

#endif /* QUEUE_H */
