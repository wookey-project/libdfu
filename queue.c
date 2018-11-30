#include "api/malloc.h"
#include "queue.h"
#define assert(val) if (!(val)) { while (1) ; };

static volatile int queue_mutex = 0;

struct queue *queue_create(uint32_t capacity)
{
	struct queue *q = 0;
    int ret = 0;
    // FIXME return value to check
    ret = wmalloc((void**)&q, sizeof(struct queue), ALLOC_NORMAL);
    if (ret != 0) {
      //printf("malloc failed with %x\n", ret);
      while(1){};
    }
    printf("queue address is %x\n", q);
	if (q) {
		q->head = NULL;
		q->tail = NULL;
	}
	q->max = capacity;
	q->size = 0;
	return q;
}

int queue_enqueue(struct queue *q, void *data)
{
	assert(q);
	assert(!q->max || (q->size <= q->max));
        int ret;
	if (q->max && q->size == q->max){
		return -1;
	}

	struct node *n;
    // FIXME return value to check
    ret = wmalloc((void**)&n, sizeof(struct node), ALLOC_NORMAL);
    if (ret != 0) {
      //printf("malloc failed with %x\n", ret);
      while(1){};
    }

	if (!n){
//		queue_mutex = 0;
		return -1;
	}

	n->next = q->head;
	n->prev = NULL;
	n->data = data;
	if (q->head){
		q->head->prev = n;
	}
	q->head = n;
	if (!q->tail){
		q->tail = q->head;
	}

	q->size++;

	return 0;
}

void *queue_next_element(struct queue *q)
{
	assert(q);
	assert(q->tail);
	assert(!q->max || (q->size <= q->max));

	return q->tail->data;
}

int print_heap(void);
void *queue_dequeue(struct queue *q)
{
	assert(q);
	assert(q->tail);
	assert(!q->max || (q->size <= q->max));
	int ret;
	struct node *last = q->tail;
	void *data = last->data;
	if(last->prev != NULL){
		last->prev->next = NULL;
	}

	q->tail = last->prev;
	if (last == q->head){
		q->head = NULL;
	}

	ret = wfree((void**)&last);
    if (ret != 0) {
      printf("free failed with %x\n", ret);
     print_heap();
      while(1){};
    }

	q->size--;

	return data;
}

int queue_is_empty(struct queue *q)
{
	int ret;
	assert(q);
	assert(!q->max || (q->size <= q->max));
	ret = !q->head;

	return ret;
}

uint32_t queue_available_space(struct queue *q)
{
	uint32_t ret;
	while(queue_mutex == 1){
		continue;
	}
	queue_mutex = 1;

	assert(q);
	assert(!q->max || (q->size <= q->max));
	if (!q->max){
		ret = (uint32_t)-1;
	}
	else{
		ret = q->max - q->size;
	}

	queue_mutex = 0;
	return ret;
}
