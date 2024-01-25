/* KALINA BIAŁEK, 340152
 * ---------------------------
 * Some of the code is basen on mm-implicit.c and CSAPP chapter 9.9.
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>
#include <stdint.h>
#include <stddef.h>
#include <unistd.h>

#include "mm.h"
#include "memlib.h"

/* If you want debugging output, use the following macro.  When you hand
 * in, remove the #define DEBUG line. */
#define DEBUG
#ifdef DEBUG
#define debug(...) printf(__VA_ARGS__)
#else
#define debug(...)
#endif

/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

/* --=[ block and other ]=-------------------------------------------- */

/* ciekawostka: arytmetyka na wskaźnikach różnych typów, to ciągłe bawienie się
 * w rzutowanie typów wskaźników :) */

typedef struct {

  /* 31--Current Block Size--3--0--0--a,
   * where a can be 1-allocated or 0-free */
  int32_t header;

  /* 31--Prev Block Size--3--0--0--b,
   * where b can be 1-allocated or 0-free */
  int32_t footer;

  /*
   * We don't know what the size of the payload will be, so we will
   * declare it as a zero-length array. This allow us to obtain a
   * pointer to the start of the payload.
   */
  uint8_t payload[];
} block_t;

static void *heap_start;   /* Address of the first block */
static void *heap_end;     /* Address past last byte of last block */
/* static word_t *last; */ /* Points at last block */

typedef enum {
  FREE = 0,     /* Block is free */
  USED = 1,     /* Block is used */
  PREVFREE = 2, /* Previous block is free (optimized boundary tags) */
} bt_flags;

#define EXTEND_SIZE (1 << 9)
#define test false

/* --=[ basic procedures ]=-------------------------------------------- */

static size_t round_up(size_t size) {
  return (size + ALIGNMENT - 1) & -ALIGNMENT;
}

static bool is_allocated(block_t *block) {
  return block->header & USED;
}

static bool is_prev_allocated(block_t *block) {
  return block->footer & USED;
}

static size_t get_size(block_t *block) {
  return block->header & -2;
}

static size_t get_prev_size(block_t *block) {
  return block->footer & -2;
}

static void set_header(block_t *block, size_t size, bool is_allocated) {
  block->header = size | is_allocated;
}

static void set_footer(block_t *block, size_t size, bool is_allocated) {
  block->footer = size | is_allocated;
}

static void *morecore(size_t size) {
  void *ptr = mem_sbrk(size);
  if (ptr == (void *)-1)
    return NULL;
  return ptr;
}

/* --=[ init ]=-------------------------------------------- */
/*
 * mm_init - Called when a new trace starts.
 */
int mm_init(void) {
  /* Pad heap start so first payload is at ALIGNMENT. */
  void *ptr = morecore(ALIGNMENT - offsetof(block_t, payload));
  if (!ptr)
    return -1;

  /* we need to know, where does the heap start */
  heap_start = ptr + ALIGNMENT - offsetof(block_t, payload);
  heap_end = heap_start;

  return 0;
}

/* --=[ malloc ]=-------------------------------------------- */
/*
 * malloc - Find first good fit and allocate block there. Extend the heap if
 * necessary. Always allocate a block whose size is a multiple of the alignment.
 */

static block_t *find_fit(size_t rqsize) {
  if (test)
    printf("find_fit\n");
  void *ptr = heap_start;
  void *prev = ptr;
  /* find first fit */
  /* not passed end   &&  (allocated already  ||   too small) */
  while ((ptr < heap_end) &&
         ((is_allocated(ptr)) || (get_size(ptr) < rqsize))) {
    prev = ptr;
    ptr = ptr + get_size(ptr);
  }

  if (test)
    printf("ptr after loop: %p\n", ptr);
  if (test)
    printf("header of ptr: %ld | %d\n", get_size(ptr), is_allocated(ptr));
  if (test)
    printf("heap_end | heap_size : %p | %ld\n", heap_end, mem_heapsize());
  if (test)
    printf("end of heap: %p\n", mem_heap_hi());

  /* if we didn't find any fit - allocate new memory and make free block_t */
  if (ptr == heap_end) {
    size_t ext = (rqsize <= EXTEND_SIZE) ? EXTEND_SIZE : rqsize;
    ptr = morecore(ext);
    if (!ptr)
      return (void *)-1;

    heap_end += ext;
    if (test)
      printf(
        "after allocating new heap memory - heap_end | heap_size : %p | %ld\n",
        heap_end, mem_heapsize());
    if (test)
      printf("end of heap: %p\n", mem_heap_hi());
    set_header(ptr, ext, FREE);

    if (ptr == heap_start)
      set_footer(ptr, 0, USED);
    else
      set_footer(ptr, get_size(prev), is_allocated(prev));
  }

  if (test)
    printf("end find_fit\n");

  return ptr;
}

/* -------------------------------------------- */

static void place(block_t *block, size_t size) {
  if (test)
    printf("place\n");
  size_t split_size = get_size(block) - size;

  /* remember next block */
  void *next = (void *)block + get_size(block);
  if (test)
    printf("next block: %p\n", next);
  /* default option: we can split */
  size_t next_size = split_size;
  bool is_allo = FREE;

  /* we can split, if split_size is >= minimal word size (== ALIGNMENT)*/
  if (split_size >= ALIGNMENT) {
    /* make new free block after allocated block right now */
    void *new_free = (void *)block + size;
    set_header(new_free, split_size, FREE);
    set_footer(new_free, size, USED);
    if (test)
      printf("new free block: %ld | %d\n", get_size(new_free),
             is_allocated(new_free));

    /* make allocated block */
    set_header(block, size, USED);
  }
  /* we do not split otherwise */
  else {
    set_header(block, get_size(block), USED);
    /* change update info for footer of next block */
    next_size = get_size(block);
    is_allo = USED;
  }

  /* update footer of next block */
  if (next != heap_end)
    set_footer(next, next_size, is_allo);

  if (test)
    printf("header of block: %ld | %d\n", get_size(block), is_allocated(block));

  if (next != heap_end)
    if (test)
      printf("footer of next block: %ld | %d\n", get_size(next),
             is_allocated(next));

  if (test)
    printf("end place\n");
}

/* -------------------------------------------- */

void *malloc(size_t size) {
  size = round_up(sizeof(block_t) + size);
  if (test)
    printf("malloc with size: %ld\n", size);

  block_t *block = find_fit(size);
  if ((long)block < 0)
    return NULL;

  place(block, size);

  if (test)
    printf("end of heap: %p\n", mem_heap_hi());
  if (test)
    printf("\n\n");
  return block->payload;
}

/* --=[ free ]=-------------------------------------------- */
/*
 * free - Maybe we shouldn't ignore it... Let's try to free some space.
 * We coalesce every time we free a block.
 */
void free(void *ptr) {
  if (test)
    printf("free with ptr: %p\n", ptr);

  if (!ptr)
    return;

  /* ptr is pointing to PAYLOAD so we just need to move it to the header of
   * block :D */
  ptr -= offsetof(block_t, payload);

  if (test)
    printf("ptr: %p\n", ptr);
  if (test)
    printf("header of block: %ld | %d\n", get_size(ptr), is_allocated(ptr));
  if (test)
    printf("footer of block: %ld | %d\n", get_prev_size(ptr),
           is_prev_allocated(ptr));
  if (test)
    printf("header of next block: %ld | %d\n", get_size(ptr + get_size(ptr)),
           is_allocated(ptr + get_size(ptr)));

  /* free current block before coalesce */
  set_header(ptr, get_size(ptr), FREE);

  /* if the next block is free  and not heap_end */
  if ((ptr + get_size(ptr) != heap_end) && !is_allocated(ptr + get_size(ptr)))
    set_header(ptr, get_size(ptr) + get_size(ptr + get_size(ptr)), FREE);

  if (test)
    printf("after next block check\n");
  if (test)
    printf("header of block: %ld | %d\n", get_size(ptr), is_allocated(ptr));

  /* if the previous block is free */
  if (!is_prev_allocated(ptr))
    set_header(ptr - get_prev_size(ptr), get_prev_size(ptr) + get_size(ptr),
               FREE);

  if (test)
    printf("after prev block check\n");
  if (test)
    printf("header of block: %ld | %d\n", get_size(ptr), is_allocated(ptr));

  /* change footer of next block */
  if (ptr + get_size(ptr) != heap_end)
    set_footer(ptr + get_size(ptr), get_size(ptr), FREE);

  if (test)
    printf("footer of next block: %ld | %d\n",
           get_prev_size(ptr + get_size(ptr)),
           is_prev_allocated(ptr + get_size(ptr)));

  if (test)
    printf("\n\n");
}

/* --=[ realloc ]=-------------------------------------------- */
/*
 * realloc - Change the size of the block by mallocing a new block,
 *      copying its data, and freeing the old block.
 **/
void *realloc(void *old_ptr, size_t size) {
  if (test)
    printf("realloc with ptr and size: %p | %ld\n",
           old_ptr - offsetof(block_t, payload), size);

  /* If size == 0 then this is just free, and we return NULL. */
  if (size == 0) {
    free(old_ptr);
    return NULL;
  }

  /* If old_ptr is NULL, then this is just malloc. */
  if (!old_ptr)
    return malloc(size);

  /* we got pointer to PAYLOAD! */
  void *ptr = old_ptr - offsetof(block_t, payload);

  /* we need to keep alignment happy */
  size_t rqsize = round_up(sizeof(block_t) + size);
  if (test)
    printf("size after round_up: %ld\n", rqsize);

  /* we do not shrink blocks! */
  if (rqsize <= get_size(ptr))
    return old_ptr;

  if (test)
    printf("current block: %ld | %d\n", get_size(ptr), is_allocated(ptr));
  if (test)
    printf("next block: %ld | %d\n", get_size(ptr + get_size(ptr)),
           is_allocated(ptr + get_size(ptr)));

  /* check if we can just extend existing block */
  /* if next block is not heap_end and is not allocated yet and there is enough
   * space */
  if ((ptr + get_size(ptr) != heap_end) && !is_allocated(ptr + get_size(ptr)) &&
      (get_size(ptr) + get_size(ptr + get_size(ptr)) > rqsize)) {
    if (test)
      printf("next block is free!\n");
    set_header(ptr, get_size(ptr) + get_size(ptr + get_size(ptr)), USED);
    place(ptr, rqsize);
    return old_ptr;
  }

  if (test)
    printf("we need to find new block...\n");
  /* we can't extend existing block - we need to find new block */
  void *new_ptr = malloc(size);

  /* If malloc() fails, the original block is left untouched. */
  if (!new_ptr)
    return NULL;

  /* Copy the old data. */
  block_t *block = old_ptr - offsetof(block_t, payload);
  size_t old_size = get_size(block);
  if (size < old_size)
    old_size = size;
  memcpy(new_ptr, old_ptr, old_size);

  /* Free the old block. */
  free(old_ptr);

  if (test)
    printf("\n\n");

  return new_ptr;
}

/* --=[ calloc ]=-------------------------------------------- */
/*
 * calloc - Allocate the block and set it to zero.
 * Leave it be - it's awesome :D
 */
void *calloc(size_t nmemb, size_t size) {
  if (test)
    printf("calloc with size: %ld\n", size);
  size_t bytes = nmemb * size;
  void *new_ptr = malloc(bytes);

  /* If malloc() fails, skip zeroing out the memory. */
  if (new_ptr)
    memset(new_ptr, 0, bytes);

  if (test)
    printf("\n\n");

  return new_ptr;
}

/* --=[ checkheap ]=-------------------------------------------- */
/*
 * mm_checkheap - So simple, it doesn't need a checker!
 */
void mm_checkheap(int verbose) {
  if (test)
    printf("checkheap\n\n");
}
