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

typedef int32_t word_t; /* Heap is bascially an array of 4-byte words. */

/* [allocated block]
 * word_t header
 *      31--Block Size--3-0-b-a
 *      where: a = 0 --> current block is free
 *             a = 1 --> current block is allocated
 *             b = 0 --> previous block is free
 *             b = 1 --> previous block is allocated
 * payload of requested size
 * (optional) padding
 */

/* [free block]
 * word_t header
 *      31--Block Size--3-0-b-a
 *      where: a = 0 --> current block is free
 *             b = 0 --> previous block is free
 *             b = 1 --> previous block is allocated
 * empty payload
 * word_t footer
 *      31--Block Size--3-0-b-a
 *      where: a = 0 --> current block is free
 *             b = 0 --> previous block is free
 *             b = 1 --> previous block is allocated
 */

static word_t *heap_start;  /* Address of the first block */
static word_t *heap_end;    /* Address past last byte of last block */
/* static word_t *last;  */ /* Points at last block */

typedef enum {
  FREE = 0, /* Block is free */
  USED = 1, /* Block is used */
  PREV = 2, /* Previous block is free (optimized boundary tags) */
} bt_flags;

#define EXTEND_SIZE (1 << 9)
#define test false

/* --=[ basic procedures for code clarity
 * ]=-------------------------------------------- */

static inline size_t round_up(size_t size) {
  return (size + ALIGNMENT - 1) & -ALIGNMENT;
}

static inline bool is_allocated(word_t *tag) {
  return *tag & USED;
}

static inline bool is_prev_allocated(word_t *tag) {
  return *tag & PREV;
}

static inline size_t get_size(word_t *tag) {
  return *tag & -4;
}

static inline void print_tag(word_t *tag) {
  printf("%ld | %d | %d\n", get_size(tag), is_prev_allocated(tag),
         is_allocated(tag));
}

/* -------------------------------------------------------------------------------------
 */

static inline void set_size(word_t *tag, size_t size) {
  *tag = size | (is_prev_allocated(tag) << 1) | is_allocated(tag);
}

static inline void set_tag(word_t *tag, size_t size, bool is_prev_allocated,
                           bool is_allocated) {
  *tag = size | (is_prev_allocated << 1) | is_allocated;
}

static inline void set_allo(word_t *tag) {
  *tag |= USED;
}

static inline void clear_allo(word_t *tag) {
  if (tag)
    *tag &= ~USED;
}

static inline void set_prev_allo(word_t *tag) {
  *tag |= PREV;
}

static inline void clear_prev_allo(word_t *tag) {
  if (tag)
    *tag &= ~PREV;
}

/* -------------------------------------------------------------------------------------
 */

/* Given payload pointer returns an address of boundary tag. */
static inline word_t *payload_to_tag(void *ptr) {
  return (word_t *)ptr - 1;
}

/* Given boundary tag pointer returns an address of payload. */
static inline word_t *tag_to_payload(word_t *tag) {
  return tag + 1;
}

/* Returns address of next block or NULL. */
static inline word_t *tag_next(void *tag) {
  word_t *next_tag = tag + get_size(tag);
  if (next_tag != heap_end)
    return next_tag;
  return NULL;
}

/* Returns address of previous block or NULL. */
static inline word_t *tag_prev(void *tag) {
  if (is_prev_allocated(tag))
    return NULL;

  word_t *prev_tag = tag - get_size((word_t *)tag - 1);
  return prev_tag;
}

/* -------------------------------------------------------------------------------------
 */

static void create_free_block(word_t *tag, size_t size,
                              bool is_prev_allocated) {
  /* create header */
  set_tag(tag, size, is_prev_allocated, FREE);

  /* create footer */
  set_tag((void *)tag + size - sizeof(word_t), size, is_prev_allocated, FREE);
}

static void create_allo_block(word_t *tag, size_t size,
                              bool is_prev_allocated) {
  /* create header */
  set_tag(tag, size, is_prev_allocated, USED);
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
 * We make initial padding, so the first payload start at ALIGNMENT.
 * Then we remember the address of the first block of user data and where does
 * the heap end. We create guardian angel - footer of empty, allocated block.
 */
/* -------------------------------------------------------- */

int mm_init(void) {
  /* Pad heap start so first payload is at ALIGNMENT. */
  void *ptr = morecore(ALIGNMENT - sizeof(word_t));
  if (!ptr)
    return -1;

  /* we need to know, where is the first block and where does the heap end */
  heap_start = ptr + ALIGNMENT - sizeof(word_t);
  heap_end = heap_start;

  if (test)
    printf("heap_start: %p\n", heap_start);

  /* make guardian angel boundary tag before first user data block */
  set_tag(heap_start - 1, sizeof(word_t), USED, USED);

  if (test) {
    printf("Guardian angel header: ");
    print_tag(heap_start - 1);
    printf("\n\n");
  }

  return 0;
}

/* --=[ malloc ]=-------------------------------------------- */
/*
 * malloc - Find first good fit and allocate block there. Extend the heap if
 * necessary. Always allocate a block whose size is a multiple of the ALIGNMENT.
 */
/* ---------------------------------------------------------- */

/*
 * find_fit - Find first good match. We start searching from the first data
 * block. If we don't find any fit, we extend the heap.
 */

static word_t *find_fit(size_t rqsize) {
  if (test)
    printf("find_fit\n");

  void *ptr = heap_start;
  void *prev = (word_t *)ptr - 1;

  if ((word_t *)ptr == heap_end)
    ptr = NULL;

  /* find first fit
   * not passed end && (allocated already || too small) */
  while (ptr && (is_allocated(ptr) || (get_size(ptr) < rqsize))) {
    prev = ptr;
    ptr = tag_next(ptr);
  }

  if (test) {
    if (ptr) {
      printf("ptr after loop: %p\n", ptr);
      printf("header of ptr: ");
      print_tag(ptr);
    } else
      printf("ptr == heap end\n");

    printf("heap_end | heap_size : %p | %ld\n", heap_end, mem_heapsize());
    printf("end of heap: %p\n", mem_heap_hi());
  }

  /* if we didn't find any fit - allocate new memory and make free block_t */
  if (!ptr) {
    /* extend heap */
    size_t ext = (rqsize <= EXTEND_SIZE) ? EXTEND_SIZE : rqsize;
    ptr = morecore(ext);
    if (!ptr)
      return (void *)-1;

    /* update heap_end */
    heap_end = mem_heap_hi() + 1;

    if (test) {
      printf(
        "after allocating new heap memory - heap_end | heap_size : %p | %ld\n",
        heap_end, mem_heapsize());
      printf("end of heap: %p\n", mem_heap_hi());
    }

    /* create empty block on the extended heap space */
    create_free_block(ptr, ext, is_allocated(prev));
  }

  if (test)
    printf("end find_fit\n");

  return ptr;
}

/* -------------------------------------------- */

/* place - We found a fit in find_fit, now we have to allocate block there.
 * We split the fit into allocated and free block if it's possible.
 */

static void place(word_t *tag, size_t size) {
  if (test)
    printf("place\n");

  /* we need to check if we can split this block */
  size_t split_size = get_size(tag) - size;

  if (test)
    printf("split_size: %ld\n", split_size);

  /* we can split, if split_size is >= minimal word size (== ALIGNMENT)*/
  if (split_size >= ALIGNMENT) {
    /* make new free block after allocated block */
    void *new_free = (void *)tag + size;
    create_free_block(new_free, split_size, USED);

    if (test) {
      printf("new free block: ");
      print_tag(new_free);
    }

    /* make allocated block */
    create_allo_block(tag, size, is_prev_allocated(tag));
  }
  /* we do not split otherwise */
  else {
    /* just mark block as USED */
    set_allo(tag);

    /* update header of next block */
    if (tag_next(tag))
      set_prev_allo(tag_next(tag));
  }

  if (test) {
    printf("header of block: ");
    print_tag(tag);
    printf("end place\n");
  }
}

/* -------------------------------------------- */

void *malloc(size_t size) {
  if (test)
    printf("malloc with size: %ld\n", size);

  size = round_up(sizeof(word_t) + size);

  if (test)
    printf("malloc with round-up size: %ld\n", size);

  word_t *tag = find_fit(size);
  if ((long)tag < 0)
    return NULL;

  place(tag, size);

  if (test) {
    printf("end of heap: %p\n", mem_heap_hi());
    printf("tag | payload : %p | %p\n\n\n", tag, tag_to_payload(tag));
  }

  return tag_to_payload(tag);
}

/* --=[ free ]=-------------------------------------------- */
/*
 * free - Maybe we shouldn't ignore it... Let's try to free some space.
 * We coalesce every time we free a block.
 */
/* -------------------------------------------------------- */

void free(void *ptr) {
  if (!ptr)
    return;

  /* ptr is pointing to PAYLOAD so we just need to move it to the header of the
   * block :D */
  ptr = payload_to_tag(ptr);

  if (test) {
    printf("free with ptr: %p\n", ptr);
    printf("header of block: ");
    print_tag(ptr);

    if (tag_next(ptr)) {
      printf("header of next block: ");
      print_tag(tag_next(ptr));
    } else
      printf("next block == heap end\n");
  }

  /* free current block before coalesce */
  create_free_block(ptr, get_size(ptr), is_prev_allocated(ptr));

  /* if the next block is not heap end and is free */
  if (tag_next(ptr) && !is_allocated(tag_next(ptr)))
    create_free_block(ptr, get_size(ptr) + get_size(tag_next(ptr)),
                      is_prev_allocated(ptr));

  if (test) {
    printf("after next block check\n");
    printf("header of block: ");
    print_tag(ptr);
  }

  /* if the previous block is free */
  if (!is_prev_allocated(ptr))
    create_free_block(tag_prev(ptr), get_size(ptr) + get_size(tag_prev(ptr)),
                      is_prev_allocated(tag_prev(ptr)));

  if (test) {
    printf("after prev block check\n");
    printf("header of block: ");
    print_tag(ptr);
  }

  /* change header of next block */
  if (tag_next(ptr))
    clear_prev_allo(tag_next(ptr));

  if (test) {
    if (tag_next(ptr)) {
      printf("header of next block: ");
      print_tag(tag_next(ptr));
    } else
      printf("next block == heap end\n");

    printf("\n\n");
  }
}

/* --=[ realloc ]=-------------------------------------------- */
/*
 * realloc - Change the size of the block. First we check, if we can just extend
 *current block. If not, we find a new fit with malloc.
 **/
/* ----------------------------------------------------------- */

void *realloc(void *old_ptr, size_t size) {
  if (test)
    printf("realloc with ptr and size: %p | %ld\n", payload_to_tag(old_ptr),
           size);

  /* If size == 0 then this is just free, and we return NULL. */
  if (size == 0) {
    free(old_ptr);
    return NULL;
  }

  /* If old_ptr is NULL, then this is just malloc. */
  if (!old_ptr)
    return malloc(size);

  /* we got pointer to PAYLOAD! */
  void *ptr = payload_to_tag(old_ptr);

  /* we need to keep alignment happy */
  size_t rqsize = round_up(sizeof(word_t) + size);

  /* we do not shrink blocks - it's not worth it */
  if (rqsize <= get_size(ptr))
    return old_ptr;

  if (test) {
    printf("size after round_up: %ld\n", rqsize);
    printf("current block: ");
    print_tag(ptr);

    if (tag_next(ptr)) {
      printf("header of next block: ");
      print_tag(tag_next(ptr));
    } else
      printf("next block == heap end\n");
  }

  /* check if we can just extend existing block */
  /* if next block is not heap_end and is free and there is enough space */
  if (tag_next(ptr) && (!is_allocated(tag_next(ptr))) &&
      (get_size(ptr) + get_size(tag_next(ptr)) > rqsize)) {
    if (test)
      printf("next block is free!\n");

    set_size(ptr, get_size(ptr) + get_size(tag_next(ptr)));
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
  memcpy(new_ptr, old_ptr, get_size(ptr));

  /* Free the old block. */
  free(old_ptr);

  if (test)
    printf("\n\n");

  return new_ptr;
}

/* --=[ calloc ]=-------------------------------------------- */
/*
 * calloc - Allocate the block and set it to zero.
 * I leave it be - it's awesome :D
 */
/* ---------------------------------------------------------- */

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
/* ------------------------------------------------------------- */

void mm_checkheap(int verbose) {
  if (test)
    printf("checkheap\n\n");

  if (verbose) {
    word_t *start = heap_start;
    printf("\n\n\n");
    while (start) {
      printf("address: %p | ", start);
      print_tag(start);
      start = tag_next(start);
    }
    printf("\n\n\n");
  }
}
