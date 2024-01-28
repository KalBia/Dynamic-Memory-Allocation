/* ---------------------------
 * KALINA BIAŁEK, 340152
 * ---------------------------
 *
 * Some of the code is based on mm-implicit.c and CSAPP chapter 9.9.
 *
 * ---------------------------
 *
 * Idea:
 *  We use optimized boundary tags with address ordered explicit free list.
 *
 * ---------------------------
 *
 * Pointers:
 *  We want pointers in free blocks to use only 4 bytes, so we need to
 *  realize that we will never use upper 4 bytes of addresses.
 *  We can store only distance from mem_heap_lo()!
 *
 *  relative address: distance from mem_heap_lo().
 *  real address: address normally stored by pointer.
 *
 * ------------------------------
 *
 * Blocks:
 *
 * [allocated block]
 *  word_t header
 *      31--Block Size--3-0-b-a
 *      where: a = 0 --> current block is free
 *             a = 1 --> current block is allocated
 *             b = 0 --> previous block is free
 *             b = 1 --> previous block is allocated
 *  payload of requested size
 *  (optional) padding
 *
 * [free block]
 *  word_t header
 *      31--Block Size--3-0-b-a
 *      where: a = 0 --> current block is free
 *             b = 0 --> previous block is free
 *             b = 1 --> previous block is allocated
 *  word_t ptr predecessor
 *  word_t ptr successor
 *  empty payload
 *  (optional) padding
 *  word_t footer
 *      31--Block Size--3-0-b-a
 *      where: a = 0 --> current block is free
 *             b = 0 --> previous block is free
 *             b = 1 --> previous block is allocated
 *
 * ----------------------------
 *
 * Guardian Angels:
 *
 *  Thanks to them we don't need to handle corner cases in some situations.
 *
 *  starting guardian: one word_t before heap_start
 *      - size in header: 0
 *      - marked as allocated
 *
 *  ending guardian: at the address of heap_end
 *      - size in header: 0
 *      - marked as allocated
 *      - holds information about allocation of last block in heap. We use it
 *        when extending the heap.
 *
 * ----------------------------
 *
 * Explicit free list:
 *
 *  start of the list: free_start
 *        address: two word_t before heap_start
 *
 *  end of the list: mem_heap_lo()
 *        why? Its address does not change during execution of the program,
 *             so it can be used as ending point.
 *             Easy to check in loops as ending condition.
 *
 * ----------------------------
 *
 * Allocating memory:
 *
 *  We loop through address ordered explicit free list. We stop at first fit,
 *  first free block that has size greater or equal than required size.
 *
 *  If the size of found block is big enough to split
 *      size of free block - required size >= ALIGNMENT
 *  than we can allocate the block of required size and make new free block from
 *  the rest of the old free block.
 *
 *  We erase old free block from explicit list and optionally add new free block
 *  created with splitting.
 *
 * ----------------------------
 *
 * Freeing memory:
 *
 *  We check if we can coalesce current block with next or previous block.
 *  We do it every time we free any block of memory.
 *
 *  We erase free "neighbors" of current block from list and add new bigger
 *  block at the end.
 *
 * ---------------------------
 *
 * Reallocating memory:
 *
 *  First we check, if we can just extend current block - if the next block is
 * free and big enough. If not, we find a new fit with malloc and copy the data
 * to the new place.
 *
 * ---------------------------
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

/* --=[ variables and others ]=------------------------------- */

typedef int32_t word_t; /* Heap is bascially an array of 4-byte words. */

static word_t *heap_start; /* Address of the first block */
static word_t *heap_end;   /* Address past last byte of last block */
static word_t *free_start; /* Adress of the start of free blocks list */

typedef enum {
  FREE = 0, /* Block is free */
  USED = 1, /* Block is used */
  PREV = 2, /* Previous block is free (optimized boundary tags) */
} bt_flags;

#define EXTEND_SIZE (1 << 9)

/* --=[ boundary tags ]=-------------------------- */

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
  printf("[%p]   %ld | %d | %d\n", tag, get_size(tag), is_prev_allocated(tag),
         is_allocated(tag));
}

/* -------------------------------------------- */

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

/* --------------------------------------------- */

/* Given payload pointer returns an address of boundary tag. */
static inline word_t *payload_to_tag(void *ptr) {
  return (word_t *)ptr - 1;
}

/* Given boundary tag pointer returns an address of payload. */
static inline word_t *tag_to_payload(word_t *tag) {
  return tag + 1;
}

/* Returns address of next block. */
static inline word_t *tag_next(void *tag) {
  word_t *next_tag = tag + get_size(tag);
  return next_tag;
}

/* Returns address of previous block. */
static inline word_t *tag_prev(void *tag) {
  if (is_prev_allocated(tag))
    return NULL;

  word_t *prev_tag = tag - get_size((word_t *)tag - 1);
  return prev_tag;
}

/* ---=[ blocks ]=---------------------------- */

static void create_free_block(word_t *tag, size_t size, bool is_prev_allocated,
                              word_t prev, word_t next) {
  /* create header */
  set_tag(tag, size, is_prev_allocated, FREE);

  /* create "pointers" */
  *(tag + 1) = prev;
  *(tag + 2) = next;

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

/* --=[ explicit free list ]=----------------------------------- */

/* We want pointers in free blocks to use only 4 bytes.
 * We will never use upper 4 bytes because of max range of heap.
 * So we can store only distance from mem_heap_lo()!
 * We call it further "relative address".
 * The "real address" will be the address that pointer would store. */

/* given relative address returns real address */
static inline word_t *ptr_to_tag(word_t ptr) {
  return (void *)mem_heap_lo() + ptr;
}

/* given real address returns relative address */
static inline word_t tag_to_ptr(word_t *tag) {
  return (word_t)((int64_t)tag & 0x00000000FFFFFFFF);
}

/* returns the tag of the next free block */
static inline word_t *free_next(word_t *tag) {
  if (tag == free_start)
    return ptr_to_tag(*tag);

  return ptr_to_tag(*(tag + 2));
}

/* returns the tag of the previous free block */
static inline word_t *free_prev(word_t *tag) {
  if (tag == free_start)
    return NULL;

  return ptr_to_tag(*(tag + 1));
}

/* sets relative pointer to prev free block in block 'tag' to 'new' */
static inline void set_prev_free(word_t *tag, word_t new) {
  if (tag != mem_heap_lo())
    *(tag + 1) = new;
}

/* sets relative pointer to next free block in block 'tag' to 'new' */
static inline void set_next_free(word_t *tag, word_t new) {
  if (tag != free_start)
    *(tag + 2) = new;
  else
    *free_start = new;
}

/* reconnect "pipes" so they skip block 'tag' in explicit free list */
static void erase_free_block(word_t *tag) {
  if (free_prev(tag) == free_start)
    *free_start = *(tag + 2);
  else
    set_next_free(free_prev(tag), *(tag + 2));

  if (free_next(tag) != mem_heap_lo())
    set_prev_free(free_next(tag), *(tag + 1));
}

/* [address ordered explicit list]
 * We loop through list to find the first free block with address
 * higher than block 'tag'.
 * It can't be equal - we don't store duplicates of free blocks. */
static void push_new_free(word_t *tag) {
  word_t *next = ptr_to_tag(*free_start);
  word_t *prev = free_start;

  /* while not end of list && address is lower than address of 'tag' */
  while ((next != mem_heap_lo()) && (next < tag)) {
    prev = next;
    next = free_next(next);
  }

  /* "pipe" from new one to next on list */
  set_next_free(tag, tag_to_ptr(next));

  /* "pipe" from new one to prev on list */
  set_prev_free(tag, tag_to_ptr(prev));

  /* "pipe" from prev on list to new one */
  set_next_free(prev, tag_to_ptr(tag));

  /* "pipe" from next on list to new one */
  set_prev_free(next, tag_to_ptr(tag));
}

/* --=[ init ]=----------------------------------- */
/*
 * mm_init - Called when a new trace starts.
 * We make initial padding, so the first payload starts at ALIGNMENT.
 * Then we remember the address of the first block of user data and where does
 * the heap end. We create guardian angels - "allocated blocks" at the end
 * and beginning of the heap. We don't need to check some corner cases anymore.
 * We assume that heap ends at the start of guardian angel at the end.
 * We add starting pointer of the free blocks list (explicit free list).
 */
/* ----------------------------------------------- */

int mm_init(void) {
  /* Pad heap start so first payload is at ALIGNMENT
   * and we need space for guardian angels. */
  void *ptr = morecore(ALIGNMENT);
  if (!ptr)
    return -1;

  /* we need to know, where is the first block, where does the heap end and
   * where does the free blocks list start */
  heap_start = ptr + ALIGNMENT - sizeof(word_t);
  heap_end = heap_start;
  free_start = ptr + ALIGNMENT - 3 * sizeof(word_t);

  /* list of free blocks is empty - the end of it we will mark as a "pointer" to
   * heap_lo */
  *free_start = 0;

  /* make guardian angel boundary tag before first user data block */
  set_tag(heap_start - 1, 0, USED, USED);
  /* make guardian angel boundary tag after empty heap */
  set_tag(heap_end, 0, USED, USED);

  return 0;
}

/* --=[ malloc ]=----------------------------------- */
/*
 * malloc - Find first fit in address ordered explicit free list and allocate
 * block there. Extend the heap if necessary. Always allocate a block whose size
 * is a multiple of the ALIGNMENT.
 */
/* ------------------------------------------------- */

/*
 * find_fit - Find first good match. We use explicit free list with adrress
 * ordering. If we don't find any fit, we extend the heap.
 */

static word_t *find_fit(size_t rqsize) {

  word_t *ptr = ptr_to_tag(*free_start);
  /* find first fit
   * As said before - end of explicit list is marked as "pointer" to heap_lo.
   *     (not passed end of list) &&
   *      (allocated already || too small) */
  while ((ptr != mem_heap_lo()) &&
         (is_allocated(ptr) || (get_size(ptr) < rqsize)))
    ptr = free_next(ptr);

  /* if we didn't find any fit - allocate new memory and make free block */
  if (ptr == mem_heap_lo()) {
    /* extend heap */
    size_t ext = (rqsize <= EXTEND_SIZE) ? EXTEND_SIZE : rqsize;
    ptr = morecore(ext);
    if (!ptr)
      return (void *)-1;

    /* TRICKY! morecore(...) returns pointer to the start of new given memory.
     * 'Cause we keep guardian angel at the end, we need to move pointer. */
    ptr = (void *)ptr - sizeof(word_t);

    /* we need to remember if the previous block before newly added space was
     * allocated */
    bool was_allocated = is_prev_allocated(heap_end);

    /* move guardian angel - prev is free, we just created extra space */
    set_tag((mem_heap_hi() + 1) - sizeof(word_t), 0, FREE, USED);

    /* update heap_end */
    heap_end = (mem_heap_hi() + 1) - sizeof(word_t);

    /* create empty block on the extended heap space */
    create_free_block(ptr, ext, was_allocated, 0, 0);

    /* push it to explicit free list */
    push_new_free(ptr);
  }

  return ptr;
}

/* -------------------------------------------- */

/* place - We found a fit in find_fit, now we have to allocate block there.
 * We split the fit into allocated and free block if it's possible.
 */

static void place(word_t *tag, size_t size, bool is_malloc_call) {
  /* we need to check if we can split this block */
  size_t split_size = get_size(tag) - size;

  /* we can split, if split_size is >= minimal word size (== ALIGNMENT)*/
  if (split_size >= ALIGNMENT) {
    /* make new free block after allocated block */
    void *new_free = (void *)tag + size;
    create_free_block(new_free, split_size, USED, 0, 0);

    /* put new free block in the list */
    push_new_free(new_free);

    /* make allocated block */
    create_allo_block(tag, size, is_prev_allocated(tag));
  }
  /* otherwise we do not split */
  else {
    /* just mark block as USED */
    set_allo(tag);

    /* update header of next block */
    set_prev_allo(tag_next(tag));
  }

  /* if it is malloc call (in case of realloc it's not free block!)
   *    erase free block from the explicit list */
  if (is_malloc_call)
    erase_free_block(tag);
}

/* -------------------------------------------- */

void *malloc(size_t size) {
  size = round_up(sizeof(word_t) + size);

  word_t *tag = find_fit(size);
  if ((long)tag < 0)
    return NULL;

  place(tag, size, true);

  return tag_to_payload(tag);
}

/* --=[ free ]=--------------------------------------- */
/*
 * free - Coalesce every time we free a block. Check both next
 * and previous block for potential coalescing.
 */
/* --------------------------------------------------- */

void free(void *ptr) {
  if (!ptr)
    return;

  /* ptr is pointing to PAYLOAD so we just need to move it to the header of the
   * block :D */
  ptr = payload_to_tag(ptr);

  /* free current block before coalesce and assume we will add this block to
   * explicit list */
  create_free_block(ptr, get_size(ptr), is_prev_allocated(ptr), 0, 0);
  void *add_to_list = ptr;

  /* if the next block is free */
  if (!is_allocated(tag_next(ptr))) {
    erase_free_block(tag_next(ptr));
    /* change header */
    set_size(ptr, get_size(ptr) + get_size(tag_next(ptr)));
    /* change footer */
    set_size(tag_next(ptr) - 1, get_size(ptr));
  }

  /* if the previous block is free
        change which block we add to explicit list */
  if (!is_prev_allocated(ptr)) {
    erase_free_block(tag_prev(ptr));
    create_free_block(tag_prev(ptr), get_size(ptr) + get_size(tag_prev(ptr)),
                      is_prev_allocated(tag_prev(ptr)), 0, 0);
    add_to_list = tag_prev(ptr);
  }

  /* add newly created free block to explicit list */
  push_new_free(add_to_list);

  /* change header of next block */
  clear_prev_allo(tag_next(ptr));
}

/* --=[ realloc ]=---------------------------------------- */
/*
 * realloc - Change the size of the block. First we check, if we can just extend
 * current block. If not, we find a new fit with malloc and copy the data.
 *
 * */
/* ------------------------------------------------------- */

void *realloc(void *old_ptr, size_t size) {

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

  /* check if we can just extend existing block */
  /* if (next block is free) and (there is enough space) */
  if ((!is_allocated(tag_next(ptr))) &&
      (get_size(ptr) + get_size(tag_next(ptr)) > rqsize)) {

    erase_free_block(tag_next(ptr));

    /* make it a big "free" block */
    /* change header */
    set_size(ptr, get_size(ptr) + get_size(tag_next(ptr)));
    /* change footer */
    set_size(tag_next(ptr) - 1, get_size(ptr));

    place(ptr, rqsize, false);

    return old_ptr;
  }

  /* we can't extend existing block - we need to find new one */
  void *new_ptr = malloc(size);

  /* If malloc() fails, the original block is left untouched. */
  if (!new_ptr)
    return NULL;

  /* Copy the old data. */
  memcpy(new_ptr, old_ptr, get_size(ptr));

  /* Free the old block. */
  free(old_ptr);

  return new_ptr;
}

/* --=[ calloc ]=---------------------------------------- */
/*
 * calloc - Allocate the block and set it to zero.
 * I leave it be - it's awesome as it is :D
 */
/* ------------------------------------------------------ */

void *calloc(size_t nmemb, size_t size) {

  size_t bytes = nmemb * size;
  void *new_ptr = malloc(bytes);

  /* If malloc() fails, skip zeroing out the memory. */
  if (new_ptr)
    memset(new_ptr, 0, bytes);

  return new_ptr;
}

/* --=[ checkheap ]=---------------------------------------- */
/*
 * mm_checkheap - I would love to say, that it's that simple as before...
 *
 * Numbers before invariants shows further in the code when are they checked.
 *
 * How it should be?
 *  1. Every block is correctly alligned to ALIGNMENT.
 *  2. Every header and footer of free block are the same.
 *  3.1. Every free block is on the free list.
 *  3.2. Every block on free list is marked as free and belongs to heap.
 *  3.3. Blocks on free list are sorted by address.
 *  3.4. Every free block has correct pointer to next block.
 *  4. No free block is adjacent to another free block.
 *  5. Every free block has correct pointer to previous block.
 */
/* -------------------------------------------------------- */

void mm_checkheap(int verbose) {

  if (verbose) {
    /* Print whole heap - every block with it's addres, size,
     * allocation and prev_allocation. */
    printf("\n\nwhole heap:\n");
    word_t *start = heap_start;
    while (start != heap_end) {
      print_tag(start);
      start = tag_next(start);
    }
    printf("\n\n");

    /* Print only explicit free list - with address, size,
     * allocation and prev allocation.
     * Additionally: address of prev and next free block on list. */
    printf("explicit list:\n");
    start = free_next(free_start);
    while (start != mem_heap_lo()) {
      print_tag(start);
      printf("prev: %p\n", ptr_to_tag(*(start + 1)));
      printf("next: %p\n", ptr_to_tag(*(start + 2)));
      start = free_next(start);
    }
    printf("\n\n");
  }

  /* check correctness of the whole heap */
  word_t *every_block = heap_start;
  word_t *free_block = free_next(free_start); /* first free block */
  word_t *prev_free_block =
    free_start; /* needed to check if prev pointers are correct */

  while ((every_block != heap_end) && (free_block != mem_heap_lo())) {

    /* 1. check if block is correctly alligned to ALIGNMENT */
    /* payload address start at multiple of ALIGNMENT */
    if ((int64_t)tag_to_payload(every_block) % ALIGNMENT != 0) {
      printf("block %p not aligned correctly (cause: payload address): %p\n",
             every_block, tag_to_payload(every_block));
      return;
    }

    /* size is a multiple of ALIGNMENT */
    if ((int64_t)get_size(every_block) % ALIGNMENT != 0) {
      printf("block %p not aligned correctly (cause: size): %ld\n", every_block,
             get_size(every_block));
      return;
    }

    /* 2. check if header and footer of free block are the same */
    if (!is_allocated(every_block) &&
        *every_block != *(tag_next(every_block) - 1)) {
      printf("block %p has not matching footer and header\n", every_block);
      return;
    }

    /* 3. check if the free block is on the list of free blocks */
    /* We have them sorted by address on list, so the first free block
     * in the loop should be the first block on the list as well. */
    if (!is_allocated(every_block) && free_block != every_block) {
      printf("block %p is not on the list of free blocks, is not sorted or has "
             "incorrect next pointer\n",
             every_block);
      return;
    }

    /* 4. check if the free block is a neighbour of another free block */
    /* We have guardian angels, so we don't need to check corner cases. */
    if (!is_allocated(every_block) && (!is_prev_allocated(every_block) ||
                                       !is_allocated(tag_next(every_block)))) {
      printf("block %p is free and has a free neighbor\n", every_block);
      return;
    }

    /* 5. check if free block has correct pointer to previous free block */
    if (free_prev(free_block) != prev_free_block) {
      printf("block %p has incorrect pointer to previous free block\n",
             free_block);
      return;
    }

    /* if block was free move to next free block on list and update prev free */
    if (!is_allocated(every_block)) {
      prev_free_block = free_block;
      free_block = free_next(free_block);
    }

    /* move to next block */
    every_block = tag_next(every_block);
  }
}
