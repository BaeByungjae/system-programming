/* 
 * Simple, 32-bit and 64-bit clean allocator based on implicit free
 * lists, first-fit placement, and boundary tag coalescing, as described
 * in the CS:APP3e text. Blocks must be aligned to doubleword (8 byte) 
 * boundaries. Minimum block size is 16 bytes. 
 * Each block has header and footer of the form:
 * 
 *      31                     3  2  1  0 
 *      -----------------------------------
 *     | s  s  s  s  ... s  s  s  0  0  a/f
 *      ----------------------------------- 
 * 
 * where s are the meaningful size bits and a/f is set 
 * iff the block is allocated. The list has the following form:
 *
 * begin                                                          end
 * heap                                                           heap  
 *  -----------------------------------------------------------------   
 * |  pad   | hdr(8:a) | ftr(8:a) | zero or more usr blks | hdr(8:a) |
 *  -----------------------------------------------------------------
 *          |       prologue      |                       | epilogue |
 *          |         block       |                       | block    |
 free_block
 */
#include <stdio.h>
#include <string.h>
#include <stdlib.h>

#include "mm.h"
#include "memlib.h"



/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

#define BUFFER (1<<7) /* Reallocation buffer */


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* Basic constants and macros */
#define WSIZE       4       /* Word and header/footer size (bytes) */ 
#define DSIZE       8       /* Double word size (bytes) */
#define CHUNKSIZE  (1<<12)  /* Extend heap by this amount (bytes) */ 

#define MAX(x, y) ((x) > (y)? (x) : (y))  
#define MIN(x, y) ((x) > (y)? (y) : (x))  

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc)) 

/* Read and write a word at address p */
#define GET(p)       (*(unsigned int *)(p))        
// Preserve reallocation bit
#define PUT(p, val)       (*(size_t *)(p) = (val) | GET_TAG(p))
// Clear reallocation bit
#define PUT_NOTAG(p, val) (*(size_t *)(p) = (val))

/* Adjust the reallocation tag */
#define SET_TAG(p)   (*(size_t *)(p) = GET(p) | 0x2)//2bit tag
#define UNSET_TAG(p) (*(size_t *)(p) = GET(p) & ~0x2)//untagging

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)             
#define GET_ALLOC(p) (GET(p) & 0x1)  
#define GET_TAG(p)   (GET(p) & 0x2)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)                     
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) 

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) 
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) 
/* $end mallocmacros */

/* Global variables */
static char *heap_listp = 0;  /* Pointer to first block */  
static char *rover;           /* Next fit rover */

/* Function prototypes for internal helper routines */
static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);
static void printblock(void *bp); 
static void mm_checkheap(int verbose);
static void checkblock(void *bp);


/* 
 * mm_init - Initialize the memory manager 
 */

int mm_init(void) 
{
    /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1) //line:vm:mm:begininit
        return -1;
    PUT_NOTAG(heap_listp, 0);                            /* Alignment padding */
    PUT_NOTAG(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); /* Prologue header */
    PUT_NOTAG(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
    PUT_NOTAG(heap_listp + (3 * WSIZE), PACK(0, 1)); /* Epilogue header */
     heap_listp += (2*WSIZE);                     
	/*none reallocated init*/
    rover = heap_listp;//next_fit

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL) 
        return -1;
    return 0;
}

/* 
 * mm_malloc - Allocate a block with at least size bytes of payload 
 */
void *mm_malloc(size_t size) 
{
    size_t asize;      /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    char *bp;      
/*if heap_listp is not defined*/
    if (heap_listp == 0){
        mm_init();
    }
    /* Ignore size==0 requests */
    if (size == 0)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE)                                          
        asize = 2*DSIZE;//mutilpe of 8                                        
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);//over size of round up of mutiple 8 

    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {  
          

        place(bp, asize); //asize byte block is placed first of bp or split                   

        return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize,CHUNKSIZE);

    if ((bp = extend_heap(extendsize)) == NULL)  
        return NULL;                                  
    place(bp, asize);//asize byte block is placed first of bp or split                                 

    return bp;
} 

/* 
 * mm_free - Free a block 
 */

void mm_free(void *bp)
{
    if (bp == 0) 
        return;

    size_t size = GET_SIZE(HDRP(bp)); //size of bp
    /*if heap_listp is not defined*/
    if (heap_listp == 0){
        mm_init();
    }

 
    /* Unset the reallocation tag on the next block */
    UNSET_TAG(HDRP(NEXT_BLKP(bp)));
  
    /* Adjust the allocation status in boundary tags */
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);//if necessary merge
}
 

/*
 * coalesce - Boundary tag coalescing. Return ptr to coalesced block
 */
static void *coalesce(void *ptr) 
{    /*Check if the prev_blk,next_blk are allocated*/  
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(ptr)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(ptr)));
    size_t size = GET_SIZE(HDRP(ptr));
    

    // Do not coalesce with previous block if the previous block is tagged with Reallocation tag
    if (GET_TAG(HDRP(PREV_BLKP(ptr))))
        prev_alloc = 1;
    /*if two are allocated not merger*/ 
    if (prev_alloc && next_alloc) {                         // Case 1
        return ptr;
    }
    /* if prev is only allocated next and ptr are merged*/ 
    else if (prev_alloc && !next_alloc) {                   // Case 2
        size += GET_SIZE(HDRP(NEXT_BLKP(ptr)));
        PUT(HDRP(ptr), PACK(size, 0));
        PUT(FTRP(ptr), PACK(size, 0));
    /* if next is only allocated prev and ptr are merged*/
    } else if (!prev_alloc && next_alloc) {                 // Case 3 
        size += GET_SIZE(HDRP(PREV_BLKP(ptr)));
        PUT(FTRP(ptr), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(ptr)), PACK(size, 0));
        ptr = PREV_BLKP(ptr);
     /*if two are not allocated, prev and next and ptr are merged*/
    } else {                                                // Case 4
        size += GET_SIZE(HDRP(PREV_BLKP(ptr))) + GET_SIZE(HDRP(NEXT_BLKP(ptr)));
        PUT(HDRP(PREV_BLKP(ptr)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(ptr)), PACK(size, 0));
        ptr = PREV_BLKP(ptr);
    }
        
    /* Make sure the rover isn't pointing into the free block */
    /* that we just coalesced */
    //next_fit implimented
    if ((rover > (char *)ptr) && (rover < NEXT_BLKP(ptr))) 
        rover = ptr;
    return ptr;
}

/*
 * mm_realloc - Naive implementation of realloc
 */
void *mm_realloc(void *ptr, size_t size)
{
  void *new_ptr = ptr;    /* Pointer to be returned */
  size_t new_size = size; /* Size of new block */
  int asize;          /* Adequacy of block sizes */
  int extendsize;         /* Size of heap extension */
  int block_buffer;       /* Size of block buffer */
  
  /* Filter invalid block size */
  if (size == 0)
    return NULL;
  
  /* Adjust block size to include boundary tag and alignment requirements */
  if (new_size <= DSIZE) {
    new_size = 2 * DSIZE;
  } else {
    new_size = ALIGN(size+DSIZE);
  }
  
  /* Add overhead requirements to block size */
  new_size += BUFFER;
  
  /* Calculate block buffer */
  block_buffer = GET_SIZE(HDRP(ptr)) - new_size;
  
  /* Allocate more space if overhead falls below the minimum */
  if (block_buffer < 0) {
    /* Check if next block is a free block or the epilogue block */
    if (!GET_ALLOC(HDRP(NEXT_BLKP(ptr))) || !GET_SIZE(HDRP(NEXT_BLKP(ptr)))) {
      /* Check ptr and next block size */
      asize = GET_SIZE(HDRP(ptr)) + GET_SIZE(HDRP(NEXT_BLKP(ptr))) - new_size;
      if (asize < 0) {
        extendsize = MAX(-asize, CHUNKSIZE);
        if (extend_heap(extendsize) == NULL)/*heap is extended is not null*/
          return NULL;
        asize += extendsize;
      }
      
      // Do not split block and not malloc -> next and ptr are merged so, realloced
      PUT_NOTAG(HDRP(ptr), PACK(new_size + asize, 1)); /* Block header */
      PUT_NOTAG(FTRP(ptr), PACK(new_size + asize, 1)); /* Block footer */
    } 
	else {
      new_ptr = mm_malloc(new_size);/*realloced block*/
      memcpy(new_ptr, ptr, MIN(size, new_size));/*data is moved to realloced blokc*/
      mm_free(ptr);/*after realloced and old_ptr free*/
    }
    block_buffer = GET_SIZE(HDRP(new_ptr)) - new_size;
  }  

  /* Tag the next block if block overhead drops below twice the overhead */
  if (block_buffer < 2 * BUFFER)
    SET_TAG(HDRP(NEXT_BLKP(new_ptr)));

  /* Return reallocated block */
return new_ptr;
}



/* 
 * The remaining routines are internal helper routines 
 */

/* 
 * extend_heap - Extend heap with free block and return its block pointer
 */
static void *extend_heap(size_t size) 
{
    void *ptr;                   
    size_t asize;                // Adjusted size 
    
    asize = ALIGN(size);
    
    if ((ptr = mem_sbrk(asize)) == (void *)-1)
        return NULL;
    
    // Set headers and footer 
    PUT_NOTAG(HDRP(ptr), PACK(asize, 0));  
    PUT_NOTAG(FTRP(ptr), PACK(asize, 0));   
    PUT_NOTAG(HDRP(NEXT_BLKP(ptr)), PACK(0, 1)); 

    return coalesce(ptr);                     
}

/* 
 * place - Place block of asize bytes at start of free block bp 
 *         and split if remainder would be at least minimum block size
 */
static void place(void *ptr, size_t asize)
{
      size_t csize = GET_SIZE(HDRP(ptr));
      size_t size = csize - asize;
      if (size >= 2*DSIZE) {
        /* Split block */
        PUT(HDRP(ptr), PACK(asize, 1)); /* Block header */
        PUT(FTRP(ptr), PACK(asize, 1)); /* Block footer */
        PUT_NOTAG(HDRP(NEXT_BLKP(ptr)), PACK(size, 0)); /* Next header */
        PUT_NOTAG(FTRP(NEXT_BLKP(ptr)), PACK(size, 0)); /* Next footer */  
      } else {
        /* Do not split block */
        PUT(HDRP(ptr), PACK(csize, 1)); /* Block header */
        PUT(FTRP(ptr), PACK(csize, 1)); /* Block footer */
      }
    return;
}

/* 
 * find_fit - Find a fit for a block with asize bytes 
 */

static void *find_fit(size_t asize)
{

    /* Next fit search */
    char *oldrover = rover;


    /* Search from the rover to the end of list */
    for ( ; GET_SIZE(HDRP(rover)) > 0; rover = NEXT_BLKP(rover))
        if ((!GET_ALLOC(HDRP(rover)) && (asize <= GET_SIZE(HDRP(rover)))) && !(GET_TAG(HDRP(rover))))
            return rover;

    /* search from start of list to old rover */
    for (rover = heap_listp; rover < oldrover; rover = NEXT_BLKP(rover))
        if ((!GET_ALLOC(HDRP(rover)) && (asize <= GET_SIZE(HDRP(rover)))) && !(GET_TAG(HDRP(rover))))
            return rover;

    return NULL;  /* no fit found */

}
/* $end mmfirstfit */

static void printblock(void *bp) 
{
    size_t hsize, halloc, fsize, falloc;

    mm_checkheap(0);
    hsize = GET_SIZE(HDRP(bp));
    halloc = GET_ALLOC(HDRP(bp));  
    fsize = GET_SIZE(FTRP(bp));
    falloc = GET_ALLOC(FTRP(bp));  

    if (hsize == 0) {
        printf("%p: EOL\n", bp);
        return;
    }

    printf("%p: header: [%ld:%c] footer: [%ld:%c]\n", bp, 
           hsize, (halloc ? 'a' : 'f'), 
           fsize, (falloc ? 'a' : 'f')); 
}

static void checkblock(void *bp) 
{
    if ((size_t)bp % 8)
        printf("Error: %p is not doubleword aligned\n", bp);
    if (GET(HDRP(bp)) != GET(FTRP(bp)))
        printf("Error: header does not match footer\n");
}

/* 
 * mm_checkheap - Check the heap for correctnes
*/
void mm_checkheap(int verbose) 
{
    char *bp = heap_listp;

    if (verbose)
        printf("Heap (%p):\n", heap_listp);

    if ((GET_SIZE(HDRP(heap_listp)) != DSIZE) || !GET_ALLOC(HDRP(heap_listp)))
        printf("Bad prologue header\n");
    checkblock(heap_listp);

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (verbose) 
            printblock(bp);
        checkblock(bp);
    }

    if (verbose)
        printblock(bp);
    if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp))))
        printf("Bad epilogue header\n");
}

