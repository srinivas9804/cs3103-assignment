/*
 * SPECS
 * ----------------------------
 * Segregated (explicit) lists. Each list is maintained in an ascending order.
 *
 * VITAL STATISTICS
 * -----------------
 * Minimum block size:  24 bytes
 *
 *
 * ANATOMY OF BLOCKS:
 *
 * size of header = 4 bytes
 * size of footer = 4 bytes
 * size of next free block ptr = 8 bytes
 * size of next prev block ptr = 8 bytes
 * 
 * >>>> Free Block
 * +-----------+-----------------------+-----------------------+-----------------------+-----------+
 * | header    |    previous block     |      next block       |      .....            | footer    |
 * +-----------+-----------------------+-----------------------+-----------------------+-----------+
 *
 * >>>> Allocated Block
 * +-----------+-----------------------+-----------------------+-----------------------+-----------+
 * | header    |                                  data                                 | footer    |
 * +-----------+-----------------------+-----------------------+-----------------------+-----------+
 *
 * >>>> Prologue Block
 * +-----------+-----------------------+-----------------------+-----------+
 * | header    |    previous block     |      next block       | footer    |
 * +-----------+-----------------------+-----------------------+-----------+
 *
 * >>>> Epilogue Block
 * +-----------+
 * | header    |
 * +-----------+
 *
 * MALLOC
 * ---------------------
 * In this approach, a block is allocated by first finding the free list of the same size class.
 * Then the list is traversed to find the first block that's big enough for the allocation request.
 * If a free block is too big (unused poriton is big enough to be a free block), split the block.
 *
 * FREEING:
 * ----------------------
 * Newly freed blocks are inserted into the free list in such a way that the list remains sorted.
 *
 */
#include <stdio.h>
#include <string.h>
#include <stdlib.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your group information in the following struct.
 ********************************************************/
group_t group = {
        /* Project group number (You're required to join a group on Canvas) */
        "34",
        /* First member's full name */
        "NDER Sesugh",
        /* First member's email address */
        "samuender2-c@my.cityu.edu.hk",
        /* Second member's full name (leave blank if none) */
        "SIVAKUMAR Srinivas",
        /* Second member's email address (leave blank if none) */
        "ssivakuma2-c@my.cityu.edu.hk",
        /* Third member's full name (leave blank if none) */
        "",
        /* Third member's email address (leave blank if none) */
        ""
};

/* Basic constants and macros */
#define WSIZE       4       /* Word and header/footer size (bytes) */
#define DSIZE       8       /* Doubleword size (bytes) */
#define CHUNKSIZE  (1<<12)  /* Extend heap by this amount (bytes) */
#define MIN_BLK_SIZE    24
#define START_SHIFT 5
#define INIT_CHUNK_SIZE CHUNKSIZE/WSIZE
#define NUM_CLASSES 300

#define MAX(x, y) ((x) > (y)? (x) : (y))
#define ALIGN(size) (DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)       (*(int*)(p))
#define PUT(p, val)  (*(int*)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)   ((void*)(bp) - WSIZE)
#define FTRP(bp)   ((void*)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of (physically) next and previous blocks */
#define NEXT_BLKP(bp)  ((void* )(bp) + GET_SIZE(HDRP(bp)))
#define PREV_BLKP(bp)  ((void* )(bp) - GET_SIZE(HDRP(bp) - WSIZE))

/* Given free block ptr, bp, compute address of next and previous blocks*/
#define NEXT_FREEP(bp)  (*(void**)(bp + DSIZE))
#define PREV_FREEP(bp)  (*(void**)(bp))

/* Given a free block ptr, bp, compute the POINTER to the address of next and previous blocks*/
#define BLK_NEXT(bp)  ((void*)bp + DSIZE)
#define BLK_PREV(bp)  ((void*)bp)

/* Global variables */
static void *heap_listp = 0;  /* Pointer to first block */
static void *free_list[NUM_CLASSES]; // Each list is maintained in ascending order
// static void *epilogue = NULL;

/* Function prototypes for internal helper routines */
static void *extend_heap(size_t words);

static void *place(void *bp, size_t asize);

static void *find_fit(size_t asize);

static void *coalesce(void *bp);

static inline int get_size_class(size_t asize);

static inline void insert_block(void *ptr);

static void delete_block(void *ptr);


/*
 * mm_init - Initialize the memory manager
 *
 */
int mm_init(void) {
    /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk(4 * DSIZE)) == (void *) -1)
        return -1;

    for (int i = 0; i < NUM_CLASSES; i++) {
        free_list[i] = NULL;
    }

    /* Padding */
    PUT(heap_listp, 0);

    /* Prologue */
    PUT(heap_listp + WSIZE, PACK(MIN_BLK_SIZE, 1)); // header
    PUT(heap_listp + DSIZE, 0); // prev
    PUT(heap_listp + DSIZE * 2, 0); // next
    PUT(heap_listp + DSIZE * 3, PACK(MIN_BLK_SIZE, 1)); // footer

    /* Epilogue */
    PUT(heap_listp + DSIZE * 3 + WSIZE, PACK(0, 1)); // header only


    //-------------------------------------------------------
    //epilogue = heap_listp + DSIZE * 3 + WSIZE;

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    // if (extend_heap(INIT_CHUNK_SIZE) == NULL)
    //    return -1;
    return 0;
}

/*
 * mm_malloc - Allocate a block with at least size bytes of payload
 */
void *mm_malloc(size_t size) {
    size_t asize;      /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    char *bp;

    if (heap_listp == 0) {
        mm_init();
    }
    /* Ignore spurious requests */
    if (size == 0)
        return NULL;

    asize = MAX(ALIGN(size), MIN_BLK_SIZE);
    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {
        return place(bp, asize);
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;
 
    return place(bp, asize);
}

/*
 * mm_free - Free a block, bp
 */
void mm_free(void *bp) {
    if (bp == 0)
        return;

    if (heap_listp == 0) {
        mm_init();
    }

    size_t size = GET_SIZE(HDRP(bp));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));

    coalesce(bp);
}

/*
 * coalesce - Boundary tag coalescing. 
 * Inserts into segregated list and returns ptr to coalesced block
 */
static void *coalesce(void *ptr) {
    size_t prev_alloc = GET_ALLOC(HDRP(PREV_BLKP(ptr)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(ptr)));
    size_t size = GET_SIZE(HDRP(ptr));

    /* 
    * Case 1 
    */
    if (prev_alloc && next_alloc) {
        // do nothing
    }
    /*
    * Case 2: increase block right
    */
    else if (prev_alloc && !next_alloc) {
        size += GET_SIZE(HDRP(NEXT_BLKP(ptr)));
        delete_block(NEXT_BLKP(ptr));

        PUT(HDRP(ptr), PACK(size, 0));
        PUT(FTRP(ptr), PACK(size, 0));
    }
    /*
    * Case 3: increase block left
    */
    else if (!prev_alloc && next_alloc) {
        size += GET_SIZE(HDRP(PREV_BLKP(ptr)));
        delete_block(PREV_BLKP(ptr));

        ptr = PREV_BLKP(ptr);
        PUT(HDRP(ptr), PACK(size, 0));
        PUT(FTRP(ptr), PACK(size, 0));
    }
    /*
    * Case 4: increase block in both directions
    */
    else {
        delete_block(PREV_BLKP(ptr));
        delete_block(NEXT_BLKP(ptr));
        size += GET_SIZE(HDRP(PREV_BLKP(ptr))) + GET_SIZE(HDRP(NEXT_BLKP(ptr)));
        ptr = PREV_BLKP(ptr);
        PUT(HDRP(ptr), PACK(size, 0));
        PUT(FTRP(ptr), PACK(size, 0));
    }

    insert_block(ptr);
    return ptr;
}


/*
 * The remaining routines are internal helper routines
 */

/*
 * extend_heap - Extend heap with free block and return its block pointer
 */
static void *extend_heap(size_t words) {
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    size = MAX(size, MIN_BLK_SIZE);
    if ((long) (bp = mem_sbrk(size)) == -1)
        return NULL;

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));         /* Free block header */
    PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */

    // epilogue = HDRP(NEXT_BLKP(bp));

    return coalesce(bp);
}

/*
 * place - Place block of asize bytes at start of free block bp
 *         and split if remainder would be at least minimum block size
 */
static void *place(void *bp, size_t asize) {
    size_t csize = GET_SIZE(HDRP(bp));
    size_t remainder = csize - asize;

    delete_block(bp);

    // No splitting
    if (remainder < MIN_BLK_SIZE) {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
    // Split block -  place in upper address space
    else if (asize > 100){
        PUT(HDRP(bp), PACK(remainder, 0));
        PUT(FTRP(bp), PACK(remainder, 0));

        PUT(HDRP(NEXT_BLKP(bp)), PACK(asize, 1));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(asize, 1));
        coalesce(bp);
        bp = NEXT_BLKP(bp);
    }
    // Split block - place in lower address space
    else {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));

        PUT(HDRP(NEXT_BLKP(bp)), PACK(remainder, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(remainder, 0));
        coalesce(NEXT_BLKP(bp));
    }
    return bp;
}

/*
 * find_fit - Find a fit for a block with asize bytes.
 *            Implements "first-fit" search
 */
static void *find_fit(size_t asize) {

    for (int size_class = get_size_class(asize); size_class < NUM_CLASSES; size_class++) {

        for (void *bp = free_list[size_class]; bp != NULL && GET_ALLOC(HDRP(bp)) == 0; bp = NEXT_FREEP(bp)) {
            if (asize <= (size_t)GET_SIZE(HDRP(bp)))
                return bp;
        }
    }

    return NULL; // No fit
}


/*
* get_size_class - Returns the appropriate size size_class or 
*                    class given a (word-aligned) size.
*/
static inline int get_size_class(size_t asize) {
    int size_class = 0;
    // Powers of two less than 5 (START_SHIFT), {2, 4, 6, 16}, do not make for 
    // valid size classes as the minimum block size is 24 bytes.
    asize >>= START_SHIFT;

    while (size_class < NUM_CLASSES - 1 && asize > 1) {
        asize >>= 1;
        size_class++;
    }

    return size_class;
}


/*
 * insert_block -   Inserts a newly acquired (free) memory (either from coalescing or heap extension)
 *                  into the segregated list.
 * 
 */
static inline void insert_block(void *bp) {

    size_t size = GET_SIZE(HDRP(bp));
    int size_class = get_size_class(size);
    void *current_ptr = free_list[size_class];
    void *insert_ptr = NULL;

    while ((current_ptr != NULL) && (GET_SIZE(HDRP(current_ptr)) < size)) {
        insert_ptr = current_ptr;
        current_ptr = NEXT_FREEP(current_ptr);
    }

    // #1: 1st node
    if (current_ptr == NULL && insert_ptr == NULL) {
        PREV_FREEP(bp) = NULL;
        NEXT_FREEP(bp) = NULL;
        free_list[size_class] = bp;
    }
        // #2: Insert at start of list
    else if (current_ptr != NULL && insert_ptr == NULL) {
        NEXT_FREEP(bp) = free_list[size_class];
        PREV_FREEP(bp) = NULL;
        PREV_FREEP(free_list[size_class]) = bp;
        free_list[size_class] = bp;
    }
        // #3: End of list
    else if (current_ptr == NULL && insert_ptr != NULL) {
        NEXT_FREEP(insert_ptr) = bp;
        NEXT_FREEP(bp) = NULL;
        PREV_FREEP(bp) = insert_ptr;
    }
        // #4: Middle of list
    else {
        NEXT_FREEP(insert_ptr) = bp;
        PREV_FREEP(current_ptr) = bp;
        NEXT_FREEP(bp) = current_ptr;
        PREV_FREEP(bp) = insert_ptr;
    }
}

/*
 * Removes a free block from the segregated list
 */
static void delete_block(void *bp) {

    int size_class = get_size_class(GET_SIZE(HDRP(bp)));

    if (PREV_FREEP(bp) != NULL)
        NEXT_FREEP(PREV_FREEP(bp)) = NEXT_FREEP(bp);
    else
        free_list[size_class] = NEXT_FREEP(bp);

    if (NEXT_FREEP(bp))
        PREV_FREEP(NEXT_FREEP(bp)) = PREV_FREEP(bp);
    NEXT_FREEP(bp) = NULL;
    PREV_FREEP(bp) = NULL;
}
