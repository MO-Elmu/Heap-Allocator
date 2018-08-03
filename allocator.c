/*
 * File: allocator.c
 * Author: Mohamed Elmuhtadi
 * -------------------------                                                                            
 * This allocator is implemented using segregated fits with explicit singly linked lists.                                                     
 *                                                                                                                                            
 * Each memory block has an 8-byte header (no footer). The header stores the                                                                  
 * (a) size of the allocated block                                                                                                            
 * (b) status of allocation (free or allocated)                                                                                               
 * (c) index which points to the free list in the segregated free lists array the block belongs to.                                           
 *                                                                                                                                            
 * Free blocks are stored in one of many size segregated linked lists. There are 28 linked list (0 to 27)                                     
 * each list contains blocks with sizes between 2^n to 2^(n+1)-1, the last linked list is reserved for myrealloc.                             
 * we start from size class 2^4 - (2^5)-1, since the minimum block size can be allocated is 16 bytes (including header).                      
 *                                                                                                                                            
 * To allocate a block, we determine the requested size class and do a first-fit search of the appropriate free list for                      
 * a block that fits. if we find one, then we split it and based on the number of HITS for this size class we either leave                                                                                                
 * the remaining fragment in the same free list or insert it into the appropriate free list that match its new size. If we can't              
 * find a block that fits, then we search the free list for the next larger size class (Unless the number of HITS for                         
 * this size class exceedes the HIT_SENSOR then we break out of the loop and ask the operating system for more memory).                       
 * This is repeated untill a block is found. If none was found in all free lists, we request additional heap memory from the Operating System.
 * Allocate the block and place the remainder in the appropriate size class. To free a block we read its index (or size) and place            
 * it on the matching free list.                                                                                                              
 *                                                                                                                                          
 * Reallocation is handeled seperately, it has its own free list in index 27 (last one) in the segregated free list array.                    
 * If reallocation is requested, first we check if the originally allocated size can still provide the requested new size                     
 * if so we just return the same pointer if not we request memory from the OS and move everything to the realloc free list                    
 * in index 27 and process everthing in there for any future reallocing. 
 */                                                                     
 
                                                                            
#include <stdlib.h>                                                            
#include <string.h>                                                            
#include "allocator.h"                                                         
#include "segment.h"                                                           
#include "limits.h"                                                            
#include <stdio.h>                                                             
                                                                               
// Heap blocks are required to be aligned to 8-byte boundary                   
#define ALIGNMENT 8                                                            
#define MIN_BLK_SZ 16
#define EXP 4            //The exponent of the minimum block size can be allocated (base 2) 2^4 = 16 = MIN_BLK_SZ
#define TRUE 1           //This is easier to read and less complex than enum (personal preference)
#define FALSE 0
#define REALLOC_INDEX 27 // The index (in segregated free lists array) of the free list dedicated for reallocation 
#define SZ_CLASSES  28  // Number of segregated size classes (free lists)



/* if a size class number of HITS (requests) exceeds this sensor all future requests for this size class go through different
 * code path. Which is 
 * 1- Requests for a block of memory are only searched within its appropriate size class free list, No looping through the entire segregated free lists array.
 * 2- If not found, OS is asked for more memory for this specific free list.
 * 3- Splitting is done in place meaning the remaining fragment of memory is place in the same free list not in its appropriate size class free list.
 */

#define HIT_SENSOR 150000   // This can be increased and decreased to notice its effect on Utilization and Throughput, less = more sensitive


// struct represents memory block header
typedef struct {
   unsigned int payloadsz;   // This indicates allocated (not requested) payload size
   unsigned short alloc;     // if alloc=0 means block is free, alloc=1 block is allocated
   unsigned short index;     // The index of the free list in the segregated free_lists array this block belongs to.
} headerT;


void *free_lists[SZ_CLASSES];  // 28 segregated free lists representing 28 size classes starting from (2^4 - (2^5 -1)) to (2^30 - (2^31 -1)

/* The values in this array maps the HIT count for the free lists stored in free_lists (implicit index matching) */

unsigned int hit_counter[SZ_CLASSES];  //counts the number of allocation hits for each segregated free list class, This array size should match free_lists (implicit mapping)


// global variable to store a pointer to the start of the heap
void *mem_heap = NULL;      /* points to first byte of heap */


// Very efficient bitwise round of sz up to nearest multiple of mult
// does this by adding mult-1 to sz, then masking off the
// the bottom bits to compute least multiple of mult that is
// greater/equal than sz, this value is returned
// NOTE: mult has to be power of 2 for the bitwise trick to work!

static inline size_t roundup(size_t sz, size_t mult)
{
    return (sz + mult-1) & ~(mult-1);
}


// Given a pointer to start of payload, simply back up
// to access its block header
static inline headerT *hdr_for_payload(void *payload)
{
    return (headerT *)((char *)payload - sizeof(headerT));
}


// Given a pointer to block header, advance past
// header to access start of payload
static inline void *payload_for_hdr(headerT *header)
{
    return (char *)header + sizeof(headerT);
}

//Helper function Given a pointer to block header,get a block payload size
static inline size_t get_size (headerT *header)
{
    return header->payloadsz;
}

//Helper function to set a block header to a specific payload size
static inline void set_size (headerT *header, size_t size)
{
    header->payloadsz = size;
}

//Helper function to set index of a block header
static inline void set_free_lists_index (headerT *header, unsigned short index)
{
    header->index = index;
}

//Helper function to set index of a block header
static inline unsigned short get_free_lists_index (headerT *header)
{
    return header->index;
}

// Helper function to set a block header to signal free
static inline void set_to_free (headerT *header)
{
    header->alloc = 0;      // set the block with header "header" to free
}

// Helper function to set a block header to signal allocated
static inline void set_to_alloc (headerT *header)
{
    header->alloc = 1;      // set the block with header "header" to allocated
}

// Given block header pointer and a size (size could be different from existing payload size), compute address of the next block header
static inline void *next_block_ptr (headerT *header, size_t size)
{
    return (void *)((char *)header + sizeof(headerT) + size);
}

// Helper function to Map requested memory size to the matching size class range (2^n - (2^(n+1) -1)), return the index of the matching free list.
static inline unsigned short free_list_indx (size_t size) {

    int exp = 0;
    while (size != 0){
          size >>= 0x1;
          exp++;
    }
    /* -4 since the min block size is 16 = 2^4 so the first class in the array free_lists[0] is (16-31 bytes)
        any request below 16bytes will still be given 16 bytes and belong to free_lists[0] */

    return (exp - EXP - 1) ;  //calculate the index in the free_lists array that points to the correct size class
}


/*Function: split_blk
 *Helper Function for splitting a block routine,
 *it returns the a new free block as a result of the split
 *it also  adjusts the header of the old original block
*/

static inline void split_blk (headerT *original_blk, unsigned short free_lists_index, size_t requested_sz, size_t size_diff) {

    /* create and intialize the new free block resulted from the split, set payloadsz, alloc, free_lists index */
    void *new_block_ptr = next_block_ptr(original_blk, requested_sz);
    set_size (new_block_ptr, (size_diff - sizeof(headerT)));  //set payload size
    set_to_free (new_block_ptr);                              // mark it as free
    set_free_lists_index(new_block_ptr, free_lists_index);
    
    memcpy(payload_for_hdr(new_block_ptr), &free_lists[free_lists_index], sizeof(void *));  // keep the linked list intact
    
    free_lists[free_lists_index] = new_block_ptr;     //Insert it to the begining of that list

    /* Adjust the header (payloadsz & alloc) of the original block */
    set_size (original_blk, requested_sz);   // set payload size of the original block to the new requested size
    set_to_alloc (original_blk);             // mark it as allocated

}

/* The responsibility of the myinit function is to configure a new
 * empty heap. Typically this function will initialize the
 * segment (you decide the initial number pages to set aside, can be
 * zero if you intend to defer until first request) and set up the
 * global variables for the empty, ready-to-go state. The myinit
 * function is called once at program start, before any allocation
 * requests are made. It may also be called later to wipe out the current
 * heap contents and start over fresh. This "reset" option is specifically
 * needed by the test harness to run a sequence of scripts, one after another,
 * without restarting program from scratch.
 */
 
bool myinit()
{
    mem_heap = init_heap_segment(0); // reset heap segment

    /* intialize all free lists and ht_counters. set to NULL & Zero */
    for (int i=0; i<SZ_CLASSES; i++) {
         free_lists[i] = NULL;
         hit_counter[i] = 0;
        // OS_hit_counter[i] = 0;
    }
    /* So this to preserve isolation and special treatment (code path) for Realloc */
    hit_counter[REALLOC_INDEX] = HIT_SENSOR ;   //Force myrealloc to always follow the code path of {# HITS (requests) > HIT_SENSOR}
    return true;
}
/* Function: find_fit
 * ------------------
 * Helper function to look for a size request fit in the free linked list, return NULL if NO fit
 * It also perform the splitting process if bool split = TRUE, Splitting has to different code paths
 * in this function depending on the value of the HIT_SENSOR and number of HITs (requests) for specific
 * size class. It loops through individual free list from segregated free_lists.
 */

static  void *find_fit(size_t size, unsigned short free_lists_index, bool split)
{
    /* First-fit search */
    void *hdr_ptr = NULL;       //pointer to the found block fit to satisfy allocation request, NULL if no fit found
    void *prev_hdr_ptr = NULL;  //pointer to keep track of previous free block and update it to point to the correct next node in linked list,
    size_t size_diff = 0;       //parameter to measure difference between available and requested memory to decide if split is needed


    /* loop through the free linked list to find a fit, return a pointer to the found block otherwise return NULL */
    for (hdr_ptr = free_lists[free_lists_index]; hdr_ptr != NULL ; prev_hdr_ptr = hdr_ptr,  hdr_ptr = *(void **)payload_for_hdr(hdr_ptr)){

        if (size <= get_size(hdr_ptr)){      //check if requested size is less than or equal a free block

            /* Split the free space if the size difference after splitting (the remainder) is greater than or equal the minimum block size 16 bytes */
            if((split) && ((size_diff = (get_size(hdr_ptr) - size)) >= MIN_BLK_SZ)){

                 /* Handle the case if the first block in the free linked list is a fit */
                 if (prev_hdr_ptr == NULL)
                     // free_lists[free_lists_index] = *(void **)payload_for_hdr(hdr_ptr);
                     memcpy(&free_lists[free_lists_index], payload_for_hdr(hdr_ptr), sizeof(void *));
                 /* Update the previous node in the linked list */
                 else
                      memcpy(payload_for_hdr(prev_hdr_ptr), payload_for_hdr(hdr_ptr), sizeof(void *));

                 if (hit_counter[free_lists_index] >= HIT_SENSOR){
                      /* Split, Match the remainder free block with the same free list, Insert it to the begining of that list */
                      split_blk (hdr_ptr, free_lists_index, size, size_diff);
                 }
                 else {
                      /* Match the remainder free block with the right free list and insert it to the begining of that list */
                      unsigned short list_indx = free_list_indx(size_diff);

                      /* create a new free block as a result of the split, and a insert it into its appropriate free list based on its size */
                      split_blk (hdr_ptr, list_indx, size, size_diff);
                 }

                 return hdr_ptr;
            }
            else {
                set_to_alloc (hdr_ptr);           //mark size as allocated
                set_size(hdr_ptr, get_size(hdr_ptr)); //give the request the whole memory, since the remainder is not usable

                /* Handle the case if the first block in the free linked list is a fit */
                if (prev_hdr_ptr == NULL)
                     //free_lists[free_lists_index] = *(void **)payload_for_hdr(hdr_ptr);
                     memcpy(&free_lists[free_lists_index], payload_for_hdr(hdr_ptr), sizeof(void *));
                else
                     memcpy(payload_for_hdr(prev_hdr_ptr), payload_for_hdr(hdr_ptr), sizeof(void *));

                return hdr_ptr;
            }

        }

    }

    return NULL; /* No fit */

}

// malloc a block by rounding up size to number of pages, extending heap
// segment and using most recently added page(s) for this block. This
// means each block gets its own page -- how generous! :-)

void *mymalloc(size_t requestedsz)
{
    size_t adjustedsz;  /* Adjusted block size to comply with Alignment and min block size requirement */
    size_t extendsz;    /* # of pages to extend heap if no fit */
    void *bp;

    /* ignore spurious requests */
    if (requestedsz == 0 || requestedsz > INT_MAX) return NULL;

    /* Adjust block size */
    adjustedsz = roundup(requestedsz + sizeof(headerT), ALIGNMENT);

    unsigned short index = free_list_indx(adjustedsz);   //calculate the index in the free_lists array that points to the correct size class
    hit_counter[index]++;                //increase the hit count for this specific free list class by one
    /* Search the free list for a first fit */
    for (int i=0; i<REALLOC_INDEX; i++){   //till 26 index, last index is reserved for realloc use only
        if ((bp = find_fit(adjustedsz - sizeof(headerT), i, TRUE)) != NULL){
             set_free_lists_index(bp, i);
             return payload_for_hdr(bp);
        }
        if (hit_counter[index] >= HIT_SENSOR) break;
    }

    /* No fit found. Get more memory and place the block */
    extendsz = roundup(adjustedsz, PAGE_SIZE)/PAGE_SIZE;
    size_t size_diff = 0;
    size_t extended_sz = extendsz*PAGE_SIZE;
    if ((bp = extend_heap_segment(extendsz)) == NULL) return NULL;       //optimize here if before it is free coelse
    set_free_lists_index(bp,index);


    /* Split the free space if the size difference after splitting (the remainder) is greater than or equal the minimum block size 16 bytes */
    if((size_diff = (extended_sz - adjustedsz)) >= MIN_BLK_SZ){

          if (hit_counter[index] >= HIT_SENSOR){
               //hit_counter[index]--;
               
               /* Split, Match the remainder free block with the same free list, Insert it to the begining of that list */
               split_blk (bp, index, (adjustedsz-sizeof(headerT)), size_diff);
          }
          else {
               /* Match the remainder free block with the right free list and insert it to the begining of that list */
               unsigned short list_indx = free_list_indx(size_diff);

               /*&free_list to keep linked list intact and insert the new free block at the begining of the list */
               split_blk (bp, list_indx, (adjustedsz-sizeof(headerT)), size_diff);
          }
    }
    else {
         set_size(bp, (extended_sz - sizeof(headerT)));   //No split give away the whole memory block
         set_to_alloc(bp);
    }
    return payload_for_hdr(bp);
}


// free does nothing.  fast!... but lame :(
void myfree(void *ptr)
{
    if (ptr){
       /* insert freed block to the front of the free list, copy pointer to next from free_list into payload space in freed block */
       void *hdr_ptr = hdr_for_payload(ptr);  //pointer to the header of the freed block
       unsigned short index = get_free_lists_index(hdr_ptr);
       hit_counter[index]--;
       memcpy (ptr, &free_lists[index], sizeof(void *));
       set_to_free(hdr_ptr);
       free_lists[index] = hdr_ptr;
    }
}


// realloc built on malloc/memcpy/free is easy to write.
// This code will work ok on ordinary cases, but needs attention
// to robustness. Realloc efficiency can be improved by
// implementing a standalone realloc as opposed to
// delegating to malloc/free.

void *myrealloc(void *oldptr, size_t newsz)
{
    hit_counter[REALLOC_INDEX]++;                //increase the hit count for this specific free list class by one
    void *newptr;
    void *bp;
    if (oldptr) {
        size_t oldsz = get_size(hdr_for_payload(oldptr));
        if (newsz == 0 || newsz > INT_MAX) return NULL;
        if (newsz <= oldsz)
             return oldptr;

        size_t adjustedsz;  /* Adjusted block size to comply with Alignment and min block size requirement */
        size_t extendsz;    /* Amount to extend heap if no fit */

        /* Adjust block size give it double of adjusted size since its realloc to account for future realloc in the same block*/
        adjustedsz =  (roundup(newsz + sizeof(headerT), ALIGNMENT)) << 1;

        if ((bp = find_fit(adjustedsz - sizeof(headerT), REALLOC_INDEX, TRUE)) != NULL) {
             set_free_lists_index(bp, REALLOC_INDEX);
             newptr = payload_for_hdr(bp);
             memcpy(newptr, oldptr, oldsz);
             myfree(oldptr);
             //set it to alloc, and set new payload size
             return newptr;
        }

         /* No fit found. Get more memory and place the block */
         extendsz = roundup((adjustedsz), PAGE_SIZE)/PAGE_SIZE;
         size_t extended_sz = extendsz*PAGE_SIZE;
         if ((bp = extend_heap_segment(extendsz)) == NULL) return NULL;
         set_free_lists_index(bp, REALLOC_INDEX);
         size_t size_diff = extended_sz - adjustedsz;
         newptr = payload_for_hdr(bp);

          if(size_diff  >= MIN_BLK_SZ){
          	
             /* Split, Match the remainder free block with the same free list, Insert it to the begining of that list */
             split_blk (bp, REALLOC_INDEX, (adjustedsz-sizeof(headerT)), size_diff);
             
             memcpy(newptr, oldptr, oldsz);
             myfree(oldptr);
             return newptr;

          }
         memcpy(newptr, oldptr, oldsz);
         myfree(oldptr);
         set_size(bp, (extended_sz - sizeof(headerT)));   //No split give away the whole memory block
         set_to_alloc(bp);
    }

    /*void *newptr = mymalloc(newsz);
    memcpy(newptr, oldptr, oldsz < newsz ? oldsz: newsz);
    myfree(oldptr);
    return newptr;*/
     else
         newptr = mymalloc(newsz);

    return newptr;

}


// validate_heap is your debugging routine to detect/report
// on problems/inconsistency within your heap data structures
bool validate_heap()
{
    return true;
}

