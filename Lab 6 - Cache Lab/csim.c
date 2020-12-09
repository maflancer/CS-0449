/*
 * csim.c - A cache simulator that can replay traces from Valgrind
 *     and output statistics such as number of hits, misses, and
 *     evictions.  The replacement policy is LRU.
 *
 * Implementation and assumptions:
 *
 *  1. Each load/store can cause at most one cache miss. (I examined the trace,
 *  the largest request I saw was for 8 bytes).
 *
 *  2. Instruction loads (I) are ignored, since we are interested in evaluating
 *  data cache performance.
 *
 *  3. data modify (M) is treated as a load followed by a store to the same
 *  address. Hence, an M operation can result in two cache hits, or a miss and a
 *  hit plus an possible eviction.
 *
 * The function printSummary() is given to print output.
 * Please use this function to print the number of hits, misses and evictions.
 * IMPORTANT: This is crucial for the driver to evaluate your work.
 *
 */

#include <getopt.h>
#include <stdlib.h>
#include <unistd.h>
#include <stdio.h>
#include <assert.h>
#include <math.h>
#include <limits.h>
#include <string.h>
#include <errno.h>

//#define DEBUG_ON
#define ADDRESS_LENGTH 64

/* Type: Memory address */
typedef unsigned long long int mem_addr_t;

/*
 * Data structures to represent the cache we are simulating
 *
 * TODO: Define your own!
 *
 * E.g., Types: cache, cache line, cache set
 * (you can use a counter to implement LRU replacement policy)
 */

typedef struct line {  //struct for a line in the cache
  mem_addr_t tag;
  int lru_count;
  int valid;
} cache_line_t;

typedef cache_line_t *cache_set_t;  //lines make up a set
typedef cache_set_t *cache_t;   //sets make up cache

cache_t cache; //the cache

/* Globals set by command line args */
int verbosity = 0; /* print trace if set */
int s = 0; /* set index bits */
int b = 0; /* block offset bits */
int E = 0; /* associativity */
char* trace_file = NULL;

/* Derived from command line args */
int S; /* number of sets */
int B; /* block size (bytes) */

/* Counters used to record cache statistics */
int miss_count = 0;
int hit_count = 0;
int eviction_count = 0;

/*
 * initCache - Allocate memory (with malloc) for cache data structures (i.e., for each of the sets and lines per set),
 * writing 0's for valid and tag and LRU
 *
 * TODO: Implement
 *
 */
void initCache()
{
  cache = malloc(S * sizeof(cache_set_t)); //allocate space for S(# of sets) * size of a set

  for(int i = 0; i < S; i++) { //loop through each set
    cache[i] = malloc(E * sizeof(cache_line_t)); //allocate space for E(# of lines per set) * size of a line

    for(int j = 0; j < E; j++) { //loop through each line
      cache[i][j].valid = 0;
      cache[i][j].tag = 0;
      cache[i][j].lru_count = 0;
    }
  }
}


/*
 * freeCache - free allocated memory
 *
 * This function deallocates (with free) the cache data structures of each
 * set and line.
 *
 * TODO: Implement
 */
void freeCache()
{
  for(int i = 0; i < S; i ++) {  //free each set
    free(cache[i]);
  }

  free(cache); //free cache
}


/*
 * accessData - Access data at memory address addr
 *   If it is already in cache, increase hit_count
 *   If it is not in cache, bring it in cache, increase miss count.
 *   Also increase eviction_count if a line is evicted.
 *
 * TODO: Implement
 */
void accessData(mem_addr_t addr)
{
  mem_addr_t tag = addr >> (b + s);          //set tag amd set addresses based on b, s, and S
  mem_addr_t set = (addr >> b) & (S - 1);

  int hit = 0; //if an address was a hit(1) or miss(0)

  int MRU, LRU = cache[(int) set][0].lru_count;   //set most recently used and least recently used equal to first entry in the set's lru_count

  for(int i = 0; i < E; i++) { //loop through lines in the set
    if(MRU < cache[(int) set][i].lru_count){      //finds the most recently used line in the set
      MRU = cache[(int) set][i].lru_count;
    }
    if(LRU > cache[(int) set][i].lru_count) { //finds the least recently used line in the set
      LRU = cache[(int) set][i].lru_count;
    }
  }

  for(int i = 0; i < E; i++) { //loop through lines in the set
    if(cache[(int) set][i].tag == tag && cache[(int) set][i].valid){  //if the line's tag matches and the line is valid
      hit_count++; //update hit count
      hit = 1; //signifies a hit
      cache[(int) set][i].lru_count = MRU + 1;//set the line's lru_count to the most recently used + 1
      MRU++;
      LRU++;
      for(int j = 0; j < E; j++) { //loop through lines in the set again
        if(LRU > cache[(int) set][j].lru_count){ //finds the new least recently used
          LRU = cache[(int) set][j].lru_count;
        }
      }
    }
  }

  if(hit == 0) { //if there was a miss
    miss_count++; //update miss count

    int check = 0;
    for(int i = 0; i < E; i++) { //loop through lines in the set
      if(cache[(int) set][i].valid == 0 && check == 0){ //if the line is not valid
        cache[(int) set][i].tag = tag;
        cache[(int) set][i].lru_count = MRU + 1;   //set the tag, lru_count, and valid
        cache[(int) set][i].valid = '1';
        MRU++;
        LRU++;
        hit = 1;
        check = 1;
        for(int j = 0; j < E; j++) { //loop through lines in the set again
          if(LRU > cache[(int) set][j].lru_count){ //finds the new least recently used
            LRU = cache[(int) set][j].lru_count;
          }
        }
      }
    }

    check = 0;
    if(hit == 0){ //if there was a miss and there was no room for the address to be inserted in the cache
      for(int i = 0; i < E; i++) { //loop through lines in the set
        if(cache[(int) set][i].lru_count == LRU && check == 0){ //find the least recently used and insert the new address (eviction)
          cache[(int) set][i].tag = tag;
          cache[(int) set][i].lru_count = MRU + 1;
          MRU++;
          LRU++;
          eviction_count++; //update eviction count
          hit = 1;
          check = 1;
        }
      }
    }
  }
}


/*
 * replayTrace - replays the given trace file against the cache
 *
 * This function:
 * - opens file trace_fn for reading (using fopen)
 * - reads lines (e.g., using fgets) from the file handle (may name `trace_fp` variable)
 * - skips lines not starting with ` S`, ` L` or ` M`
 * - parses the memory address (unsigned long, in hex) and len (unsigned int, in decimal)
 *   from each input line
 * - calls `access_data(address)` for each access to a cache line
 *
 * TODO: Implement
 *
 */
void replayTrace(char* trace_fn)
{
    FILE *trace_fp; //file handle
    char str[2000]; //where the string read from fgets is stored
    mem_addr_t memoryAddress;
    unsigned int len ;

    trace_fp = fopen(trace_fn, "r"); //open the file
    if(trace_fp == NULL) {
      printf("%s\n", "Error opening file"); //check if file is valid
    }

    while(fgets(str, 2000, trace_fp) != NULL) {
      if(str[1] == 'S' || str[1] == 'L' || str[1] == 'M') { //only care about lines starting with 'S', 'L', or 'M'

        sscanf(str+3, "%llx,%u", &memoryAddress, &len); //parses current string into memory address and len

        accessData(memoryAddress);

        if(str[1] == 'M') {  //the data modify operation is treated as a load followed by a store to the same address
          accessData(memoryAddress);
        }
      }
    }

    fclose(trace_fp); //close the file
}

/*
 * printUsage - Print usage info
 */
void printUsage(char* argv[])
{
    printf("Usage: %s [-hv] -s <num> -E <num> -b <num> -t <file>\n", argv[0]);
    printf("Options:\n");
    printf("  -h         Print this help message.\n");
    printf("  -v         Optional verbose flag.\n");
    printf("  -s <num>   Number of set index bits.\n");
    printf("  -E <num>   Number of lines per set.\n");
    printf("  -b <num>   Number of block offset bits.\n");
    printf("  -t <file>  Trace file.\n");
    printf("\nExamples:\n");
    printf("  linux>  %s -s 4 -E 1 -b 4 -t traces/yi.trace\n", argv[0]);
    printf("  linux>  %s -v -s 8 -E 2 -b 4 -t traces/yi.trace\n", argv[0]);
    exit(0);
}

/*
 *
 * !! DO NOT MODIFY !!
 *
 * printSummary - Summarize the cache simulation statistics. Student cache simulators
 *                must call this function in order to be properly autograded.
 */
void printSummary(int hits, int misses, int evictions)
{
    printf("hits:%d misses:%d evictions:%d\n", hits, misses, evictions);
    FILE* output_fp = fopen(".csim_results", "w");
    assert(output_fp);
    fprintf(output_fp, "%d %d %d\n", hits, misses, evictions);
    fclose(output_fp);
}

/*
 * main - Main routine
 */
int main(int argc, char* argv[])
{
    char c;

    while( (c=getopt(argc,argv,"s:E:b:t:vh")) != -1){
        switch(c){
        case 's':
            s = atoi(optarg);
            break;
        case 'E':
            E = atoi(optarg);
            break;
        case 'b':
            b = atoi(optarg);
            break;
        case 't':
            trace_file = optarg;
            break;
        case 'v':
            verbosity = 1;
            break;
        case 'h':
            printUsage(argv);
            exit(0);
        default:
            printUsage(argv);
            exit(1);
        }
    }

    /* Make sure that all required command line args were specified */
    if (s == 0 || E == 0 || b == 0 || trace_file == NULL) {
        printf("%s: Missing required command line argument\n", argv[0]);
        printUsage(argv);
        exit(1);
    }

    /* Compute S, E and B from command line args */
    S = (unsigned int) pow(2, s);
    B = (unsigned int) pow(2, b);

    /* Initialize cache */
    initCache();

#ifdef DEBUG_ON
    printf("DEBUG: S:%u E:%u B:%u trace:%s\n", S, E, B, trace_file);
#endif

    replayTrace(trace_file);

    /* Free allocated memory */
    freeCache();

    /* Output the hit and miss statistics for the autograder */
    printSummary(hit_count, miss_count, eviction_count);

    return 0;
}
