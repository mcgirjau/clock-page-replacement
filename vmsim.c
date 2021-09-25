// =================================================================================================================================
/**
 * vmsim.c
 *
 * Allocate space that is then virtually mapped, page by page, to a simulated underlying space.  Maintain page tables and follow
 * their mappings with a simulated MMU.
 **/
// =================================================================================================================================



// =================================================================================================================================
// INCLUDES

#include <assert.h>
#include <errno.h>
#include <stdbool.h>
#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <sys/mman.h>
#include "bs.h"
#include "mmu.h"
#include "vmsim.h"
// =================================================================================================================================



// =================================================================================================================================
// CONSTANTS AND MACRO FUNCTIONS

#define KB(n)      (n * 1024)
#define MB(n)      (KB(n) * 1024)
#define GB(n)      (MB(n) * 1024)
 
#define DEFAULT_REAL_MEMORY_SIZE   (MB(4) + KB(16)) //WAS MB(5)
#define PAGESIZE                   KB(4)
#define PT_AREA_SIZE               (MB(4) + KB(4))

#define OFFSET_MASK           (PAGESIZE - 1)
#define PAGE_NUMBER_MASK      (~OFFSET_MASK)
#define GET_UPPER_INDEX(addr) ((addr >> 22) & 0x3ff)
#define GET_LOWER_INDEX(addr) ((addr >> 12) & 0x3ff)
#define GET_OFFSET(addr)      (addr & OFFSET_MASK)
#define GET_PAGE_ADDR(addr)   (addr & PAGE_NUMBER_MASK)
#define IS_ALIGNED(addr)      ((addr & OFFSET_MASK) == 0)

#define IS_RESIDENT(pte)      (pte & PTE_RESIDENT_BIT)
#define IS_REFERENCED(pte)    (pte & PTE_REFERENCED_BIT)
#define IS_DIRTY(pte)         (pte & PTE_DIRTY_BIT)
#define SET_RESIDENT(pte)     (pte |= PTE_RESIDENT_BIT)
#define CLEAR_RESIDENT(pte)   (pte &= ~PTE_RESIDENT_BIT)
#define CLEAR_REFERENCED(pte) (pte &= ~PTE_REFERENCED_BIT)
#define CLEAR_DIRTY(pte)      (pte &= ~PTE_DIRTY_BIT)

// The boundaries and size of the real memory region.
static void*        real_base       = NULL;
static void*        real_limit      = NULL;
static uint64_t     real_size       = DEFAULT_REAL_MEMORY_SIZE;

// Where to find the next page of real memory for page table blocks.
static vmsim_addr_t pt_free_addr    = PAGESIZE;

// Where to find the next page of real memory for backing simulated pages.
static vmsim_addr_t real_free_addr  = PT_AREA_SIZE;

// The base real address of the upper page table.
static vmsim_addr_t upper_pt        = 0;

// Used by the heap allocator, the address of the next free simulated address.
static vmsim_addr_t sim_free_addr   = 0;

// The next available block number on the backing store.
static int next_block_number 	    = 1;

// The list of page entries.
static pt_entry_t** entries         = NULL;

// The number of page entries available.
static uint64_t num_entries         = (DEFAULT_REAL_MEMORY_SIZE - PT_AREA_SIZE) / PAGESIZE;

// The current page number that we're pointing at (for the Clock Algorithm to go around).
static uint64_t current_page_number = 0;

// Function declarations for Clock Algorithm and page swapping utilities
pt_entry_t*  find_lru      ();
vmsim_addr_t from_mm_to_bs (pt_entry_t* entry_ptr);
void         from_bs_to_mm (vmsim_addr_t entry_address, vmsim_addr_t real_address);
void         swap_pages    (vmsim_addr_t bs_page, pt_entry_t* mm_page);
// =================================================================================================================================



// =================================================================================================================================
/**
 * Allocate a page of real memory space for a page table block.  Taken from a region of real memory reserved for this purpose.
 *
 * \return The _real_ base address of a page of memory for a page table block.
 */
vmsim_addr_t allocate_pt () {

  vmsim_addr_t new_pt_addr = pt_free_addr;
  pt_free_addr += PAGESIZE;
  assert(IS_ALIGNED(new_pt_addr));
  assert(pt_free_addr <= PT_AREA_SIZE);
  void* new_pt_ptr = (void*)(real_base + new_pt_addr);
  memset(new_pt_ptr, 0, PAGESIZE);
  
  return new_pt_addr;
  
} // allocate_pt ()
// =================================================================================================================================



// =================================================================================================================================
/**
 * Allocate a page of real memory space for backing a simulated page.  Taken from the general pool of real memory.
 *
 * \return The _real_ base address of a page of memory.
 */
vmsim_addr_t allocate_real_page () {

  vmsim_addr_t new_real_addr = real_free_addr;
  real_free_addr += PAGESIZE;
  assert(IS_ALIGNED(new_real_addr));

  /** Are we out of main memory space? If so, we have to swap some pages. */
  if (real_free_addr > real_size) { 

    /** Find the least-recently used entry. */
    pt_entry_t* entry = find_lru();

    /** Move the contents of that entry to the backing store, and get the
     *  address of the page we just freed. */
    vmsim_addr_t address = from_mm_to_bs(entry);

    /** Return the newly-freed page address. */
    return address;
  }
    
  void* new_real_ptr = (void*) (real_base + new_real_addr);
  memset(new_real_ptr, 0, PAGESIZE);

  return new_real_addr;
  
} // allocate_real_page ()
// =================================================================================================================================



// =================================================================================================================================
void vmsim_init () {

  // Only initialize if it hasn't already happened.
  if (real_base == NULL) {

    // Determine the real memory size, preferrably by environment variable, otherwise use the default.
    char* real_size_envvar = getenv("VMSIM_REAL_MEM_SIZE");
    if (real_size_envvar != NULL) {
      errno = 0;
      real_size = strtoul(real_size_envvar, NULL, 10);
      assert(errno == 0);
    }

    // Map the real storage space.
    real_base = mmap(NULL, real_size, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    assert(real_base != NULL);
    real_limit = (void*)((intptr_t)real_base + real_size);
    upper_pt = allocate_pt();

    // Initialize the simualted space allocator.  Leave page 0 unused, start at page 1.
    sim_free_addr = PAGESIZE;

    // Initialize the supporting components.
    mmu_init(upper_pt);
    bs_init();

    // Initialize the array to hold lower page table entries.
    num_entries = (real_size - PT_AREA_SIZE) / PAGESIZE;
    entries = malloc(sizeof(vmsim_addr_t) * num_entries);
    
  }
  
} // vmsim_init ()
// =================================================================================================================================



// =================================================================================================================================
/**
 * Map a _simulated_ address to a _real_ one, ensuring first that the page table and real spaces are initialized.
 *
 * \param  sim_addr        The _simulated_ address to translate.
 * \param  write_operation Whether the memory access is to _read_ (`false`) or to _write_ (`true`).
 * \return the translated _real_ address.
 */ 
vmsim_addr_t vmsim_map (vmsim_addr_t sim_addr, bool write_operation) {

  vmsim_init();

  assert(real_base != NULL);
  vmsim_addr_t real_addr = mmu_translate(sim_addr, write_operation);
  return real_addr;
  
} // vmsim_map ()
// =================================================================================================================================



// =================================================================================================================================
/**
 * Called when the translation of a _simulated_ address fails.  When this function is done, a _real_ page will back the _simulated_
 * one that contains the given address, with the page tables appropriately updated.
 *
 * \param sim_addr The _simulated_ address for which address translation failed.
 */
void vmsim_map_fault (vmsim_addr_t sim_addr) {

  assert(upper_pt != 0);

  // Grab the upper table's entry.
  vmsim_addr_t upper_index    = GET_UPPER_INDEX(sim_addr);
  vmsim_addr_t upper_pte_addr = upper_pt + (upper_index * sizeof(pt_entry_t));
  pt_entry_t   upper_pte;
  vmsim_read_real(&upper_pte, upper_pte_addr, sizeof(upper_pte));

  // If the lower table doesn't exist, create it and update the upper table.
  if (upper_pte == 0) {

    upper_pte = allocate_pt();
    assert(upper_pte != 0);
    vmsim_write_real(&upper_pte, upper_pte_addr, sizeof(upper_pte));
    
  }

  // Grab the lower table's entry.
  vmsim_addr_t lower_pt       = GET_PAGE_ADDR(upper_pte);
  vmsim_addr_t lower_index    = GET_LOWER_INDEX(sim_addr);
  vmsim_addr_t lower_pte_addr = lower_pt + (lower_index * sizeof(pt_entry_t));
  pt_entry_t   lower_pte;
  vmsim_read_real(&lower_pte, lower_pte_addr, sizeof(lower_pte));

  // If there is no mapped page, create it and update the lower table.
  if (lower_pte == 0) {

    lower_pte = allocate_real_page();
    vmsim_addr_t real_addr = lower_pte;
    SET_RESIDENT(lower_pte);
    vmsim_write_real(&lower_pte, lower_pte_addr, sizeof(lower_pte));
    
    // Add the new page to the list of main memory page entries.
    uint64_t page_number = (real_addr - PT_AREA_SIZE) / PAGESIZE;
    entries[page_number] = (pt_entry_t*) (lower_pte_addr + real_base);

  }  

  // Is the page resident? If not, we must swap it in with the least-recently
  // used page.
  if (!IS_RESIDENT(lower_pte)) {

    pt_entry_t* lru_page = find_lru();
    swap_pages(lower_pte_addr, lru_page);

  }
    
  
} // vmsim_map_fault ()
// =================================================================================================================================



// =================================================================================================================================
void vmsim_read_real (void* buffer, vmsim_addr_t real_addr, size_t size) {

  // Get a pointer into the real space and check the bounds.
  void* ptr = real_base + real_addr;
  void* end = (void*) ((intptr_t) ptr + size);
  assert(end <= real_limit);

  // Copy the requested bytes from the real space.
  memcpy(buffer, ptr, size);
  
} // vmsim_read_real ()
// =================================================================================================================================



// =================================================================================================================================
void vmsim_write_real (void* buffer, vmsim_addr_t real_addr, size_t size) {

  // Get a pointer into the real space and check the bounds.
  void* ptr = real_base + real_addr;
  void* end = (void*) ((intptr_t) ptr + size);
  assert(end <= real_limit);

  // Copy the requested bytes into the real space.
  memcpy(ptr, buffer, size);
  
} // vmsim_write_real ()
// =================================================================================================================================



// =================================================================================================================================
void vmsim_read (void* buffer, vmsim_addr_t addr, size_t size) {

  vmsim_addr_t real_addr = vmsim_map(addr, false);
  vmsim_read_real(buffer, real_addr, size);

} // vmsim_read ()
// =================================================================================================================================



// =================================================================================================================================
void vmsim_write (void* buffer, vmsim_addr_t addr, size_t size) {

  vmsim_addr_t real_addr = vmsim_map(addr, true);
  vmsim_write_real(buffer, real_addr, size);

} // vmsim_write ()
// =================================================================================================================================



// =================================================================================================================================
vmsim_addr_t vmsim_alloc (size_t size) {

  vmsim_init();

  // Pointer-bumping allocator with no reclamation.
  vmsim_addr_t addr = sim_free_addr;
  sim_free_addr += size;
  return addr;
  
} // vmsim_alloc ()
// =================================================================================================================================



// =================================================================================================================================
void vmsim_free (vmsim_addr_t ptr) {

  // No reclamation, so nothing to do.

} // vmsim_free ()
// =================================================================================================================================



// =================================================================================================================================
pt_entry_t* find_lru () {

  // Start from the page at which our "clock hand" is currently pointing.
  pt_entry_t entry = *entries[current_page_number];

  // Keep going around the clock until we find a non-referenced page.
  while IS_REFERENCED(entry) {
      
      // The current page is referenced, so clear it in advance.
      pt_entry_t cleared_entry = CLEAR_REFERENCED(entry);

      // Find the address of the current slot, to write the cleared entry into it.
      vmsim_addr_t destination_address = (vmsim_addr_t) ((void*) entries[current_page_number] - real_base);
      
      // Write the cleared page back into the current slot.
      vmsim_write_real(&cleared_entry, destination_address, sizeof(pt_entry_t));

      // Move on to the next entry.
      current_page_number = (current_page_number + 1) % num_entries;
      entry = *entries[current_page_number];

  }
  
  // Return the first non-referenced page we find.
  return entries[current_page_number];

} // find_lru ()
// =================================================================================================================================



// =================================================================================================================================
void swap_pages (vmsim_addr_t bs_page, pt_entry_t* mm_page) {

  // Move the main memory page to the backing store, returning its free slot address.
  vmsim_addr_t freed_slot = from_mm_to_bs(mm_page);

  // Move the backing store page into the free slot whose address we just got.
  from_bs_to_mm(bs_page, freed_slot);

} // swap_pages ()
// =================================================================================================================================



// =================================================================================================================================
vmsim_addr_t from_mm_to_bs (pt_entry_t* entry_ptr) {

  // Get the lower page table entry.
  pt_entry_t entry = *entry_ptr;

  // Get the address of the page slot whose contents we are swapping from main
  // memory into the backing store.
  vmsim_addr_t free_slot_address = GET_PAGE_ADDR(entry);

  // Write the free slot address into the next available block of the backing
  // store, ensure we account for the used space, and mark the fact that 
  // the entry we just moved isn't resident in main memory anymore.
  bs_write(free_slot_address, next_block_number);
  entry = (entry & 0x3ff) | (next_block_number << 10);
  next_block_number = next_block_number + 1;
  CLEAR_RESIDENT(entry);

  // Clean up pointers.
  void* free_slot_ptr = (void*) (real_base + free_slot_address);
  memset(free_slot_ptr, 0, PAGESIZE);

  // Finally, copy the entry into the destination address.
  vmsim_addr_t destination_address = (vmsim_addr_t) ((void*) entry_ptr - real_base);
  vmsim_write_real(&entry, destination_address, sizeof(pt_entry_t));

  // Return the address of the newly-freed slot.
  return free_slot_address;

} // from_mm_to_bs ()
// =================================================================================================================================



// =================================================================================================================================
void from_bs_to_mm (vmsim_addr_t entry_address, vmsim_addr_t real_address) {

  // Read in the entry from the given lower page table entry address.
  pt_entry_t entry;
  vmsim_read_real(&entry, entry_address, sizeof(pt_entry_t));

  // Find the corresponding block in the backing store.
  int block_number = (entry & 0xfffc00) >> 10;
  bs_read(real_address, block_number);
  
  // The entry can now be considered to be resident in main memory.
  entry = (entry & 0x3ff) | real_address;
  SET_RESIDENT(entry);
  vmsim_write_real(&entry, entry_address, sizeof(pt_entry_t));

  // Add the entry to our list of main memory entries.
  uint64_t page_number = (real_address - PT_AREA_SIZE) / PAGESIZE;
  entries[page_number] = (pt_entry_t*) (real_base + entry_address);

} // from_bs_to_mm ()
// =================================================================================================================================

