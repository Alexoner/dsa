/* Hash tables (fixed size)
 * 15-122 Principles of Imperative Computation, Fall 2010 
 * Frank Pfenning
 */

#include <stdbool.h>
#include <stdlib.h>
#include "xalloc.h"
#include "contracts.h"
#include "hashtable.h"

/* Interface type definitions */
/* see hashtable.h */

struct list {
  ht_elem data;			/* data != NULL */
  struct list* next;
};
typedef struct list* list;

/* alpha = n/m = num_elems/size */
struct ht {
  int size;			/* m */
  list* A;			/* \length(A) == size */
  ht_key (*elem_key)(ht_elem e); /* extracting keys from elements */
  bool (*key_equal)(ht_key k1, ht_key k2); /* comparing keys */
  int (*key_hash)(ht_key k, int m);	   /* hashing keys */
};

/* chains, implemented as linked lists */

list list_new(ht_elem e, list tail) {
  list lnew = xmalloc(sizeof(struct list));
  lnew->data = e;
  lnew->next = tail;
  return lnew;
}

void list_free(list p, void (*elem_free)(ht_elem e)) {
  while (p != NULL) {
    if (p->data != NULL && elem_free != NULL)
      /* free element, if such a function is supplied */
      (*elem_free)(p->data);
    list tmp = p->next;
    free(p);
    p = tmp;
  }
}

bool is_chain(ht H, list l, int h) {
  while (l != NULL) {
    if (l->data == NULL) return false;
    if (H->key_hash(H->elem_key(l->data), H->size) != h) return false;
    l = l->next;
  }
  return true;
}

bool is_ht(ht H) {
  if (H == NULL) return false;
  if (!(H->size > 0)) return false;
  //@assert H->size == \length(H->A);
  for (int h = 0; h < H->size; h++)
    if (!(is_chain(H, H->A[h], h))) return false;
  return true;
}

/* hash table implementation */

ht ht_new(int init_size,
	  ht_key (*elem_key)(ht_elem e),
	  bool (*key_equal)(ht_key k1, ht_key k2),
	  int (*key_hash)(ht_key k, int m))
{ REQUIRES(init_size > 1);
  list* A = xcalloc(init_size, sizeof(list));
  ht H = xmalloc(sizeof(struct ht));
  H->size = init_size;
  H->A = A;			/* all initialized to NULL; */
  H->elem_key = elem_key;
  H->key_equal = key_equal;
  H->key_hash = key_hash;
  ENSURES(is_ht(H));
  return H;
}

void ht_insert(ht H, ht_elem e)
{ REQUIRES(is_ht(H));
  assert(e != NULL);		/* cannot insert NULL element */
  ht_key k = H->elem_key(e);
  int h = H->key_hash(k, H->size);
  list l = H->A[h];
  while (l != NULL)
    //@loop_invariant is_chain(H, l, h);
    {
      if (H->key_equal(H->elem_key(l->data), k)) {
	l->data = e;		/* modify in place if k already there */
	return;
      }
      l = l->next;
    }
  /* k is not already in the hash table */
  /* insert at the beginning of the chain at A[h] */
  H->A[h] = list_new(e, H->A[h]);
  ENSURES(is_ht(H));
  return;
}

/* ht_search(H, k) returns NULL if key k not present in H */
ht_elem ht_search(ht H, ht_key k)
{
  REQUIRES(is_ht(H));
  int h = H->key_hash(k, H->size);
  list l = H->A[h];
  while (l != NULL)
    //@loop_invariant is_chain(H, l, h);
    {
      if (H->key_equal(H->elem_key(l->data), k))
	return l->data;
      l = l->next;
    }
  return NULL;
}

void ht_free(ht H, void (*elem_free)(ht_elem e))
{ REQUIRES(is_ht(H));
  for (int i = 0; i < H->size; i++) {
    list l = H->A[i];
    if (l != NULL) list_free(l, elem_free);
  }
  free(H->A);
  free(H);
}
