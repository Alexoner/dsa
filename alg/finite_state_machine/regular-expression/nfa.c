/*
 * Regular expression implementation.
 * Supports only "( | ) . * + ?".  No escapes.
 * Compiles to NFA and then simulates NFA
 * using Thompson's algorithm.
 *
 * See also http://swtch.com/~rsc/regexp/ and
 * Thompson, Ken.  Regular Expression Search Algorithm,
 * Communications of the ACM 11(6) (June 1968), pp. 419-422.
 *
 * Copyright (c) 2007 Russ Cox.
 * Can be distributed under the MIT license, see bottom of file.
 *
 * INFIX to POSTFIX.
 * Stack to build Finite State Machine Graph.
 * NFA simulation.
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <string.h>
#include <assert.h>
#include <unistd.h>

#define CATENATE_SYMBOL  '\xFF'

#pragma mark - convert regular expression to NFA

/*
 * Convert infix regexp re to postfix notation.
 * Insert . as explicit concatenation operator.
 * Cheesy parser, return static buffer.
 *
 * Because we have to insert explicit CONCATENATION operator into POSTFIX
 * from implicit INFIX expression, so we have to maintain a variable to store
 * how many ATOMIC parts there are before.
 *
 * 1) literal characters: just PUSH into the postfix string and append
 *	CONCATENATION, increase the number of atomic parts
 * 2) *, ?, +: just PUSH these post operators into the postfix string
 * 3) (: PUSH into the STACK information, could be recursive, then do everyting
 *	other than '()'
 * 4) ): append CONCATENATION, ALTERNATION, POP out the STACK, increase the
 *	number of atomic parts
 * 5) |: weakest operator, should append when a ')' has come or at the end of
 *	the expression.
 */
char*
re2post(char *re)
{
	int nalt, natom;
	static char buf[8000];
	char *dst;
	// parenthesis states STACK, serving as a STACK FRAME in the corresponding
	// recursive procedure
	struct {
		int nalt;
		int natom;
	} paren[100], *p;

	p = paren;
	dst = buf;
	nalt = 0;   // number of alternation
	natom = 0;  // number of atomic parts
	if(strlen(re) >= sizeof buf/2)
		return NULL;
	for(char *pre = re; *pre; pre++){
		switch(*pre){
		case '(':
			if(natom > 1){
				--natom;
				*dst++ = CATENATE_SYMBOL;
			}
			// maximum regular expression length
			if(p >= paren+100)
				return NULL;
			p->nalt = nalt;
			p->natom = natom; // no more than 1, <2
			// PUSH STACK
			p++;
			nalt = 0;

			natom = 0;
			break;
		case ')':
			if(p == paren)
				return NULL;
			if(natom == 0)
				return NULL;
			while(--natom > 0)
				*dst++ = CATENATE_SYMBOL;
			for(; nalt > 0; nalt--)
				*dst++ = '|';
			// POP STACK
			--p;
			nalt = p->nalt;
			natom = p->natom; // no more than 1, <2
			// XXX: the parenthesis subpart will be treated as an atom
			natom++;
			break;
		case '|':
			if(natom == 0)
				return NULL;
			while(--natom > 0)
				*dst++ = CATENATE_SYMBOL;
			nalt++;
			break;
		case '*':
		case '+':
		case '?':
			// just append POSTFIX operator
			if(natom == 0)
				return NULL;
			*dst++ = *pre;
			break;
		default: // ATOMIC literal character
			//maybe insert CONCATENATION
			if(natom > 1){
				--natom;
				*dst++ = CATENATE_SYMBOL;
			}
			*dst++ = *pre;
			natom++;
			break;
		}
	}
	if(p != paren)
		return NULL;
	while(--natom > 0)
		*dst++ = CATENATE_SYMBOL;
	for(; nalt > 0; nalt--)
		*dst++ = '|';
	*dst = 0;
	fprintf(stdout, "re2post: %s => %s\n", re, buf);
	fflush(stdout);
	return buf;
}

#pragma mark - REPRESENTATION and CONSTRUCTION of NFA

/*
 * Represents an NFA state plus zero or one or two arrows exiting.
 * if c == Match, no arrows out; matching state.
 * If c == Split, unlabeled arrows to out and out1 (if != NULL).
 * If c < 256, labeled arrow with character c to out.
 */
enum
{
	Match = 256,	// must be greater than 255
	Split = 0xFE,	// must be greater than 255
};

/*
 * Represent an NFA as a linked collection of State structures
 * Each State represents one of three NFA fragments
 * (CONCATENATE, SPLIT, MATCH), depending on the value of c.
 */
typedef struct State State;
struct State
{
	int c;			// the character
	State *out;		// a outgoing linked state
	State *out1;	// another outgoing linked state
	int lastlist;	// used during execution
};

State matchstate = { Match };	/* matching state */
int nstate;

/* Allocate and initialize State */
State*
state(int c, State *out, State *out1)
{
	State *s;

	nstate++;
	s           = malloc(sizeof *s);
	s->lastlist = 0;
	s->c        = c;
	s->out      = out;
	s->out1     = out1;
	return s;
}

/*
 * A partially built NFA without the matching state filled in.
 * Frag.start points at the start state.
 * Frag.out is a list of places that need to be set to the
 * next state for this fragment.
 */
typedef struct Frag Frag;
typedef union Ptrlist Ptrlist;
struct Frag
{
	State *start;	// points at the start state
	Ptrlist *out;	// list of dangling outgoing arrows not yet connected to anything
};

/* Initialize Frag struct. */
Frag
frag(State *start, Ptrlist *out)
{
	Frag n = { start, out };
	return n;
}

/*
 * Since the out pointers in the list are always
 * uninitialized, we use the pointers themselves
 * as storage for the Ptrlists.
 */
union Ptrlist
{
	Ptrlist *next;
	State *s;
};

#pragma mark - HELPER FUNCTIONS TO MANIPULATE POINTER LISTS

/* TIP: the arrow operator p->m is just equivalent to first increase the
 * pointer by some OFFSETS and then DEREFERENCE the pointer, i.e. (*p).m
 */

/* Create singleton list containing just outp. */
Ptrlist*
list1(State **outp)
{
	Ptrlist *l;

	// take a State* pointer's address as Ptrlist* pointer's value
	// so that l->s is exactly the same as the State* pointer
	l = (Ptrlist*)outp;
	l->next = NULL;  // set the state* pointer's value to NULL
	return l;
}

/* Patch the list of states at out to point to start.
 * Connects the dangling arrows in the pointer list l to state s
 */
void
patch(Ptrlist *l, State *s)
{
	Ptrlist *next;

	for(; l; l=next){
		next = l->next;
		l->s = s;
	}
}

/* Join(concatenate) the two lists l1 and l2, returning the combination. */
Ptrlist*
append(Ptrlist *l1, Ptrlist *l2)
{
	Ptrlist *oldl1;

	oldl1 = l1;
	while(l1->next)
		l1 = l1->next;
	l1->next = l2;
	return oldl1;
}

/*
 * Convert postfix regular expression to NFA.
 * Return start state.
 *
 * Given these primitives and a fragment STACK, the compiler is a simple loop
 * over the POSTFIX expression. At the end, there is a single fragment left:
 * patching in a matching state completes the NFA.
 */
State*
post2nfa(char *postfix)
{
	char *p;
	Frag stack[1000], *stackp, e1, e2, e;
	State *s;

	// fprintf(stderr, "postfix: %s\n", postfix);

	if(postfix == NULL)
		return NULL;

	#define push(s) *stackp++ = s
	#define pop() *--stackp

	nstate = 0;
	stackp = stack;
	for(p=postfix; *p; p++){
		switch(*p){
		default:	/* literal characters */
			/*fprintf(stdout, "literal characters: %c, %x\n", *p, *p);*/
			s = state(*p, NULL, NULL);
			push(frag(s, list1(&s->out)));
			break;
		case CATENATE_SYMBOL:	/* catenate */
			e2 = pop();
			e1 = pop();
			patch(e1.out, e2.start);
			push(frag(e1.start, e2.out));
			break;
		case '|':	/* alternate */
			e2 = pop();
			e1 = pop();
			s = state(Split, e1.start, e2.start);
			push(frag(s, append(e1.out, e2.out)));
			break;
		case '?':	/* zero or one */
			e = pop();
			s = state(Split, e.start, NULL);
			push(frag(s, append(e.out, list1(&s->out1))));
			break;
		case '*':	/* zero or more */
			e = pop();
			s = state(Split, e.start, NULL);
			patch(e.out, s);
			push(frag(s, list1(&s->out1)));
			break;
		case '+':	/* one or more */
			e = pop();
			s = state(Split, e.start, NULL);
			patch(e.out, s);
			push(frag(e.start, list1(&s->out1)));
			break;
		}
	}

	e = pop();
	if(stackp != stack)
		return NULL;

	patch(e.out, &matchstate);
	return e.start;
#undef pop
#undef push
}

#pragma mark - Simulating the NFA

/* The simulation requires tracking State sets, which are stored as a simple
 * array list.
 *
 * This is following the Directed GRAPH.
 */

typedef struct List List;
struct List
{
	State **s;
	int n;
};
List l1, l2;
static int listid;

void addstate(List*, State*);
void step(List*, int, List*);

/* Compute initial state list
 * Startlist creates an initial state list by adding just the start state
 */
List*
startlist(State *start, List *l)
{
	l->n = 0;
	listid++;
	addstate(l, start);
	return l;
}

/* Check whether state list contains a match.
 *
 * If the final state list contains the matching state, then the string matches.
 */
int
ismatch(List *l)
{
	int i;

	for(i=0; i<l->n; i++)
		if(l->s[i] == &matchstate)
			return 1;
	return 0;
}

/* Add s to l, following unlabeled arrows.
 *
 * Addstate adds a state to the list, but not if it is already on the list.
 * Scanning the entire list for each add would be inefficient; instead the
 * variable listid acts as a list generation number. When addstate adds s to
 * a list, it records listid in s->lastlist. If the two are already equal, then
 * s is already on the list being built. This is how we deal with *, +
 * splitting cases.
 *
 * Addstate also follows unlabeled
 * arrows : if s is a Split state with two unlabeled arrows to new states,
 * addstate adds those states to the list instead of s.
 */
void
addstate(List *l, State *s)
{
	if(s == NULL || s->lastlist == listid)
		return;
	s->lastlist = listid;
	if(s->c == Split){
		/* follow unlabeled arrows */
		addstate(l, s->out);
		addstate(l, s->out1);
		return;
	}
	l->s[l->n++] = s;
}

/*
 * Step the NFA from the states in clist
 * past the character c,
 * to create next NFA state set nlist.
 *
 * Advances the NFA past a single character, using the current list clist
 * to compute the next list nlist. When there is a split, the NFA are advanced
 * to those "Split state's" outgoing states instead of the "Split state"
 * itself.
 */
void
step(List *clist, int c, List *nlist)
{
	int i;
	State *s;

	listid++;
	nlist->n = 0;
	for(i=0; i<clist->n; i++){
		s = clist->s[i];
		/*printf("stepping s->c: %x, c: %x, %d\n", s->c, c, (s->c - c));*/
		// s->c == '.' represents any character
		// an EVENT that character c is received triggers the STATE TRANSITION
		if(s->c == c || s->c == '.')
			addstate(nlist, s->out);
	}
}

/* Run NFA to determine whether it matches s.
 *
 * The simulation uses two lists: clist is the current set of states that the
 * NFA is in, and nlist is the next set of states that the NFA will be in,
 * after processing the current character. The execution loop initializes
 * clist to contain just the start state and then runs the machine one step
 * at a time.
 */
int
match(State *start, char *s)
{
	int c;
	List *clist, *nlist, *t;

	/* l1 and l2 are preallocated globals to avoid allocation on every iteration */
	clist = startlist(start, &l1);
	nlist = &l2;
	for(; *s; s++){
		/*c = *s & 0xFF;*/
		c = *s;
		step(clist, c, nlist);
		t = clist; clist = nlist; nlist = t;	/* swap clist, nlist */
	}
	return ismatch(clist);
}

// match string with a regular expression
bool
rematch(char *re, char *s)
{
	/*fprintf(stdout, "%ld, %ld, %d\n", strlen(re), strlen(s), !strlen(re) && !strlen(s) );*/
	if (!strlen(re) )
		return !strlen(s);
	char *post = re2post(re);
	State *start = post2nfa(post);

	l1.s = malloc(nstate * sizeof l1.s[0]);
	l2.s = malloc(nstate * sizeof l2.s[0]);

	bool result = match(start, s);

	return result;
}

void test()
{
	assert(!rematch("abc", "abx"));
	assert(rematch(".?", ""));
	assert(rematch(".*", ""));
	assert(!rematch("", "asd"));
	assert(rematch("a", "a"));
	/*assert(rematch("你*好", "好"));*/
	assert(rematch("a*", "aa"));
	assert(rematch("a**", "aa"));
	assert(rematch(".*", "aa"));
	assert(rematch(".*", "ab"));
	assert(!rematch(".*b", "a"));
	assert(rematch("(((((((((a)))))))))", "a"));
	assert(rematch("(a)+b|aac", "aac"));
	assert(rematch("a*(a|cd)+b|aac", "acdb"));
	assert(rematch("a|b|c|d|e", "d"));
	assert(rematch("a|b|c|d|e.*", "d"));
	assert(!rematch("(a|b)c*d", "abcd"));
	assert(rematch("(a|b)c*d", "acd"));
	assert(rematch("(a|b)c*d*d*d*d*d*d*d*d*d*d*d*d*d*d*d*d*d", "acddddddddddddddddddddddddddddddddddddd"));
	assert(rematch("a*a*a*a*a*a*a*a*a*a*a*a*a*a*a*a*a*a*a*a*a*a*a*a*a*a*a*a*c*b+", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaab"));
	assert(rematch("a*a*a*a*a*a*a*a*a*a*a*a*a*a*a*a*a*a*a*a*a*"
				"a*a*a*a*a*a*a*a*a*a*a*a*a*a*a*a*a*a*a*a*a*a*"
				"a*a*a*a*a*a*a*a*a*a*a*a*a*a*a*a*a*a*a*a*a*a*a*a*a*a*a*a*a*a*a*a*b+a*a*",
				"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
				"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaab"
		    ));
	/*assert(rematch("\xff", "\377"));*/
	fprintf(stdout, "\nSELF TEST PASSED!\n\n");
	fflush(stdout);
}

int
main(int argc, char **argv)
{
	int i;
	char *post;
	State *start;
	test();

	if(argc < 3){
		fprintf(stderr, "usage: nfa regexp string...\n");
		return 1;
	}

	post = re2post(argv[1]);
	if(post == NULL){
		fprintf(stderr, "bad regexp %s\n", argv[1]);
		return 1;
	}

	start = post2nfa(post);
	if(start == NULL){
		fprintf(stderr, "error in post2nfa %s\n", post);
		return 1;
	}

	// global variable nstate is increased every time a new State is initialized
	l1.s = malloc(nstate*sizeof l1.s[0]);
	l2.s = malloc(nstate*sizeof l2.s[0]);
	for(i=2; i<argc; i++)
		if(match(start, argv[i]))
			printf("%s\n", argv[i]);
	return 0;
}

/*
 * Permission is hereby granted, free of charge, to any person
 * obtaining a copy of this software and associated
 * documentation files (the "Software"), to deal in the
 * Software without restriction, including without limitation
 * the rights to use, copy, modify, merge, publish, distribute,
 * sublicense, and/or sell copies of the Software, and to
 * permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall
 * be included in all copies or substantial portions of the
 * Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY
 * KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE
 * WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR
 * PURPOSE AND NONINFRINGEMENT.  IN NO EVENT SHALL THE AUTHORS
 * OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR
 * OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR
 * OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
 * SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */
