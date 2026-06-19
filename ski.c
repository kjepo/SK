#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <assert.h>

/*
 * 
 * Graph reduction  5/5/90 --kjepo, revised again 2023 and again in 2024!
 *
 * [Turner '79, A new implementation technique for Applicative Languages]
 *
 */

typedef enum {			/* change redfcns to match this */
  INDIRECTION,
  APPLY, NUM,
  B, C, S, K, I, Y,
  P,				/* P builds a pair */
  HEAD, TAIL, NULLP,
  PLUS, MINUS, TIMES, COND, EQ,
  TRUE, FALSE, NIL,
  CONS,				/* CONS is the value */
  LT, GT, NE, NOT
} Nodetype;

typedef struct Node {
  Nodetype kind;
  union {
    struct {
      struct Node *left;
      struct Node *right;
    } apply;
    int val;
  } u_node;
  int nodenumber;
  int visited;
} *Noderef;

#define kind(p)        ((p)->kind)
#define left(p)        ((p)->u_node.apply.left)
#define right(p)       ((p)->u_node.apply.right)
#define num(p)         ((p)->u_node.val)
#define nodenumber(p)  ((p)->nodenumber)
#define visited(p)     ((p)->visited)

Noderef graph, root;	        /* the combinator graph */
Noderef stack[100000];	        /* spine stack for unwinding */
int sp;		                /* stack pointer  */
int trace = 0;	                /* =1 if we're tracing the evaluation */
int dag = 0;	                /* =1 if we're generating graphviz code  */
FILE *dagfp;	                /* output file for graphviz code */
int nodectr = 0;                /* every node has a unique number */
int visitctr = 0;		/* to detect cycles in the graph while traversing */

Noderef reduce(Noderef graph, int stack_bot);
void print(Noderef graph);
char *result_to_str(Noderef g, char *p);

Noderef mknode(Nodetype tag) {
  Noderef p = (Noderef) malloc(sizeof(struct Node));
  assert(p);
  kind(p) = tag;
  left(p) = right(p) = 0;	/* in case malloc doesn't return 0 bytes */
  nodenumber(p) = nodectr++;
  visited(p) = visitctr;
  return p;
}

Noderef mkapply(Noderef l, Noderef r) {
  Noderef p = mknode(APPLY);
  left(p) = l;
  right(p) = r;
  return p;
}

// not sure if P should be overloaded as both a combinator (w/o arguments)
// and a node kind, like a cons cell.  Perhaps re-introduce CONS again?
// we can't implement the P-rule as "do nothing", hoping that it will
// be reduced when the list encounters null, head or tail.
// The reason is that head must evaluate its argument recursively
// and if the argument is P x y, internally represented as
// apply(apply(...(apply(P, ...))))
// then the evaluation will never terminate because of all the apply nodes.
// However, if P x y is rewritten as cons(x,y) we won't have that problem
// because head can then return x, tail can return y and null can
// check if it's nil or not.

Noderef mkpair(Noderef l, Noderef r) {
  Noderef p = mknode(CONS);
  left(p) = l;
  right(p) = r;
  return p;
}

Noderef mknum(int i) {
  Noderef p = mknode(NUM);
  num(p) = i;
  return p;
}

Noderef mkHEAD()        { return mknode(HEAD); }
Noderef mkTAIL()        { return mknode(TAIL); }
Noderef mkNULL()        { return mknode(NULLP); }
Noderef mkPLUS()        { return mknode(PLUS); }
Noderef mkEQUAL()       { return mknode(EQ); }
Noderef mkNOTEQUAL()    { return mknode(NE); }
Noderef mkLESSTHAN()    { return mknode(LT); }
Noderef mkGREATERTHAN() { return mknode(GT); }
Noderef mkNOT()         { return mknode(NOT); }
Noderef mkMINUS()       { return mknode(MINUS); }
Noderef mkTIMES()       { return mknode(TIMES); }
Noderef mkCOND()        { return mknode(COND); }
Noderef mkEQ()          { return mknode(EQ); }
Noderef mkB()           { return mknode(B); }
Noderef mkC()           { return mknode(C); }
Noderef mkS()           { return mknode(S); }
Noderef mkK()           { return mknode(K); }
Noderef mkI()           { return mknode(I); }
Noderef mkP()           { return mknode(P); }
Noderef mkY()           { return mknode(Y); }
Noderef mkTRUE()        { return mknode(TRUE); }
Noderef mkFALSE()       { return mknode(FALSE); }
Noderef mkNIL()         { return mknode(NIL); }

char *print_tag(Noderef p) {
  if (!p)
    return "NIL";
  switch (kind(p)) {
  case INDIRECTION: return "i";
  case APPLY: return "APPLY";
  case NUM: return "NUM";
  case B: return "B";
  case C: return "C";
  case S: return "S";
  case K: return "K";
  case I: return "I";
  case Y: return "Y";
  case P: return "P";
  case CONS: return ":";
  case HEAD: return "HEAD";
  case TAIL: return "TAIL";
  case NULLP: return "NULLP";
  case PLUS: return "PLUS";
  case MINUS: return "MINUS";
  case TIMES: return "TIMES";
  case COND: return "COND";
  case EQ: return "EQ";
  case TRUE: return "TRUE";
  case FALSE: return "FALSE";
  case NIL: return "NIL";
  case LT: return "LT";
  case GT: return "GT";
  case NE: return "NE";
  case NOT: return "NOT";
  default: return "?";
  }
}

void pretty_print_aux(Noderef p) {
  if (!p || visited(p) >= visitctr)
    return;
  visited(p) = visitctr;
  char *tag = print_tag(p);
  switch (kind(p)) {
  case INDIRECTION:
    pretty_print_aux(right(p));
    break;
  case APPLY:
  case CONS:
    printf("%s(", tag); 
    pretty_print_aux(left(p));
    printf(",");
    pretty_print_aux(right(p));
    printf(")");
    break;
  case NUM:
    printf("%d", num(p));
    break;
  default:
    printf("%s", tag);
    break;
  }
}

void graphviz_aux(Noderef p) {
  if (!p || visited(p) >= visitctr)
    return;
  visited(p) = visitctr;
  char *tag = print_tag(p);
  char *pairname = ":";
  int nodenum = nodenumber(p);
  switch (kind(p)) {
  case INDIRECTION:
    fprintf(dagfp, "%s_%d -> %s_%d;\n", tag, nodenum, print_tag(right(p)), nodenumber(right(p)));
    graphviz_aux(right(p));
    break;
  case APPLY:
    pairname = "@";
  case CONS:
    fprintf(dagfp, "%s_%d [label=\"%s\", shape=plaintext, constraint=false, ordering=out];\n", tag, nodenum, pairname);
    if (left(p)) {
      graphviz_aux(left(p));
      fprintf(dagfp, "%s_%d -> %s_%d;\n", tag, nodenum, print_tag(left(p)), nodenumber(left(p)));
    }
    if (right(p)) {
      graphviz_aux(right(p));
      fprintf(dagfp, "%s_%d -> %s_%d;\n", tag, nodenum, print_tag(right(p)), nodenumber(right(p)));
    }
    break;
  case NUM:
    fprintf(dagfp, "%s_%d [label=\"%d\", shape=plaintext];\n", print_tag(p), nodenumber(p), num(p));
    break;
  default:
    fprintf(dagfp, "%s_%d [label=\"%s\", shape=plaintext];\n", tag, nodenum, tag);
    break;
  }
}

void graphviz() {
  visitctr++;
  fprintf(dagfp, "digraph G{\nsize=\"14!,14!\"\n");
  graphviz_aux(root);
  fprintf(dagfp, "}\n");  
}

void pretty_print(Noderef p, char *prefix, char ch) {
  visitctr++;
  if (trace) {
    printf("%s", prefix);
    pretty_print_aux(p);
  }
  if (trace)
    putchar(ch);
}

#define DEF(name, p)	 \
  Noderef name = mkapply(0,0);	 \
  Noderef name##body = p;	 \
  left(name) = left(name##body); \
  right(name) = right(name##body); 

void init() {           /* builds every example, then evaluates and prints each */
  // ex1 = S K K 42
  DEF(ex1, mkapply(mkapply(mkapply(mkS(), mkK()), mkK()), mknum(42)));

  // S12 = + 1 2
  DEF(S12, mkapply(mkapply(mkPLUS(), mknum(1)), mknum(2)));
  // ex2 = * S12 S12
  DEF(ex2, mkapply(mkapply(mkTIMES(), S12), S12));
  
  // p12 = + 2 3
  DEF(p12, mkapply(mkapply(mkPLUS(), mknum(2)), mknum(3)));
  // a1 = K p12 101
  DEF(a1, mkapply(mkapply(mkK(), p12), mknum(101)));
  // a2 = K p12 102
  DEF(a2, mkapply(mkapply(mkK(), p12), mknum(102)));
      
  // def sign x = if x < 0 then -1 else (if x > 0 then 1 else 0);
  // S (C (B cond (C lessthan 0)) (minus 0 1)) (C (C (B cond (C greaterthan 0)) 1) 0)
  DEF(sign, mkapply(mkapply(mkS(), mkapply(mkapply(mkC(), mkapply(mkapply(mkB(), mkCOND()), mkapply(mkapply(mkC(), mkLESSTHAN()), mknum(0)))), mkapply(mkapply(mkMINUS(), mknum(0)), mknum(1)))), mkapply(mkapply(mkC(), mkapply(mkapply(mkC(), mkapply(mkapply(mkB(), mkCOND()), mkapply(mkapply(mkC(), mkGREATERTHAN()), mknum(0)))), mknum(1))), mknum(0))));

  // def sum n = if n == 0 then 0 else n + sum(n-1);
  // S (C (B cond (C equal 0)) 0) (S plus (B sum (C minus 1)))
  DEF(sum, mkapply(mkapply(mkS(), mkapply(mkapply(mkC(), mkapply(mkapply(mkB(), mkCOND()), mkapply(mkapply(mkC(), mkEQUAL()), mknum(0)))), mknum(0))), mkapply(mkapply(mkS(), mkPLUS()), mkapply(mkapply(mkB(), sum), mkapply(mkapply(mkC(), mkMINUS()), mknum(1))))));

  // def fac x = if x==0 then 1 else x*fac(x-1);
  // S (C (B cond (C equal 0)) 1) (S times (B fac (C minus 1)))
  DEF(fak, mkapply(mkapply(mkS(), mkapply(mkapply(mkC(), mkapply(mkapply(mkB(), mkCOND()), mkapply(mkapply(mkC(), mkEQUAL()), mknum(0)))), mknum(1))), mkapply(mkapply(mkS(), mkTIMES()), mkapply(mkapply(mkB(), fak), mkapply(mkapply(mkC(), mkMINUS()), mknum(1))))));
  
  // def len xs = if (null xs) then 0 else 1 + len(tail xs);
  // S (C (B cond null) 0) (B (plus 1) (B len tail))
  DEF(len, mkapply(mkapply(mkS(), mkapply(mkapply(mkC(), mkapply(mkapply(mkB(), mkCOND()), mkNULL())), mknum(0))), mkapply(mkapply(mkB(), mkapply(mkPLUS(), mknum(1))), mkapply(mkapply(mkB(), len), mkTAIL()))));

  // (P 1 (P 2 nil))
  DEF(list12, mkapply(mkapply(mkP(), mknum(1)), mkapply(mkapply(mkP(), mknum(2)), mkNIL())));

  // tail (P 1 (P 2 nil))
  DEF(tail12, mkapply(mkTAIL(), mkapply(mkapply(mkP(), mknum(1)), mkapply(mkapply(mkP(), mknum(2)), mkNIL()))));

  //  Noderef list_12 = mkapply(mkapply(mkP(), mknum(1)), mkapply(mkapply(mkP(), mknum(2)), mkNIL()));
  DEF(list_12, mkapply(mkapply(mkP(), mknum(1)), mkapply(mkapply(mkP(), mknum(2)), mkNIL())));

   DEF(list3, mkapply(mkapply(mkP(), mknum(1)), mkapply(mkapply(mkP(), mknum(2)), mkapply(mkapply(mkP(), mknum(3)), mkNIL()))));

   // P 1 (P 2 (P 3 (P 4 (P 5 (P 6 (P 7 (P 8 (P 9 (P 10 nil)))))))))
   DEF(list10, mkapply(mkapply(mkP(), mknum(1)), mkapply(mkapply(mkP(), mknum(2)), mkapply(mkapply(mkP(), mknum(3)), mkapply(mkapply(mkP(), mknum(4)), mkapply(mkapply(mkP(), mknum(5)), mkapply(mkapply(mkP(), mknum(6)), mkapply(mkapply(mkP(), mknum(7)), mkapply(mkapply(mkP(), mknum(8)), mkapply(mkapply(mkP(), mknum(9)), mkapply(mkapply(mkP(), mknum(10)), mkNIL())))))))))));
   // return list10;

   // def range n = if n == 0 then [] else n : range(n-1);
   DEF(range, mkapply(mkapply(mkS(), mkapply(mkapply(mkC(), mkapply(mkapply(mkB(), mkCOND()), mkapply(mkapply(mkC(), mkEQUAL()), mknum(0)))), mkNIL())), mkapply(mkapply(mkS(), mkP()), mkapply(mkapply(mkB(), range), mkapply(mkapply(mkC(), mkMINUS()), mknum(1))))));

   // C plus 1
   DEF(inc, mkapply(mkapply(mkC(), mkPLUS()), mknum(1)));
   // S B (C B I)
   DEF(fndouble, mkapply(mkapply(mkS(), mkB()), mkapply(mkapply(mkC(), mkB()), mkI())));
   // S B (C B I) (C plus 1) 17
   DEF(ex3, mkapply(mkapply(mkapply(mkapply(mkS(), mkB()), mkapply(mkapply(mkC(), mkB()), mkI())), mkapply(mkapply(mkC(), mkPLUS()), mknum(1))), mknum(17)));

  // def ack x y = if y==0 then ack (x-1) 1 else (if x==0 then y+1 else ack (x-1) (ack x (y-1)));
  // S (B S (B (C (B cond (C equal 0))) (C (B ack (C minus 1)) 1))) (S (B S (C (B B (B cond (C equal 0))) (C plus 1))) (S (B B (B ack (C minus 1))) (C (B B ack) (C minus 1))))
  DEF(ack, mkapply(mkapply(mkS(), mkapply(mkapply(mkB(), mkS()), mkapply(mkapply(mkB(), mkapply(mkC(), mkapply(mkapply(mkB(), mkCOND()), mkapply(mkapply(mkC(), mkEQUAL()), mknum(0))))), mkapply(mkapply(mkC(), mkapply(mkapply(mkB(), ack), mkapply(mkapply(mkC(), mkMINUS()), mknum(1)))), mknum(1))))), mkapply(mkapply(mkS(), mkapply(mkapply(mkB(), mkS()), mkapply(mkapply(mkC(), mkapply(mkapply(mkB(), mkB()), mkapply(mkapply(mkB(), mkCOND()), mkapply(mkapply(mkC(), mkEQUAL()), mknum(0))))), mkapply(mkapply(mkC(), mkPLUS()), mknum(1))))), mkapply(mkapply(mkS(), mkapply(mkapply(mkB(), mkB()), mkapply(mkapply(mkB(), ack), mkapply(mkapply(mkC(), mkMINUS()), mknum(1))))), mkapply(mkapply(mkC(), mkapply(mkapply(mkB(), mkB()), ack)), mkapply(mkapply(mkC(), mkMINUS()), mknum(1)))))));

  // (I (C plus 1)) 17  -- exposes the function-position indirection bug
  DEF(itest, mkapply(mkapply(mkI(), mkapply(mkapply(mkC(), mkPLUS()), mknum(1))), mknum(17)));

  struct { char *desc; Noderef expr; char *expected; } tests[] = {
    { "S K K 42",                  ex1,                                       "42" },
    { "range 10",                  mkapply(range, mknum(10)),                 "10:9:8:7:6:5:4:3:2:1:nil" },
    { "S B (C B I) (C plus 1) 17", ex3,                                       "19" },
    { "I (C plus 1) 17",           itest,                                     "18" },
    { "head (1:2:nil)",            mkapply(mkHEAD(), list_12),                "1" },
    { "tail (1:2:nil)",            tail12,                                    "2:nil" },
    { "len (1:2:3:nil)",           mkapply(len, list3),                       "3" },
    { "sum 10",                    mkapply(sum, mknum(10)),                   "55" },
    { "fak 6",                     mkapply(fak, mknum(6)),                    "720" },
    { "sign 0",                    mkapply(sign, mknum(0)),                   "0" },
    { "sign -5",                   mkapply(sign, mknum(-5)),                  "-1" },
    { "sign 7",                    mkapply(sign, mknum(7)),                   "1" },
    { "ack 3 8",                   mkapply(mkapply(ack, mknum(3)), mknum(8)), "2045" },
    { "times (K p12 101) (K p12 102) where p12 = (plus 2 3)",
                                   mkapply(mkapply(mkTIMES(), a1), a2),       "25" },
  };

  int npass = 0, ntest = (int)(sizeof(tests)/sizeof(tests[0]));
  for (int i = 0; i < ntest; i++) {
    char buf[8192];
    printf("eval:     %s\n", tests[i].desc);
    sp = 0;
    root = graph = tests[i].expr;
    root = reduce(graph, 0);
    *result_to_str(root, buf) = 0;
    int ok = strcmp(buf, tests[i].expected) == 0;
    npass += ok;
    printf("result:   %s\n", buf);
    printf("expected: %s\n", tests[i].expected);
    printf("%s\n\n", ok ? "PASS" : "FAIL");
  }
  printf("%d/%d passed\n", npass, ntest);
}


void doERR() {
  return;
}

void doB() { /* B f g x => f (g x) */
  Noderef f, g, x;
  assert(sp > 2);
  f = right(stack[sp-1]);
  g = right(stack[sp-2]);
  x = right(stack[sp-3]);
  sp -= 3;
  left(stack[sp]) = f;
  right(stack[sp]) = mkapply(g, x);
}

void doC() { /* C f g x => f x g */
  Noderef f, g, x;
  assert(sp > 2);
  f = right(stack[sp-1]);
  g = right(stack[sp-2]);
  x = right(stack[sp-3]);
  sp -= 3;
  left(stack[sp]) = mkapply(f, x);
  right(stack[sp]) = g;
}

void doS() { /* S x y z => x z (y z) */
  Noderef x, y, z;
  assert(sp > 2);
  x = right(stack[sp-1]);
  y = right(stack[sp-2]);
  z = right(stack[sp-3]);
  sp -= 3;
  left(stack[sp]) = mkapply(x, z);
  right(stack[sp]) = mkapply(y, z);
}

void doK() { /* K x y => x */
  Noderef x;
  assert(sp > 1);
  x = right(stack[sp-1]);
  sp -= 2;
  kind(stack[sp]) = INDIRECTION;
  right(stack[sp]) = x;
}

void doI() { /* I x => x */
  Noderef x;
  assert(sp > 0);
  x = right(stack[sp-1]);
  sp -= 1;
  kind(stack[sp]) = INDIRECTION;
  right(stack[sp]) = x;
}

void doY() { /* Y h = h(Y h) = h(h(h(....))) */
  Noderef h;
  assert(sp > 0);
  h = right(stack[sp-1]);
  sp -= 1;
  left(stack[sp]) = h;
  right(stack[sp]) = stack[sp]; /* tie the knot */
}

void doUnaryOp(char op) {
  Noderef x;
  int xval;
  assert(sp > 0);
  x = right(stack[sp-1]);
  if (kind(x) != NUM)
    x = reduce(x, sp);		/* recursively evaluate x */
  xval = num(x);
  sp -= 1;
  kind(stack[sp]) = NUM;
  switch (op) {
  case '!':
    num(stack[sp]) = !xval;
    break;
  default:
    fprintf(stderr, "Error: doUnaryOp called with %c\n", op);
    exit(1);
  }
}

void doBinaryOp(char op) {
  Noderef x, y;
  int xval, yval;
  assert(sp > 1);
  x = right(stack[sp-1]);
  y = right(stack[sp-2]);
  if (kind(x) != NUM) 
    x = reduce(x, sp);		/* recursively evaluate x */
  xval = num(x);
  if (kind(y) != NUM)
    y = reduce(y, sp);		/* recursively evaluate y */
  yval = num(y);
  sp -= 2;
  kind(stack[sp]) = NUM;
  switch (op) {
  case '+':
    num(stack[sp]) = xval + yval;
    break;
  case '-':
    num(stack[sp]) = xval - yval;
    break;
  case '*':
    num(stack[sp]) = xval * yval;
    break;
  case '=':
    kind(stack[sp]) = (xval == yval ? TRUE : FALSE);
    break;
  case '#':
    kind(stack[sp]) = (xval != yval ? TRUE : FALSE);
    break;
  case '<':
    kind(stack[sp]) = (xval < yval ? TRUE : FALSE);
    break;
  case '>':
    kind(stack[sp]) = (xval > yval ? TRUE : FALSE);
    break;
  default:
    fprintf(stderr, "Error: doBinaryOp called with %c\n", op);
    exit(1);
  }
}

void doP() { /* P x y => cons(x,y) */
  Noderef x, y, z;
  assert (sp > 1);
  x = right(stack[sp-1]);
  y = right(stack[sp-2]);
  sp -= 2;
  z = mkpair(x, y);
  *stack[sp] = *z;
}

void doHEAD() { /* HEAD (CONS x y) => x */
  assert(sp > 0);	          /* need @(HEAD, list) at stack[sp-1] */
  Noderef x = right(stack[sp-1]); /* the list argument */
  if (CONS != kind(x))
    x = reduce(x, sp);		/* force it to a cons cell (WHNF) */
  if (CONS != kind(x)) {
    fprintf(stderr, "HEAD applied to a non-list.\n");
    pretty_print(stack[sp], "", '\n');
    exit(1);
  }
  sp -= 1;			/* unary: pop one */

  // we don't do *stack[sp] = *left(x) here because that would copy
  // the head cell, duplicating a node and lose its sharing, potentially
  // breaking Y-cycles

  kind(stack[sp]) = INDIRECTION; /* result is the head, shared via indirection */
  right(stack[sp]) = left(x);
}

void doTAIL() { /* TAIL (CONS x y) => y */
  assert(sp > 0);
  Noderef x = right(stack[sp-1]);
  if (CONS != kind(x))
    x = reduce(x, sp);
  if (CONS != kind(x)) {
    fprintf(stderr, "TAIL applied to a non-list.\n");
    pretty_print(stack[sp], "", '\n');
    exit(1);
  }
  sp -= 1;
  kind(stack[sp]) = INDIRECTION;
  right(stack[sp]) = right(x);	/* only difference from HEAD: right(x) */
}

void doNULL() { /* NULL x => TRUE iff x == NIL, else FALSE */
  Noderef x;
  assert(sp > 0);
  x = right(stack[sp-1]);
  if (kind(x) != CONS)
    x = reduce(x, sp);		/* recursively evaluate x */
  if ((kind(x) != CONS) && (kind(x) != NIL)) {
    fprintf(stderr, "NULL applied on a non-list.\n");
    pretty_print(stack[sp], "", '\n');
    exit(1);
  }
  sp -= 1;
  kind(stack[sp]) = (kind(x) == NIL ? TRUE : FALSE);
}

void doEQUAL()    { doBinaryOp('='); }
void doPLUS()     { doBinaryOp('+'); }
void doMINUS()    { doBinaryOp('-'); } /* MINUS x y => x-y */
void doTIMES()    { doBinaryOp('*'); }
void doEQ()       { doBinaryOp('='); } /* EQ x y => TRUE if x=y, EQ x y => FALSE otherwise */
void doNE()       { doBinaryOp('#'); }
void doLT()       { doBinaryOp('<'); }
void doGT()       { doBinaryOp('>'); }
void doNOT()      { doUnaryOp('!'); }

void doCOND() { /* COND TRUE x y => x, COND FALSE x y => y */
  Noderef pred, tnod, fnod;
  assert(sp > 2);
  pred = right(stack[sp-1]);
  tnod = right(stack[sp-2]);
  fnod = right(stack[sp-3]);
  if (kind(pred) != TRUE && kind(pred) != FALSE)
    pred = reduce(pred, sp);
  sp -= 3;
  switch (kind(pred)) {
  case TRUE:
    *stack[sp] = *tnod;
    break;
  case FALSE:
    *stack[sp] = *fnod;
    break;
  default:
    fprintf(stderr, "predicate wasn't boolean.\n");
    exit(1);
  }
}

void (*redfcns[])() = {	                  /* this must match the enum for Nodetype */
  doERR,				  /* INDIRECTION */
  doERR, doERR,			          /* APPLY, NUM */
  doB, doC, doS, doK, doI, doY, doP,      /* B, C, S, K, I, Y, P */
  doHEAD, doTAIL, doNULL,		  /* HEAD, TAIL, NULL */
  doPLUS, doMINUS, doTIMES, doCOND, doEQ, /* PLUS, MINUS, TIMES, COND, EQ */
  doERR, doERR, doERR, doERR,             /* TRUE, FALSE, NIL, CONS */
  doLT, doGT, doNE, doNOT		  /* LT, GT, NE, NOT */
};

void push(Noderef n) {
  assert((size_t) sp < sizeof(stack)/sizeof(stack[0]));
  stack[++sp] = n;
}

void reduction() {
  if (dag)
    graphviz();
  if (trace)
    pretty_print(graph, "--> ", '\n');

  while (kind(stack[sp]) == APPLY || kind(stack[sp]) == INDIRECTION)
    if (kind(stack[sp]) == INDIRECTION)
      stack[sp] = right(stack[sp]); /* shortcut thru the indirection */
    else
      push(left(stack[sp]));

  redfcns[kind(stack[sp])]();
  if (dag)
    graphviz();
  if (trace)
    pretty_print(graph, "<-- ", '\n');
}

Noderef reduce(Noderef graph, int stack_bot) {
  int save_sp = sp;
  while (kind(graph) == APPLY || kind(graph) == INDIRECTION) {
    if (kind(graph) == INDIRECTION) {
      graph = right(graph);	/* follow the indirection, then re-check */
    } else {
      stack[sp =stack_bot] = graph;
      reduction();		/* updates *graph (== stack[stack_bot] in place */
    }
  }
  sp = save_sp;
  return graph;
}

void printlist(Noderef);

void print(Noderef graph) {
  while (kind(graph) == INDIRECTION) /* a reduced result may be an indirection */
    graph = right(graph);
  switch (kind(graph)) {
  case NUM:
    printf("%d", num(graph));
    break;
  case TRUE:
    printf("true");
    break;
  case FALSE:
    printf("false");
    break;
  case NIL:
    printf("nil");
    break;
  case CONS:
    printlist(graph);
    break;
  default:
    fprintf(stderr, "result can not be printed, kind=%d\n", kind(graph));
    pretty_print(graph, "", '\n');
    exit(1);
  }
}

void printlist(Noderef graph) {
  int trace_value;
  if (!graph)
    return;
  trace_value = trace;
  trace = 1;
  pretty_print(left(graph), "", ':');
  trace = trace_value;
  graph = right(graph);
  graph = reduce(graph, 0);
  print(graph);
}

char *result_to_str(Noderef g, char *p) { /* render a reduced result to a string, for PASS/FAIL */
  while (kind(g) == INDIRECTION) g = right(g);
  switch (kind(g)) {
  case NUM:   return p + sprintf(p, "%d", num(g));
  case TRUE:  return p + sprintf(p, "true");
  case FALSE: return p + sprintf(p, "false");
  case NIL:   return p + sprintf(p, "nil");
  case CONS:
    p = result_to_str(reduce(left(g), sp), p);
    *p++ = ':';
    return result_to_str(reduce(right(g), sp), p);
  default:    return p + sprintf(p, "?kind=%d", kind(g));
  }
}

int main(int argc, char *argv[]) {
  char *usage = "Usage: %s [-t] [-d dotfile] [-h]\n\n-t: trace\n-d file: save graphviz file in file\n-h: this help\n";

  for (int i = 1; i < argc; i++) {
    if (argv[i][0] == '-') {
      if (argv[i][1] == 't')
	trace = 1;
      if (argv[i][1] == 'd') {
	dag = 1;
	if (i + 1 >= argc || !strcmp(&argv[i+1][0], "-"))
	  dagfp = stdout;
	else
	  assert(dagfp = fopen(&argv[i+1][0], "w"));
      }
      if (argv[i][1] == 'h') {
	fprintf(stderr, usage, argv[0]);
	exit(0);
      }
    }
  }

  init();   /* build, evaluate and check every example */
}
