#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

/*
 * 
 * Graph reduction                 5/5/90 --kjepo, revised again in 2023!
 *
 * [Turner '79, A new implementation technique for Applicative Languages]
 *
 */

typedef enum {
  APPLY, NUM,
  B, C, S, K, I, Y, P,
  HEAD, TAIL, NULLP,
  PLUS, MINUS, TIMES, COND, EQ,
  TRUE, FALSE, NIL,
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
} *Noderef;

#define kind(p)        ((p)->kind)
#define left(p)        ((p)->u_node.apply.left)
#define right(p)       ((p)->u_node.apply.right)
#define num(p)         ((p)->u_node.val)

Noderef stack[100000];
int sp;
int trace = 0;

void reduce(Noderef graph, int stack_bot);

Noderef mknode(Nodetype tag) {
  Noderef p = (Noderef) malloc(sizeof(struct Node));
  assert(p);
  kind(p) = tag;
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
  Noderef p = mknode(P);
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

int ppcount;
void pp(Noderef p);

void pp(Noderef p) {

  if (ppcount++ > 30) {
    printf("...");
    return;
  }

  if (!p)
    return;

  switch (kind(p)) {
  case APPLY:
    printf("apply(");
    pp(left(p));
    printf(",");
    pp(right(p));
    printf(")");
    break;
  case NUM:
    printf("%d", num(p));
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
  case P:
    printf("P(");
    pp(left(p));
    printf(",");
    pp(right(p));
    printf(")");
    break;
  case B:
    printf("B");
    break;
  case C:
    printf("C");
    break;
  case S:
    printf("S");
    break;
  case K:
    printf("K");
    break;
  case I:
    printf("I");
    break;
  case Y:
    printf("Y");
    break;
  case HEAD:
    printf("head");
    break;
  case TAIL:
    printf("tail");
    break;
  case NULLP:
    printf("null");
    break;      
  case PLUS:
    printf("plus");
    break;
  case MINUS:
    printf("minus");
    break;
  case TIMES:
    printf("times");
    break;
  case COND:
    printf("cond");
    break;
  case EQ:
    printf("eq");
    break;
  default:
    fprintf(stderr, "pp: unknown kind of node: %d\n", kind(p));
    break;
  }
}

void pretty_print(Noderef p, char ch) {
  ppcount = 0;
  pp(p);
  putchar(ch);
}

#define DEF(name, p)	 \
  Noderef name = mkapply(0,0);	 \
  Noderef name##body = p;	 \
  left(name) = left(name##body); \
  right(name) = right(name##body); 



Noderef init() {        /* This function simulates the compiler */

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

  // tail (P 1 (P 2 nil))
  DEF(tail12, mkapply(mkTAIL(), mkapply(mkapply(mkP(), mknum(1)), mkapply(mkapply(mkP(), mknum(2)), mkNIL()))));

  //  Noderef list_12 = mkapply(mkapply(mkP(), mknum(1)), mkapply(mkapply(mkP(), mknum(2)), mkNIL()));
     DEF(list_12, mkapply(mkapply(mkP(), mknum(1)), mkapply(mkapply(mkP(), mknum(2)), mkNIL())));

   DEF(list2, mkapply(mkapply(mkP(), mknum(1)), mkapply(mkapply(mkP(), mknum(2)), mkNIL())));
   DEF(list3, mkapply(mkapply(mkP(), mknum(1)), mkapply(mkapply(mkP(), mknum(2)), mkapply(mkapply(mkP(), mknum(3)), mkNIL()))));

   // P 1 (P 2 (P 3 (P 4 (P 5 (P 6 (P 7 (P 8 (P 9 (P 10 nil)))))))))
   DEF(list10, mkapply(mkapply(mkP(), mknum(1)), mkapply(mkapply(mkP(), mknum(2)), mkapply(mkapply(mkP(), mknum(3)), mkapply(mkapply(mkP(), mknum(4)), mkapply(mkapply(mkP(), mknum(5)), mkapply(mkapply(mkP(), mknum(6)), mkapply(mkapply(mkP(), mknum(7)), mkapply(mkapply(mkP(), mknum(8)), mkapply(mkapply(mkP(), mknum(9)), mkapply(mkapply(mkP(), mknum(10)), mkNIL())))))))))));

   DEF(pgm, mkapply(len, list10));
   return pgm;

   
  // def ack x y = if y==0 then ack (x-1) 1 else (if x==0 then y+1 else ack (x-1) (ack x (y-1)));
  // S (B S (B (C (B cond (C equal 0))) (C (B ack (C minus 1)) 1))) (S (B S (C (B B (B cond (C equal 0))) (C plus 1))) (S (B B (B ack (C minus 1))) (C (B B ack) (C minus 1))))
  DEF(ack, mkapply(mkapply(mkS(), mkapply(mkapply(mkB(), mkS()), mkapply(mkapply(mkB(), mkapply(mkC(), mkapply(mkapply(mkB(), mkCOND()), mkapply(mkapply(mkC(), mkEQUAL()), mknum(0))))), mkapply(mkapply(mkC(), mkapply(mkapply(mkB(), ack), mkapply(mkapply(mkC(), mkMINUS()), mknum(1)))), mknum(1))))), mkapply(mkapply(mkS(), mkapply(mkapply(mkB(), mkS()), mkapply(mkapply(mkC(), mkapply(mkapply(mkB(), mkB()), mkapply(mkapply(mkB(), mkCOND()), mkapply(mkapply(mkC(), mkEQUAL()), mknum(0))))), mkapply(mkapply(mkC(), mkPLUS()), mknum(1))))), mkapply(mkapply(mkS(), mkapply(mkapply(mkB(), mkB()), mkapply(mkapply(mkB(), ack), mkapply(mkapply(mkC(), mkMINUS()), mknum(1))))), mkapply(mkapply(mkC(), mkapply(mkapply(mkB(), mkB()), ack)), mkapply(mkapply(mkC(), mkMINUS()), mknum(1)))))));


  //  return mkapply(mkapply(ack, mknum(3)), mknum(8));
  //  return mkapply(sign, mknum(0));
  //  return mkapply(sum, mknum(10));
  //  return mkapply(fak, mknum(6));
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
  *stack[sp] = *x;
}

void doI() { /* I x => x */
  Noderef x;
  assert(sp > 0);
  x = right(stack[sp-1]);
  sp -= 1;
  *stack[sp] = *x;
}

void doY() { /* Y h = h(Y h) = h(h(h(....))) */
  Noderef h;
  assert(sp > 0);
  h = right(stack[sp-1]);
  sp -= 1;
  left(stack[sp]) = h;
  right(stack[sp]) = stack[sp]; /* tie the knot */
}

void doUnaryOp(op) {
  Noderef x;
  int xval;
  assert(sp > 0);
  x = right(stack[sp-1]);
  if (kind(x) != NUM) {
    reduce(x, sp);		/* recursively evaluate x */
    x = stack[sp];
  }
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


void doBinaryOp(op) {
  Noderef x, y;
  int xval, yval;
  assert(sp > 1);
  x = right(stack[sp-1]);
  y = right(stack[sp-2]);
  if (kind(x) != NUM) {
    reduce(x, sp);		/* recursively evaluate x */
    x = stack[sp];
  }
  xval = num(x);
  if (kind(y) != NUM) {
    reduce(y, sp);
    y = stack[sp];
  }
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

void doHEAD() { /* HEAD x y => x */
  Noderef x;
  assert(sp > 0);
  x = right(stack[sp-1]);
  sp -= 2;
  *stack[sp] = *x;
}

void doTAIL() { /* TAIL x y => y */
  Noderef y;
  assert(sp > 0);
  y = stack[sp-1];
  y = right(y);
  y = right(y);
  sp -= 1;
  *stack[sp] = *y;
}

void doNULL() { /* NULL x => TRUE iff x == NIL, else FALSE */
  Noderef x, y;
  int xval, yval;
  assert(sp > 0);
  x = right(stack[sp-1]);
  if (kind(x) != P) {
    reduce(x, sp);		/* recursively evaluate x */
    x = stack[sp];
  }
  if ((kind(x) != P) && (kind(x) != NIL)) {
    fprintf(stderr, "NULL applied on a non-list.\n");
    pretty_print(stack[sp], '\n');
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
  if (kind(pred) != TRUE && kind(pred) != FALSE) {
    reduce(pred, sp);
    pred = stack[sp];
  }
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

void (*redfcns[])() = {
  doERR, doERR,			          /* APPLY, NUM */
  doB, doC, doS, doK, doI, doY, doP,      /* B, C, S, K, I, Y, P */
  doHEAD, doTAIL, doNULL,		  /* HEAD, TAIL, NULL */
  doPLUS, doMINUS, doTIMES, doCOND, doEQ, /* PLUS, MINUS, TIMES, COND, EQ */
  doERR, doERR, doERR,                    /* TRUE, FALSE, NIL */
  doLT, doGT, doNE, doNOT		  /* LT, GT, NE, NOT */
};

void push(Noderef n) {
  assert(sp < sizeof(stack));
  stack[++sp] = n;
}

void reduction() {
  while (kind(stack[sp]) == APPLY)
    push(left(stack[sp]));
  redfcns[kind(stack[sp])]();
}

void reduce(Noderef graph, int stack_bot) {
  int save_sp = sp;
  sp = stack_bot;
  stack[stack_bot] = graph;
  while (kind(stack[stack_bot]) == APPLY) {
    if (trace) {
      printf("--> "); pretty_print(graph, '\n');
    }
    reduction();
    if (trace) {
      printf("<-- "); pretty_print(graph, '\n');
    }
  }
  sp = save_sp;
}

void printlist(Noderef);

void print(Noderef graph) {
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
  case P:
    printlist(graph);
    break;
  default:
    fprintf(stderr, "result can not be printed, kind=%d\n", kind(graph));
    pretty_print(graph, '\n');
    exit(1);
  }
}

void printlist(Noderef graph) {
  if (graph == 0)
    return;
  pretty_print(left(graph), ':');
  graph = right(graph);
  reduce(graph, 0);
  print(graph);
}

int main(int argc, char *argv[]) {
  Noderef graph = init();

  for (int i = 1; i < argc; i++) {
    if (argv[i][0] == '-') {
      if (argv[i][1] == 't')
	trace = 1;
      if (argv[i][1] == 'h') {
	fprintf(stderr, "Usage: %s [-th]\n\n-t: trace\n-h: this help\n", argv[0]);
	exit(0);
      }
    }
  }

  reduce(graph, 0);
  graph = stack[0];
  print(graph);
  printf("\n");
}
