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
  APPLY, NUM, B, C, S, K, I, Y, PLUS, MINUS, TIMES, COND, EQ, TRUE, FALSE
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

Noderef stack[100];
int sp;

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

Noderef mknum(int i) {
  Noderef p = mknode(NUM);
  num(p) = i;
  return p;
}

Noderef mkPLUS()        { return mknode(PLUS); }
Noderef mkMINUS()       { return mknode(MINUS); }
Noderef mkTIMES()       { return mknode(TIMES); }
Noderef mkCOND()        { return mknode(COND); }
Noderef mkEQ()          { return mknode(EQ); }
Noderef mkB()           { return mknode(B); }
Noderef mkC()           { return mknode(C); }
Noderef mkS()           { return mknode(S); }
Noderef mkK()           { return mknode(K); }
Noderef mkI()           { return mknode(I); }
Noderef mkTRUE()        { return mknode(TRUE); }
Noderef mkFALSE()       { return mknode(FALSE); }

Noderef init() {        /* This function simulates the compiler */
  Noderef fac = mkapply(0,0);	/* dummy node for recursive function */

  Noderef facp = mkapply(mkapply(mkS(), mkapply(mkapply(mkC(), mkapply(mkapply(mkB(), mkCOND()), mkapply(mkapply(mkC(), mkEQ()), mknum(0)))), mknum(1))), mkapply(mkapply(mkS(), mkTIMES()), mkapply(mkapply(mkB(), fac), mkapply(mkapply(mkC(), mkMINUS()), mknum(1)))));  



  left(fac) = left(facp);
  right(fac) = right(facp);
  return mkapply(fac, mknum(6));
}

void doERR() {
  fprintf(stderr, "Error: a number or a boolean was applied to something (?)");
  abort();
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
  default:
    fprintf(stderr, "Error: doBinaryOp called with %c\n", op);
    abort();
  }
}

void doPLUS() { /* PLUS x y => x+y */
  doBinaryOp('+');
}

void doMINUS() { /* MINUS x y => x-y */
  doBinaryOp('-');
}

void doTIMES() { /* TIMES x y => x*y */
  doBinaryOp('*');
}

void doEQ() { /* EQ x y => TRUE if x=y, EQ x y => FALSE otherwise */
  doBinaryOp('=');
}

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
    abort();
  }
}

void (*redfcns[])() = { doERR, doERR, doB, doC, doS, doK, doI, doY,
  doPLUS, doMINUS, doTIMES, doCOND, doEQ, doERR, doERR };

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
  while (kind(stack[stack_bot]) == APPLY)
    reduction();
  sp = save_sp;
}

int main() {
  Noderef graph;

  graph = init();
  reduce(graph, 0);
  switch (kind(graph)) {
  case NUM:
    printf("%d\n", num(graph));
    break;
  case TRUE:
    printf("true\n");
    break;
  case FALSE:
    printf("false\n");
    break;
  default:
    fprintf(stderr, "result can not be printed.\n");
    abort();
  }
}
