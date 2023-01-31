/*
 *   Scanner, parser and syntax-directed translation for MORK (Mora rekursiv kalkylator)
 *
 */


#include <stdio.h>
#include <stdlib.h>
#include <setjmp.h>
#include <signal.h>
#include <unistd.h>
#include <ctype.h>
#include <math.h>
#include <string.h>
#include <readline/readline.h>
#include <readline/history.h>
#include <assert.h>

int verbose = 0;
char *fname;
FILE *fp;
int lineno;
char *progname;
char *input;
static jmp_buf jmpbuf;

void error(char *s)   {
  printf("%s on line %d, file %s\n", s, (lineno-1), fname);
  longjmp(jmpbuf, 1);
}

void interrupt_handler(int sig) {
  char c;
  signal(sig, SIG_IGN);
  printf("Interrupt\n");
  signal(SIGINT, interrupt_handler);
  longjmp(jmpbuf, 1);
}

char *allocstr(char *s) {
  char *p = malloc(strlen(s) + 1);
  strcpy(p, s);
  return p;
}

// scanner 
typedef enum toktype {
  END=1, ID, NUM, STR, NIL, ARROW, DEF, IF, THEN, ELSE,
  CMPEQ, CMPNE, CMPLT = '<', CMPGT = '>', 
  NOT = '!', SEMI = ';', LPAR = '(', RPAR = ')', COLON = ':', LAMBDA = '\\',
  EQUAL = '=', PLUS = '+', MINUS = '-', TIMES = '*'
} Token;

Token token;                    // current token
char id[80];                    // string value when token == ID
int nval;                       // numeric value when token == NUM

typedef enum {
  AST_LAMBDA, AST_APPLY, AST_COLON, AST_PLUS, AST_MINUS, AST_TIMES, AST_NIL, AST_NUM, AST_ID, AST_NOT, AST_EQ, AST_NE, AST_LT, AST_GT 
} AST_Kind;

typedef struct AST_Node {
  AST_Kind kind;
  union {
    struct {
      struct AST_Node *child1;
      struct AST_Node *child2;
      struct AST_Node *child3;
    } apply;
    int val;
    char *str;
  } u_node;
} *AST_Node;

#define kind(p)        ((p)->kind)
#define left(p)        ((p)->u_node.apply.child1)
#define right(p)       ((p)->u_node.apply.child2)
#define third(p)       ((p)->u_node.apply.child3)
#define num(p)         ((p)->u_node.val)
#define str(p)         ((p)->u_node.str)

AST_Node mknode(AST_Kind tag) {
  AST_Node p = (AST_Node) malloc(sizeof(struct AST_Node));
  assert(p);
  kind(p) = tag;
  return p;
}


AST_Node mknil() {
  AST_Node p = mknode(AST_NIL);
  return p;
}

AST_Node mknum(int i) {
  AST_Node p = mknode(AST_NUM);
  num(p) = i;
  return p;
}

AST_Node mkid(char *s) {
  AST_Node p = mknode(AST_ID);
  str(p) = allocstr(s);
  return p;
}

AST_Node mkunop(AST_Kind tag, AST_Node l) {
  AST_Node p = mknode(tag);
  left(p) = l;
  return p;
}    

AST_Node mkop(AST_Kind tag, AST_Node l, AST_Node r) {
  AST_Node p = mknode(tag);
  left(p) = l;
  right(p) = r;
  return p;
}

AST_Node mkif(AST_Node p1, AST_Node p2, AST_Node p3) {
  return mkop(AST_APPLY, mkop(AST_APPLY, mkop(AST_APPLY, mkid("cond"), p1), p2), p3);
}

//  "sq2" --> \x->\y->x*x+y*y
//  String -> Expr

#define SYMTABSIZE 1024

struct {
  char *id;
  AST_Node expr;
} symtab[SYMTABSIZE];

int symtabp = 0;

int symtabLookup(char *s) {
  for (int i = 0; i < symtabp; i++)
    if (!strcmp(symtab[i].id, s))
      return 1;
  return 0;
}


int legal_symbol_start(char ch) { return isalpha(ch) || strchr("$_", ch); }
int legal_symbol_rest(char ch)  { return isalnum(ch) || strchr("$_'", ch); }

void cr_readline() {
  char prompt[20], *p;
  size_t len;
  sprintf(prompt, "[%d] ", lineno++);
  if (fp != stdin) {
    input = NULL;
    if (getline(&input, &len, fp) == -1) // POSIX (but see README for options)
      input = "(exit)";
    return;
  }
  p = readline(prompt);
  if (!p)
    exit(0);
  add_history(p);
  int n = strlen(p);
  input = malloc(n + 2);
  strcpy(input, p);		/* fixme: memory leak */
  input[n] = '\n';		/* add \n at end of input */
  input[n+1] = 0;
}

char nextchar() {
  while (input == 0 || *input == 0 || *input == '#')
    cr_readline();
  return *input++;
}

char nextrealchar() {
  char ch;
  do {
    ch = nextchar();
  } while (ch == ' ' || ch == '\t');
  return ch;
}


/* ==================================================
 * SCANNER
 * ==================================================
 */

Token scan1() {
  char *p, ch = nextrealchar(), lastchar;

  switch (ch) {
  case '\n':
    return token = END;
  case '\"':
    p = id;
    lastchar = ch;
    while ((ch = nextchar()) != EOF) {
      if (lastchar == '\\') {
        if (ch == 'a')	  *(p-1) = '\a';
        if (ch == 'b')	  *(p-1) = '\b';
        if (ch == 'f')	  *(p-1) = '\f';
        if (ch == 'n')	  *(p-1) = '\n';
        if (ch == 'r')	  *(p-1) = '\r';
        if (ch == 't')	  *(p-1) = '\t';
        if (ch == 'v')	  *(p-1) = '\v';
        if (ch == '\'')	  *(p-1) = '\'';
        if (ch == '\\')	  *(p-1) = '\\';
      } else if (ch == '\"') {
        *p = 0;
        return token = STR;
      } else {
        *p++ = ch;
      }
      lastchar = ch;
    }
    error("unterminated string");
  case ';':
    return token = SEMI;
  case '(':
    return token = LPAR;
  case ')':
    return token = RPAR;
  case '[':
    if ((ch = nextchar()) == ']')
      return token = NIL;
    else
      error("Sorry, list constants are not implemented yet.");
  case '<':
    return token = CMPLT;
  case '>':
    return token = CMPGT;
  case NOT:
    if ((ch = nextchar()) == '=')
      return token = CMPNE;
    else {
      input--;
      return token = NOT;
    }
  case PLUS:
    return token = PLUS;
  case MINUS:
    if ((ch = nextchar()) == '>')
      return token = ARROW;
    else {
      input--;
      return token = MINUS;
    }
  case TIMES:
    return token = TIMES;
  case COLON:
    return token = COLON;
  case LAMBDA:
    return token = LAMBDA;
  case EQUAL:
    if ((ch = nextchar()) == '=')
      return token = CMPEQ;
    else {
      input--;
      return token = EQUAL;
    }
  case '0': case '1': case '2': case '3': case '4':
  case '5': case '6': case '7': case '8': case '9':
    p = id;
    do {
      *p++ = ch;
      ch = nextchar();
    } while (isdigit(ch) || ch == '.');
    *p = 0;
    input--;
    sscanf(id, "%d", &nval);
    return token = NUM;
  default:
    if (legal_symbol_start(ch) && ch != ' ') {
      char cc = 0, *p = id;
      *p++ = ch;
      while ((ch = nextchar()) && legal_symbol_rest(ch))
        *p++ = ch;
      input--;
      *p = 0;
      // a integer number is an optional + or - followed by at least one or more digits,
      // with an optional fractional part.  These are numbers: 1, -1, +1, -12, -3.14
      // but these are not -, -1x, +, ++, .1
      if (sscanf(id, "%d%c", &nval, &cc) == 1 && cc == 0)
        return token = NUM;

      if (!strcmp(id, "def"))
	return token = DEF;
      else if (!strcmp(id, "if"))
	return token = IF;
      else if (!strcmp(id, "then"))
	return token = THEN;
      else if (!strcmp(id, "else"))
	return token = ELSE;
      else
	return token = ID;
    } else {
      return scan1();
    }
  }
}

void printToken(Token t) {
  switch (t) {
  case END:
    printf("\nEND\n");
    break;
  case ID:
    printf("%s ", id);
    break;
  case NUM:
    printf("%d ", nval);
    break;
  case NIL:
    printf("[] ");
    break;
  case STR:
    printf("\"%s\" ", id);
    break;
  case ARROW:
    printf("-> ");
    break;
  case DEF:
    printf("DEF ");
    break;
  case IF:
    printf("IF ");
    break;
  case THEN:
    printf("THEN ");
    break;
  case ELSE:
    printf("ELSE ");
    break;
  case SEMI:
    printf(";\n");
    break;
  case CMPEQ:
    printf("== ");
    break;
  case CMPNE:
    printf("!= ");
    break;
  case CMPLT:
  case CMPGT:
  case PLUS:
  case MINUS:
  case TIMES:
  case LPAR:
  case RPAR:
  case COLON:
  case LAMBDA:
  case EQUAL:
  case NOT:
    putchar(t);
    putchar(' ');
    break;
  default:
    printf("Unknown token!");
    break;
  }
}  

Token scan() {
  Token t = scan1();
  if (verbose)
    printToken(t);
  return t;
}

/* ==================================================
 * PARSER
 * ==================================================
 */

void printAST(AST_Node p) {
  switch (kind(p)) {
  case AST_LAMBDA:
    printf("(Abs ");
    printf("\"%s\" (", str(left(p)));
    printAST(right(p));
    printf(")) ");
    return;
  case AST_APPLY:
    printf("(App ");
    printAST(left(p));
    printf(" ");
    printAST(right(p));
    printf(")");
    return;
  case AST_PLUS:
    printf("(App (App (Var \"plus\") ");
    printAST(left(p));
    printf(") ");
    printAST(right(p));
    printf(") ");    
    return;
  case AST_MINUS:
    printf("(App (App (Var \"minus\") ");
    printAST(left(p));
    printf(") ");
    printAST(right(p));
    printf(") ");    
    return;
  case AST_COLON:
    printf("(App (App P ");
    printAST(left(p));
    printf(") ");
    printAST(right(p));
    printf(") ");    
    return;
  case AST_TIMES:
    printf("(App (App (Var \"times\") ");
    printAST(left(p));
    printf(") ");
    printAST(right(p));
    printf(") ");    
    return;
  case AST_EQ:
    printf("(App (App (Var \"equal\") ");
    printAST(left(p));
    printf(") ");
    printAST(right(p));
    printf(") ");    
    return;
  case AST_NE:
    printf("(App (App (Var \"notequal\") ");
    printAST(left(p));
    printf(") ");
    printAST(right(p));
    printf(") ");    
    return;
  case AST_LT:
    printf("(App (App (Var \"lessthan\") ");
    printAST(left(p));
    printf(") ");
    printAST(right(p));
    printf(") ");    
    return;
  case AST_GT:
    printf("(App (App (Var \"greaterthan\") ");
    printAST(left(p));
    printf(") ");
    printAST(right(p));
    printf(") ");    
    return;
  case AST_NOT:
    printf("(App (Var \"not\") ");
    printAST(left(p));
    printf(") ");
    return;
  case AST_NIL:
    printf("(Var \"nil\") ");
    return;
  case AST_NUM:
    printf("(Number %d)", num(p));
    return;
  case AST_ID:
    if (!strcmp(str(p), "cons"))
      printf("P ");
    else if (symtabLookup(str(p)))
      printf("%s ", str(p));
    else
      printf("(Var \"%s\") ", str(p));
    return;
  }
}



AST_Node parse_expr();

AST_Node parse_factor() {
  AST_Node f = 0, f1;
  do {
    if (token == LPAR) {
      scan();
      f1 = parse_expr();
      if (token == RPAR) {
	scan();
      } else
	error("expected ')'");
    } else if (token == ID) {
      f1 = mkid(id);
      scan();
    } else if (token == NUM) {
      f1 = mknum(nval);
      scan();
    } else if (token == NIL) {
      f1 = mknil();
      scan();
    }
    f = f ? mkop(AST_APPLY, f, f1) : f1;
  } while (token == LPAR || token == ID || token == NUM);
  return f;
}

AST_Node parse_term() {
  AST_Node p, p1;

  if (token == MINUS) {
    scan();
    p = parse_factor();
    p = mkop(AST_MINUS, mknum(0), p);
  } else {
    p = parse_factor();
    switch (token) {
    case TIMES:			/* * is left-assocative: use iteration */
      while (token == TIMES) {
	scan();
	p1 = parse_factor();
	p = mkop(AST_TIMES, p, p1);
      }
      break;
    case COLON:			/* cons is right-associative: use recursion */
      while (token == COLON) {
	scan();
	p1 = parse_term();
	p = mkop(AST_COLON, p, p1);
      }
      break;
    default:
      break;
    }
  }
  return p;
}  

AST_Node parse_cond() {
  AST_Node p1, p2;
  if (token == NOT) {
    scan();
    p1 = parse_cond();
    return mkunop(AST_NOT, p1);
  } else {
    p1 = parse_expr();
    if (token == CMPEQ) {
      scan();
      p2 = parse_expr();
      return mkop(AST_EQ, p1, p2);
    } else if (token == CMPNE) {
      scan();
      p2 = parse_expr();
      return mkop(AST_NE, p1, p2);
    } else if (token == CMPLT) {
      scan();
      p2 = parse_expr();
      return mkop(AST_LT, p1, p2);
    } else if (token == CMPGT) {
      scan();
      p2 = parse_expr();
      return mkop(AST_GT, p1, p2);
    } else
      return p1;
  }
}

AST_Node parse_expr() {
  AST_Node p1, p2, p3, p;
  if (token == LAMBDA) {	/* \ ID -> expr */
    scan();
    if (token == ID) {
      p1 = mkid(id);
      scan();
      if (token == ARROW) {
	scan();
	p2 = parse_expr();
	p = mkop(AST_LAMBDA, p1, p2);
      } else
	error("expected ->");
    } else
      error("expected identifier");
  } else if (token == IF) {	/* IF expr THEN expr ELSE expr */
    scan();
    p1 = parse_cond();
    if (token == THEN)
      scan();
    else {
      printf("found ");
      printToken(token);
      error("hm, expected 'then'");
    }
    p2 = parse_expr();
    if (token == ELSE)
      scan();
    else
      error("expected 'else'");
    p3 = parse_expr();
    p = mkif(p1, p2, p3);
  } else {			/* term { ( "+" | "-" ) term }  */
    p = parse_term();
    while (token == PLUS || token == MINUS) {
      Token op = token;
      scan();
      p1 = parse_term();
      p = mkop((op == PLUS ? AST_PLUS : AST_MINUS), p, p1);
    }
  }
  return p;
}

AST_Node parse_body() {
  AST_Node p;
  while (token == ID) {
    char *param = allocstr(id);
    scan();
    return mkop(AST_LAMBDA, mkid(param), parse_body());
  }
  if (token == '=')
    scan();
  else
    error("expected '='");
  p = parse_expr();
  return p;
}

void dumpSymtab() {
  printf("\n----SYMBOL TABLE----\n");
  for (int i = 0; i < symtabp; i++) {
    printf("%s: ", symtab[i].id);
    printAST(symtab[i].expr);
    printf("\n");
  }
  printf("--------------------\n");  
}

void parse_definition() {
  AST_Node p;
  if (token == DEF) {
    scan();
    if (token == ID) {
      printf("%s = ", id);
      symtab[symtabp].id = allocstr(id);
      scan();
    } else
      error("expected identifier");
  } else
    error("expected 'def'");
  p = parse_body();
  printAST(p);
  symtab[symtabp].expr = p;
  symtabp++;
  if (verbose)
    dumpSymtab();
  printf("\n");
}
			  
AST_Node parse() {
  AST_Node p;
  for (;;) {
    while (token == END)
      scan();
    if (token == DEF) {
      parse_definition();
      if (token == SEMI) {
	scan();
	scan();
      } else {
	printf("found ");
	printToken(token);
	error("but expected ';'");
      }
    } else if (token == LAMBDA || token == IF || token == LPAR || token == ID || token == NUM || token == MINUS) {
      p = parse_expr();
      printf("line%d = ", lineno);
      printAST(p);
      printf("\n");
    } else {
      printf("found ");
      printToken(token);
      error("but expected a definition or expression");
    }
  }
}

void repl() {

  // uncomment this to get the token stream:
  //  for (;;) { scan(); } return;


  input = 0;
  lineno = 1;
  for (;;) {
    scan();
    if (strncmp(input, "exit)", 5) == 0 && fp != stdin)
      return;  /* kludge to stop reading from file */
    if (token == END)		/* reached trailing \n */
      continue;
    parse();
    printf("\n");
  }
}

void slurp(char *f) {
  fname = f;
  if (!(fp = fopen(fname, "r"))) {
    fprintf(stderr, "%s: could not open %s\n", progname, fname);
    exit(1);
  } else {
    printf("reading %s...\n", fname);
    repl();
    fclose(fp);
    fp = stdin;
  }
}

int main(int argc, char *argv[]) {
  char *usage = "usage: %s [-v] [filename ...]\n";
  progname = argv[0];
  fp = stdin;
  fname = "stdin";
  signal(SIGINT, interrupt_handler);
  if (setjmp(jmpbuf) == 1)
    goto repl;

  for (int i = 1; i < argc; i++) {
    if (argv[i][0] == '-') {
      if (argv[i][1] == 'v') {
        verbose = 1;
      } else {
        fprintf(stderr, usage, progname);
        exit(1);
      }
    } else {
      slurp(argv[i]);
      fp = stdin;
      fname = "stdin";
    }
  }

  lineno = 1;
 repl:
  fp = stdin;
  fname = "stdin";
  repl();
}
