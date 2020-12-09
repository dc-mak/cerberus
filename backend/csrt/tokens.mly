%token <int> NUM
%token <string> ID
%token <string> PID
%token TRUE FALSE
%token AT DOT STAR AMPERSAND
%token POINTER_TO_INTEGER INTEGER_TO_POINTER
%token LPAREN RPAREN
%token COMMA
%token PLUS MINUS DIV
%token LT GT LE GE NE EQEQ
%token MIN MAX
%token CHAR SHORT INT LONG SIGNED UNSIGNED
%token BLOCK UNOWNED
%token EOF
%left LT GT LE GE EQEQ NE
%left PLUS MINUS
%left DIV
%right INTEGER_TO_POINTER POINTER_TO_INTEGER
%right STAR


%%
