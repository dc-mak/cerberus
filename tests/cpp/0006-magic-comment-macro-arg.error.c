#define GE(a, b) a >= b
int g(int x);
/*@ spec g(i32 x); requires GE(x, 0i32) bad; @*/
