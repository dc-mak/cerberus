//CN_VIP #include <stdio.h>
#include <inttypes.h>
int x=1;
int main()
/*CN_VIP*//*@ accesses x; @*/
{
  int *p = &x;
  intptr_t i = (intptr_t)p;
  /*CN_VIP*/int *q = __cerbvar_copy_alloc_id((uintptr_t)i, p); // TODO remove copy alloc id
  *q = 11; // is this free of undefined behaviour?
  //CN_VIP printf("*p=%d  *q=%d\n",*p,*q);
  /*CN_VIP*//*@ assert(*p == 11i32 && *q == 11i32); @*/
}
