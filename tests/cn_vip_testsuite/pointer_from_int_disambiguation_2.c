//CN_VIP #include <stdio.h>
//CN_VIP #include <string.h>
#include <stdint.h>
#include <inttypes.h>
#include <stddef.h>
#include "cn_lemmas.h"

int y=2, x=1;
int main()
/*CN_VIP*//*@ accesses x; accesses y; @*/
{
  int *p = &x+1;
  int *q = &y;
  uintptr_t i = (uintptr_t)p;
  uintptr_t j = (uintptr_t)q;
  /*CN_VIP*//*@ to_bytes Owned<int*>(&p); @*/
  /*CN_VIP*//*@ to_bytes Owned<int*>(&q); @*/
  if (_memcmp((unsigned char*)&p, (unsigned char*)&q, sizeof(p)) == 0) {
    /*CN_VIP*//*@ from_bytes Owned<int*>(&p); @*/
    /*CN_VIP*//*@ from_bytes Owned<int*>(&q); @*/
    /*CN_VIP*/int *r = __cerbvar_copy_alloc_id(i, &x); // TODO remove copy alloc id
    r=r-1;  // is this free of UB?
    *r=11;  // and this?
    //CN_VIP printf("x=%d y=%d *q=%d *r=%d\n",x,y,*q,*r);
    /*CN_VIP*//*@ assert (x == 11i32 && y == 2i32 && *q == 2i32 && *r == 11i32); @*/
  }
  /*CN_VIP*//*@ from_bytes Owned<int*>(&p); @*/
  /*CN_VIP*//*@ from_bytes Owned<int*>(&q); @*/
}
