#include <string.h>
#include <stdio.h>

int main() {
  int y;
  goto l2;
l1:
  {
    int x;
    return y;
l2:
    if (x) {
        y = 0;
        // printf("yay\n");
    } else {
        y = 1;
        // printf("boo\n");
    }
    goto l1;
  }
}
