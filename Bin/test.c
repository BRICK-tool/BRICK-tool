#include "stdlib.h"
void __BRICK_SPEC(int x){};
int main(){
    int a=0;
    double b = a+2;
    __BRICK_SPEC(b==2);
    return 0;
}
