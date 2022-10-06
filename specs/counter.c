#include <stdio.h>
int main(int argc, char const *argv[])
{
    int x = 0;
    int N = 50 * 10000000;
    for(int i=0;i<N;i++){
        x = x + 1;
    }
    printf("x=%d\n", x);
    return 0;
}
