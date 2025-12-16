#include <stdio.h>
#include <stdlib.h>

/* Declarations of runtime helpers */
const char* to_string(const void*);
char* concat(char*, char*);
void print(const char*);

int main(void) {
    const char* s = to_string((const void*)(intptr_t)42);
    char* c = concat((char*)"The value is: ", (char*)s);
    print(c);
    /* Print again to exercise backtrace paths */
    print(c);
    return 0;
}
