#include <stdio.h>
#include <stdlib.h>
#include <string.h>

extern void printInt(int n) { printf("%d\n", n); }

extern void printString(const char* str) {
    if (str == NULL)
        printf("\n");
    else
        printf("%s\n", str);
}

int readInt() {
    int n;
    char* str = NULL;
    size_t len = 0;

    getline(&str, &len, stdin);
    sscanf(str, "%d", &n);

    return n;
}

char* readString() {
    char* str = NULL;
    size_t len = 0;

    getline(&str, &len, stdin);
    len = strlen(str);
    if (str[len - 1] == '\n') str[len - 1] = '\0';

    return str;
}

void error() {
    printf("runtime error");
    exit(1);
}

char* _____concatStrings(char* str1, char* str2) {
    if (str1 == NULL) return str2;
    if (str2 == NULL) return str1;

    size_t len1 = strlen(str1), len2 = strlen(str2);
    char* result = malloc(len1 + len2 + 1);

    memcpy(result, str1, len1);
    memcpy(result + len1, str2, len2);
    result[len1 + len2] = '\0';

    return result;
}

int _____compareStrings(char* str1, char* str2) {
    int res;
    if (str1 == NULL && str2 != NULL) {
        res = strcmp("", str2);
    } else if (str1 != NULL && str2 == NULL) {
        res = strcmp(str1, "");
    } else if (str1 == NULL && str2 == NULL) {
        return 0;
    } else {
        res = strcmp(str1, str2);
    }

    return res;
}
