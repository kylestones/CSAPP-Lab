

int fun4(int x, int y, int z)
{
    int num1 = ((z-y) >> 31 + (z-y) ) >> 1 + y;
    if (num1 == x) { // 先是 >= 后是 <= ，所以只能是 ==
        return 0;
    }
    else {
        num1--;
        fun4(x, y, num1);
    }
}

int fun7(int *a, int b)
{
    int c = *a;

    if (c == b) {
        return 0;
    }
    else if (c < b) {
        a += 2;
        return 2 * fun7(a, b) + 1;
    }
    else {
        a += 1;
        return 2 * fun7(a,b);
    }
}
