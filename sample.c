int swap(int a, int b, int c, int d, int e) {
    int r = 0;
    if (!(a < 0))
        r = (a | b) & c + d << 2;
    else
        r = 2;
    return r;
}