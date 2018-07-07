int swap(int a, int b, int c, int d, int e) {
        int sum = 0;
        if (a > 100)
            b = 2;
        else
            b = 10;
        int i = 0;
        while (i < b) {
            sum = sum + i;
            i = i + 1;
        }
        return sum;
}