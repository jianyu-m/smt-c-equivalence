int swap(int *a, int b, int c, int d, int e) {
        int sum = 0;
        int* sum_ptr = &sum;
        *sum_ptr = 3;
        int total = 0;
        for (int i = 0;i < 10;i++) {
            total += sum;
        }
        return total;
}