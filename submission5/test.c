void swap (int* x, int*y) {
	int t;
	t = *x;
	*x = *y;
	*y = t;
	return;
}

int main() {
	int a = 1;
	int b = 2;

	swap(&a, &b);
	return a;
}
