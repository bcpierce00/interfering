int id(int a, int b, int c, int d, int e, int f, int g, int h, int i) {
	return i;
}

int id2(int x) {
	return x;
}

void main() {
	id(1,2,3,4,5,6,7,8,9);
	id2(42);
	id(1,2,3,4,5,6,7,8,9);
}
