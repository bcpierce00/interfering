struct S {
	int x;
};

int f(struct S s) {
	return 0;
}

void main() {
	struct S s;
	s.x = 0;
	f(s);
}
