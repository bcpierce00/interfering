int f() {
	return 0;
}

void publish(int x) {
	return;
}

void main(int argc, int* argv) {
	int secret = argv[1];
	int sensitive[4] = {0,0,0,0};
	int res = f();
	if (sensitive[0] == 42)
		publish(secret);
	else
		publish(res);
	return;
}
