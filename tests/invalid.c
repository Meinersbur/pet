void f()
{
	int A[100];
#pragma scop
	for (int i = 0; i < 100; ++i)
		A[i-1] = 0;
#pragma endscop
}
