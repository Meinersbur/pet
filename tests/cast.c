void foo()
{
	int a;
	char c = 'a';

#pragma scop
	a = (int) c;
#pragma endscop
}
