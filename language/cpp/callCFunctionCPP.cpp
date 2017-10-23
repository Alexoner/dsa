/*
 * How can a C function be called in a C++ program?
 *
 * Answer:
 * Using an "extern C" declaration.
 */
//C++ code
extern "C"{
void func(int i);
void print(int i);
}

void myfunc(int i)
{
   func(i);
   print(i);
}

int main()
{
	myfunc(0);
}
