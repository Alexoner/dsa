// CPP program to test
// size of struct
#include <iostream>
using namespace std;

// first structure
struct test1
{
	short s;// 2 bytes // 2 padding bytes
	int i; // 4 bytes
	char c; // 1 byte, 3 padding bytes
};

// second structure
struct test2
{
	int i; // 4 bytes
	char c; // 1 byte, 1 padding byte
	short s; // 2 bytes
};

// second structure
struct test3
{
	char c; // 1 byte, 1 padding byte
	short s; // 2 bytes
	int i; // 4 bytes
};


// driver program
int main()
{
	test1 t1;
	test2 t2;
	test3 t3;
	cout << "size of struct test1 is " << sizeof(t1) << "\n";
	cout << "size of struct test2 is " << sizeof(t2) << "\n";
	cout << "size of struct test3 is " << sizeof(t3) << "\n";
	return 0;
}
