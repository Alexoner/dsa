/*
What is the output of the following code:

The above will output:
from A
from A
from Base
The important thing to note here is the order of destruction of classes and how Base’s method reverts back to its own implementation once A has been destroyed.
*/

#include <iostream>

class Base {
public:
	//virtual void method() {std::cout << "from Base" << std::endl;}
	void method() {std::cout << "from Base" << std::endl;}
	virtual ~Base() {method();}
	void baseMethod() {method();}
};

class A : public Base {
public:
	void method() {std::cout << "from A" << std::endl;}
	//virtual void method() {std::cout << "from A" << std::endl;}
	~A() {method();}
};

int main(void) {
	Base* base = new A;
	base->baseMethod(); // A

	//A *a = (A*)base;
	//a->method(); // A

	delete base; // A, base
	return 0;
}
