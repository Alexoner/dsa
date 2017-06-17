#include <iostream>

using namespace std;

class SmartPtr
{
	int *ptr; // actual pointer
	public:
	// Constructor: Refer http://www.geeksforgeeks.org/g-fact-93/,
	explicit SmartPtr(int *p = NULL) { ptr = p; }

	// Destructor
	~SmartPtr() {
		cout << "deleting allocated memory" << endl;
		delete(ptr);
	}

	// Overloading dereferencing operator
	int &operator *() {
		return *ptr;
	}
};
