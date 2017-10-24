/*
class No { }; - defines a class, which will have an undefined size, which won't be zero (mandated by the standard)

class Yes { No no[3]; }; - defines another class, Yes which will be at least 3 times as big as a No. So they are guaranteed to be different sizes.

static Yes Test( B* ); - declare a function which returns a Yes, but don't give it a definition (we don't need one). It will match any pointer argument which is pointing to an object derived from B.

static No Test( ... ); - declare a function which returns a No (smaller, remember?). It's an overload which will be selected if the more specific one (above) cannot be satisfied. It accepts any argument (but the other version will be selected by overload resolution in preference if the argument is derived from B).

sizeof(Test(static_cast<D*>(0))) deduces the size of the object returned by Test when passes a pointer to a D. If D is derived from B, it will be a Yes, otherwise it will be a No.

Because the 'call' is made in a non-deduced context, it is not evaluated (called), just selected and return type deduced.

The rest is probably self-explanatory. turns out it wasn't :)

So this all gets put together here:

enum { Is = sizeof(Test(static_cast<D*>(0))) == sizeof(Yes) };

What this is doing in a nutshell, is saying:

"declare a constant called Is, which will be true if the result of calling Test with a D* is a type that happens to be the same size as a Yes. And it will be false if the result of the call happens to be a type which is a different size. Because of the two overloads, above, when D is a B, or anything derived from it, Test(D*) will select the Yes version, which will return a Yes, which is obviously the same size as a Yes. If this overload is not selected, the more permissive (but lower priority) one will be. That one returns a No, which obviously won't be the same size as a Yes (by definition)."

Why is Test(...) 'lower priority' than Test(B*) (in terms of overload resolution)? Because it just is. The standard defines it to be.

Finally:

template <class C, class P>
bool IsDerivedFrom() {
 return IsDerivedFromHelper<C, P>::Is;
}
This creates a function which will return the result of the above test for any two class types, C and P. This it will return true if P is derived from a C and false otherwise.
*/

#include <iostream>
#include <assert.h>

template<typename D, typename B>
class IsDerivedFromHelper
{
	class No {};
	class Yes {No no[3];};

	static Yes Test(B*);
	static No Test( ... );

	public:
	enum { Is = sizeof(Test(static_cast<D*>(0))) == sizeof(Yes) };
};

template <class C, class P>
bool IsDerivedFrom() {
	return IsDerivedFromHelper<C, P>::Is;
}

void testDerived()
{
	class B {};
	class A: public B {};
	class C {};

	//assert(IsDerivedFrom<A, B>());
	bool result;
	result = IsDerivedFrom<A, B>();
	assert (result);

	result = IsDerivedFrom<C, B>();
	assert (!result);

	result = IsDerivedFrom<C, A>();
	assert (!result);


	std::cout << "self test passed!" << std::endl;
}

int main() {
	testDerived();
}
