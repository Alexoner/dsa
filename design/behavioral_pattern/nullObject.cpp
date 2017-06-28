#include <iostream>

using namespace std;

class Animal {
public:
    virtual void make_sound() = 0;
};

class Dog : public Animal {
public:
    void make_sound() { cout << "woof!" << endl; }
};

class Null_animal : public Animal {
public:
    void make_sound() {}
};

int main()
{
    Dog dog;
    Null_animal null_animal;
    dog.make_sound();
    null_animal.make_sound();
    return 0;
}
