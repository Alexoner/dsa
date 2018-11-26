#include <algorithm>
#include <cassert>
#include <iostream>

template<long FROM, long TO>
class Range {
public:
    // member typedefs provided through inheriting from std::iterator
    class iterator: public std::iterator<std::input_iterator_tag, long>{
        long num = FROM;
    public:
        explicit iterator(long _num): num(_num) {};
        iterator& operator++() {num = (TO >= FROM ? num+1 : num-1); return *this;} // prefix ++
        iterator operator++(int) {
            iterator retval = *this;
            ++(*this);
            return retval;
        } // postfix ++. Get value then increment.
        bool operator==(iterator other) {
            return this->num == other.num;
        }
        bool operator!=(iterator other) {
            return !(*this == other);
        }

        reference operator*() {
            return num;
        }
    };

    iterator begin() {
        return iterator(FROM);
    }

    iterator end() {
        return iterator(TO);
    }
};

int main(int argc, char *argv[])
{
    Range<15, 25> range;
    auto itr = range.begin();
    assert(*itr == 15);

    itr = std::find(range.begin(), range.end(), 18);
    assert(*itr == 18);

    // Range::iterator also satisfies range-based for requirements
    for (long l: Range<3, 5>()) {
        std::cout << l << " ";
    }
    std::cout << std::endl;

    std::cout << "self test passed!" << std::endl;

    return 0;
}
