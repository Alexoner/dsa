#include <memory>
#include <queue>
#include <iostream>

using namespace std;

/**
 * stack:  pFrame{control & data pointer}     pFrame1    pString
 *
 *
 * Heap:   (*pFrame: Frame{pString}|counter) (*pString: string|counter)
 *
 */

class Frame {
public:
    shared_ptr<string> pString;
};

int blackBox(shared_ptr<Frame> pFrame) {
    shared_ptr<string> &pMessage = pFrame->pString;
    cout << &pMessage << " " << pMessage.get()  << endl;
    pFrame->pString = NULL; // gdb is supposed to break here
    return 0;
}

int testPointerQueue() {
    queue<shared_ptr<Frame>> mq; //

    shared_ptr<Frame> pFrame = make_shared<Frame>();
    {
        shared_ptr<string> pString = make_shared<string>("hello world");
        pFrame->pString = pString;
        cout << &pFrame->pString  << " " << pFrame->pString.get()  << " " << *pFrame->pString << endl;
        // 0x61aee0 0x61af10 hello world
    }

    {
        shared_ptr<string> &pString = pFrame->pString; // pFrame->pString is shared_ptr object on heap
        auto address = &pString;
        cout << "to watch address: " << address << endl;
        /**
         * watchpoint on *address
         * gdb> watch -l pString # &pString == &pString._M_ptr
         * gdb> watch -l *address # equivalent to watch -l pString._M_ptr
         * or just
         * gdb> watch -l *0x61aee0
         * gdb> x/s *0x0061af10 # examine string at pString.at()
         * gdb> print *(char**)0x0061af10 # equivalent to above
         */
    }

    {
        mq.push(pFrame);
        //shared_ptr<string> &pString = mq.front()->pString;
    }

    {
        shared_ptr<Frame> pFrame1 = mq.front(); mq.pop();
        shared_ptr<string> &pMessage = pFrame1->pString;
        cout << &pMessage << " " << pMessage.get()  << " " << *pMessage << endl;
    }

    {
        // this may modify the shared_ptr._M_ptr
        //pMessage = NULL; // gdb> watch point triggered
        //cout << &pMessage << " " << pMessage.get()  << endl;
        blackBox(pFrame);
    }

    return 0;
}

int main(int argc, char **argv) {
    testPointerQueue();

    return 0;
}
