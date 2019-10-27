"""
Given a fair coin, simulate the probability of 1/n, where n is an arbitrary positive integer.

================================================================================
SOLUTION

A fair coin can output binary result. And it's easy to simulate probability of 1 over powers
of 2.

--------------------------------------------------------------------------------
But the target probability is 1/n, and n is an arbitrary positive integer.
So the first problem is to REPRESENT INTEGER with BINARY system.

BINARY NUMBERS!!!
Any integer can be represented with a binary number.
Treat the result of every flip of the coin as 0 and 1. Then if we toss the coin m times,
there are m bits representing a binary number.

--------------------------------------------------------------------------------
CONDITIONAL PROBABILITY

p(x = 0 | x < n) = p(x = 0, x < n) / p(x < n) = p(x = 0) / p(x < n) = 1 / n.

Take m = ceil(log₂n). Repeat process of tossing the coin m times, until the
binary number x represented by m tosses in one process is smaller than n.
Then x = 0 indicates the event that x = 0 given x < n, with a probability of 1/n, happened.
Return true, else return false, meaning the event with 1/n probability didn't happen.

"""

import math
import random

def simulateOneOverNWithFairCoin(n, tosser=lambda : random.randint(0, 1)):
    m = math.ceil(math.log2(n))
    M = math.pow(2, m)
    x = M
    # condition x < n
    while x >= n:
        # toss m times
        x = 0
        for i in range(m):
            x = x * 2 + tosser() # binary representation of random tossing outcome
    result = int(x == 0) # 1 for hit
    # print(result)
    return result

def test():
    n = 10 # test for 1/n
    N = 10000 # simulate N times

    x = 0
    for i in range(N):
        x += simulateOneOverNWithFairCoin(n)
    print(x/N, 1/n)
    print("self test passed")
    pass

if __name__ == '__main__':
    test()
