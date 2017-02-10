#!/usr/bin/env python
# -*- coding: utf-8 -*-

'''
Reservoir sampling is a family of randomized algorithms for randomly choosing k samples
from a list of n items, where n is either a very large or unknown number. Typically n is
large enough that the list doesn’t fit into main memory.

A simple solution is to create an array reservoir[] of maximum size k. One by one
randomly select an item from stream[0..n-1]. If the selected item is not previously
selected, then put it in reservoir[]. To check if an item is previously selected or not,
we need to search the item in reservoir[]. The time complexity of this algorithm will be
O(k^2). This can be costly if k is big. Also, this is not efficient if the input is in the
form of a stream

It can be solved in O(n) time. The solution also suits well for input in the form of stream.
The idea is similar to this post. Following are the steps.

1) Create an array reservoir[0..k-1] and copy first k items of stream[] to it.
2) Now one by one consider all items from (k+1)th item to nth item.
…a) Generate a random number from 0 to i where i is index of current item in stream[]. Let
the generated random number is j.
…b) If j is in range 0 to k-1, replace reservoir[j] with arr[i]

Reference: geeksforgeeks(http://www.geeksforgeeks.org/reservoir-sampling/),
wikipedia(https://en.wikipedia.org/wiki/Reservoir_sampling)
'''

import random


def reservoir_sample(k, data, seed=None):
    '''
    @params
    k: sample count
    data: iterable of records with unknown size

    @return: list of records with size of k
    '''
    # Force the value of the seed so the results are repeatable
    if seed is not None: random.seed(seed)
    samples = []
    for index, record in enumerate(data):
        if index < k:
            samples.append(record)
        else:
            # Randomly replace elements in the reservoir
            # with a decreasing probability.
            # Choose an integer between 0 and index (inclusive)
            r = random.randint(0, index)
            if r < k:
                samples[r] = record
    return samples

def test():
    data = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
    k = 5
    samples = reservoir_sample(k, data)
    print("sampled data: ", samples)

if __name__ == '__main__':
    test()
