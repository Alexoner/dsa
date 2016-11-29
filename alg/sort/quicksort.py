'''
quick sort in CLRS python implementation.
'''

import random

class Sort:

    def partitionLomuto(self, A, p, r):
        pivot = A[r]
        i = p - 1
        # A[i] points to element not greater than pivot
        # A[i + 1] points to element greater than pivot
        for j in range(p, r):
            if A[j] <= pivot:
                i += 1
                A[i], A[j] = A[j], A[i]

        i += 1
        A[i], A[r] = A[r], A[i]
        return i

    def partitionHoare(self, A, p, r):
        # XXX: this partition method suffers from repeated elements scenario
        pivot = A[r]
        i, j = p, r
        while True:
            while A[i] < pivot:
                i += 1
            while A[j] > pivot:
                j -= 1
            if i < j:
                A[i], A[j] = A[j], A[i]
                # i += 1
                # j -= 1
            else:
                return j
            pass

    def partitionThreeWay(self, A, p, r):
        '''
        Three way partition using Dutch National Flag algorithm

        Here we use three pointers: i, j, n.
            1. Elements in range [0, i - 1] are smaller than pivot
            2. Elements in range [n + 1, end] are greater than pivot
            3. Element with index j are the current element while sweeping the sequence
        '''
        pivot = A[r]
        i, j, n = p, p, r
        while j <= n:
            if A[j] < pivot:
                A[i], A[j] = A[j], A[i]
                i += 1
                j += 1
            elif A[j] > pivot:
                A[j], A[n] = A[n], A[j]
                n -= 1
            else: j += 1
        return i, n

    def quicksort(self, arr, p, r, partition=None):
        partition = partition or self.partitionLomuto
        if p < r:
            q = partition(arr, p, r)
            self.quicksort(arr, p, q - 1)
            self.quicksort(arr, q + 1, r)

        return arr

    def quicksortIterative(self, arr):
        # random.shuffle(arr)
        stack = [(0, len(arr) - 1)]
        while stack:
            p, r = stack.pop()
            if p < r:
                q = self.partitionLomuto(arr, p, r)
                stack.append((p, q - 1))
                stack.append((q + 1, r))

        return arr

    def quicksort3Way(self, arr):
        stack = [(0, len(arr) - 1)]
        while stack:
            p, r = stack.pop()
            if p < r:
                i, j = self.partitionThreeWay(arr, p, r)
                if p < i - 1:
                    stack.append((p, i - 1))
                if j + 1< r:
                    stack.append((j, r + 1))

if __name__ == "__main__":
    sort = Sort()

    arr = [2, 8, 7, 1, 3, 5, 6, 4]
    sort.quicksort(arr, 0, len(arr) - 1)
    print('{}'.format(arr))
    assert arr == sorted(arr)

    arr = [2, 8, 7, 1, 8, 3, 5, 6, 4, 2]
    p, q = sort.partitionThreeWay(arr, 0, len(arr) - 1)
    print (p, q, arr)

    arr = [2, 8, 7, 1, 8, 3, 5, 6, 4, 2]
    sort.quicksortIterative(arr)
    print ('{}'.format(arr))
    assert arr == sorted(arr)

    arr = [2, 8, 7, 1, 3, 5, 6, 4]
    sort.quicksort(arr, 0, len(arr) - 1, sort.partitionHoare)
    print ('{}'.format(arr))
    assert arr == sorted(arr)

    arr = [1] * 24999 + [2] * 25001
    i, j = sort.partitionThreeWay(arr, 0, len(arr) - 1)
    print (i, j, arr[i], arr[i + 1], arr[j - 1], arr[j])
    sort.quicksort3Way(arr)
    assert arr == sorted(arr)

    print('self test passed')
