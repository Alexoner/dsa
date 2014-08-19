'''
quick sort in CLRS python implementation.
'''


class Sort:

    def partition(self, A, p, r):
        pivot = A[r]
        i = p - 1
        for j in range(p, r, 1):
            if A[j] <= pivot:
                i += 1
                A[i], A[j] = A[j], A[i]

        i += 1
        A[i], A[r] = A[r], A[i]
        return i

    def quicksort(self, arr, p, r):
        if p < r:
            q = self.partition(arr, p, r)
            self.quicksort(arr, p, q - 1)
            self.quicksort(arr, q + 1, r)

if __name__ == "__main__":
    arr = [2, 8, 7, 1, 3, 5, 6, 4]
    Sort().quicksort(arr, 0, len(arr) - 1)
    print '{}'.format(arr)
