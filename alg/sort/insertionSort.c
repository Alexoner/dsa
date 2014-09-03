
void insertionSort(int A[], int size)
{
    int i, key, j;
    for (i = 1; i < size; i++)
    {
        key = A[i];
        j = i - 1;

        /*Move elements of A[0..i-1],that are greater than key,to one
         * position ahead of their current position.
         */
        while (j >= 0 && A[j] > key)
        {
            A[j + 1] = A[j];
            j = j - 1;
        }
        A[j + 1] = key;
    }
}
