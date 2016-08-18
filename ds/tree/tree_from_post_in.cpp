#include <iostream>
//Tree node structure
struct Node {
    int data;
    struct Node *left, *right;
};

// Function should construct tree and return
// root of it.  in[] stores inorder traversal
// post[] stores postorder traversal.  n is
// size of these arrays

/*
 *
 *Given inorder and postorder traversals of a Binary Tree, construct the tree

For example, if given inorder and postorder traversals are {4, 8, 2, 5, 1, 6, 3, 7} and {8, 4, 5, 2, 6, 7, 3, 1}  respectively, then your function should construct below tree.

          1
       /      \
     2         3
   /   \      /  \
  4     5    6    7
    \
      8



Input:
The task is to complete the method which takes three arguments, one is an array that has inorder traversal, second is another array that has postorder traversal, third is size of two arrays (You may assume that both arrays are of same size).

There are multiple test cases. For each test case, this method will be called individually.

Output:
The function should return root of constructed tree.

Constraints:
1 <=T<= 30
1 <= Size of arrays <= 100
1 <= Values in arrays <= 1000

Example:
Input:
1
8
4 8 2 5 1 6 3 7
8 4 5 2 6 7 3 1


Output:
1 2 4 8 5 3 6 7



There is one test case.  The first line of input is number of elements in tree. Second and third lines are inorder and postorder traversals respectively.  Output is Preorder traversal.
 *
 */

/*
 *
 * ALGORITHM:
 *  1. Start from the root node which is explict in both pre-order and post-order
 *  traversal.
 *  2. Use the root node to split the traversed nodes, thus we can build the
 *  left and right children recursively.
 */

Node* node(int data, Node* left, Node* right)
{
    Node* node = new Node();
    node->data = data;
    node->left = left;
    node->right = right;
    return node;
}

Node* buildTreeRecursive(int in[], int post[], int n)
{
    int rootData = post[n - 1];
    //Node node = {
    //rootData,
    //(Node*)0,
    //(Node*)0
    //};
    //Node* root = &node;
    // NOTE: need to allocate memory on heap instead of stack
    Node* root = node(rootData, (Node*)0, (Node*)0);
    int i = 0;
    for (i = 0; i < n && in[i] != rootData; ++i)
        ;
    //std::cout << "root: " << i << "," << in[i] << " n: " << n << "\n";
    if (i && i < n) {
        root->left = buildTreeRecursive(in, post, i);
    }
    if (n - i - 1 > 0) {
        root->right = buildTreeRecursive(in + i + 1, post + i, n - i - 1);
    }
    return root;
}

void preorder(Node* tree)
{
    static int isRoot = 1;
    if (tree) {
        if (isRoot) {
            //std::cout << tree->data;
            std::cout << tree->data << " ";
        } else {
            std::cout << tree->data << " ";
        }
        isRoot = 0;
        preorder(tree->left);
        preorder(tree->right);
    }
}

// TODO: non-recursive (iterative) algorithm here

Node* buildTree(int in[], int post[], int n)
{
    // Your code here
    for (int i = 0; i < n; ++i) {
        std::cout << in[i] << " ";
    }
    std::cout << "\n";
    for (int i = 0; i < n; ++i) {
        std::cout << post[i] << " ";
    }
    std::cout << "\n";

    Node* tree = buildTreeRecursive(in, post, n);
    preorder(tree);
    std::cout << "\n";
    return tree;
}

int test()
{
    int n = 8;
    int in[] = { 4, 8, 2, 5, 1, 6, 3, 7 };
    int post[] = { 8, 4, 5, 2, 6, 7, 3, 1 };
    buildTree(in, post, n);
    int in2[] = { 2, 1, 3 };
    int post2[] = { 2, 3, 1 };
    buildTree(in2, post2, 3);

    return 0;
}

int main(int argc, char** argv)
{
    test();
    return 0;
}
