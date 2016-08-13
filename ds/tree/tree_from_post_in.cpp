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

void traversePre(Node* tree)
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
        traversePre(tree->left);
        traversePre(tree->right);
    }
}

// TODO: non-recursive algorithm heee

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
    traversePre(tree);
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
