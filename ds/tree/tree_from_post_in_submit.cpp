/* Tree node structure
struct Node 
{
   int data;
   struct Node *left, *right;
}*/

// Function should construct tree and return
// root of it.  in[] stores inorder traversal
// post[] stores postorder traversal.  n is
// size of these arrays
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
    // NOTE: need to allocate memory on heap instead of stack
    Node* root = node(rootData, (Node*)0, (Node*)0);
    int i = 0;
    for (i = 0; i < n && in[i] != rootData; ++i)
        ;
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
    if (tree) {
        std::cout << tree->data << " ";
        preorder(tree->left);
        preorder(tree->right);
    }
}

// TODO: non-recursive (iterative) algorithm here

Node* buildTree(int in[], int post[], int n)
{
    // Your code here
    Node* tree = buildTreeRecursive(in, post, n);
    //preorder(tree);
    //std::cout << "\n";
    return tree;
}
