/*
 * Lowest common ancestor
 *
 * In graph theory and computer science,the lowest common ancestor(LCA) of
 * two nodes v and w in a tree or directed acyclic graph(GAD) is the lowest
 * (i.e. deepest) node that has both v and w as descendants,where define
 * each node to be a descendant of itself.
 *  The LCA of n1 and n2 in T is the shared ancestor of n1 and n2 that is
 * located farthest from the root.It's also known as the least common
 * subsumer.
 *
 * Algorithm:
 */

/*
 *  Method 1
 *  Storing root to n1 and root to n2 paths.
 *  Time Complexity:O(n),Space Complexity: O(n).
 *
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

// binary tree node
struct Node
{
    struct Node *left, *right;
    int key;
};

struct Node *newNode(int key)
{
    struct Node *p = (struct Node *)malloc(sizeof(struct Node));
    p->key = key;
    p->left = p->right = NULL;

    return p;
}

/*
 *  Method 2
 * The idea is to traverse the tree starting from root. If any of the given
 * keys (n1 and n2) matches with root, then root is LCA (assuming that both
 * keys are present). If root doesn’t match with any of the keys, we recur
 * for left and right subtree. The node which has one key present in its
 * left subtree and the other key present in right subtree is the LCA. If
 * both keys lie in left subtree, then left subtree has LCA also, otherwise
 * LCA lies in right subtree.
 */
struct Node *findLCA(struct Node *root, int a, int b)
{
    // Base case
    if (root == NULL)
        return NULL;

    // either a or b matches with root's key,report the presence by
    // returning root
    if (root->key == a || root->key == b)
        return root;

    // Look for keys in left and right subtrees
    struct Node *left_lca = findLCA(root->left, a, b);
    struct Node *right_lca = findLCA(root->right, a, b);

    // If both of the above calls return Non-NULL, then one key
    // is present in once subtree and other is present in other,
    // So this node is the LCA
    if (left_lca && right_lca)
        return root;

    // otherwise determine either left or right subtree is LCA
    return left_lca ? left_lca : right_lca;
}

int main()
{
    // build a binary tree
    struct Node *root = newNode(1);
    root->left = newNode(2);
    root->right = newNode(3);
    root->left->left = newNode(4);
    root->left->right = newNode(5);
    root->right->left = newNode(6);
    root->right->right = newNode(7);

    printf("LCA(4,5)= %d\nLCA(4,6)= %d\nLCA(3,4)= %d\nLCA(2,4)= %d\n",
           findLCA(root, 4, 5)->key, findLCA(root, 4, 6)->key,
           findLCA(root, 3, 4)->key, findLCA(root, 2, 4)->key);

    return 0;
}
