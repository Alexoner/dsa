/*
 *
 * Trie is an efficient information retrieval data structure. Using trie, search complexities can be brought to optimal limit (key length). If we store keys in binary search tree, a well balanced BST will need time proportional to M * log N, where M is maximum string length and N is number of keys in tree. Using trie, we can search the key in O(M) time. However the penalty is on trie storage requirements.

Every node of trie consists of multiple branches. Each branch represents a possible character of keys. We need to mark the last node of every key as leaf node. A trie node field value will be used to distinguish the node as leaf node (there are other uses of the value field).
 *                     root
                    /   \    \
                    t   a     b
                    |   |     |
                    h   n     y
                    |   |  \  |
                    e   s  y  e
                 /  |   |
                 i  r   w
                 |  |   |
                 r  e   e
                        |
                        r
 *
 * Insert and search costs O(key_length), however the memory requirements of trie is O(ALPHABET_SIZE * key_length * N) where N is number of keys in trie. There are efficient representation of trie nodes.
 *
 * During delete operation we delete the key in bottom up manner using recursion. The following are possible conditions when deleting key from trie,
    1. Key may not be there in trie. Delete operation should not modify trie.
    2. Key present as unique key (no part of key contains another key (prefix), nor the key itself is prefix of another key in trie). Delete all the nodes.
    3. Key is prefix key of another long key in trie. Unmark the leaf node.
    4. Key present in trie, having atleast one other key as prefix key. Delete nodes from end of key until first leaf node of longest prefix key.
 */

#include <stdio.h>
#include <string.h>
#include <stdlib.h>

#define ARRAY_SIZE(a) sizeof(a) / sizeof(a[0])

// Alphabet size (# of symbols)
#define ALPHABET_SIZE (26)

// Converts key current character into index
// use only 'a' through 'z' and lower case
#define CHAR_TO_INDEX(c) ((int)c - (int)'a')

#define FREE(p) \
    free(p);    \
    p = NULL;

// trie node
struct TrieNode {
    struct TrieNode* children[ALPHABET_SIZE];
    // isLeaf is true if the node represents end of a word
    bool isLeaf;

    TrieNode(void)
    {
        //struct TrieNode *pNode = (struct TrieNode*)malloc(sizeof(struct TrieNode));
        this->isLeaf = false;
        for (int i = 0; i < ALPHABET_SIZE; ++i) {
            this->children[i] = NULL;
        }
    }
};

// trie tree abstract data type
struct Trie {
    struct TrieNode* root;
    int count;

    Trie(TrieNode* root)
    {
        this->root = root;
        this->count = 0;
    }
};

// If not present, inserts key into trie
// If the key is prefix of trie node, just marks leaf node
void insert(TrieNode* root, const char* key)
{
    int level;
    int length = strlen(key);
    int index;

    TrieNode* pCrawl = root;
    for (level = 0; level < length; ++level) {
        index = CHAR_TO_INDEX(key[level]);
        if (!pCrawl->children[index]) {
            // use new to allocate memory from heap, otherwise from stack
            pCrawl->children[index] = new TrieNode();
        }
        pCrawl = pCrawl->children[index];
    }

    // mark last node as leaf
    pCrawl->isLeaf = true;
}

bool search(TrieNode* root, const char* key)
{
    int level;
    int length = strlen(key);
    int index;
    TrieNode* pCrawl = root;

    for (level = 0; level < length; ++level) {
        index = CHAR_TO_INDEX(key[level]);
        if (pCrawl->children[index]) {
            pCrawl = pCrawl->children[index];
        } else {
            break;
        }
    }

    return (level == length && pCrawl && pCrawl->isLeaf);
}

bool hasBranches(struct TrieNode *trieNode)
{
    if (!trieNode) {
        return false;
    }
    int i;
    for (i = 0; i < ALPHABET_SIZE && !trieNode->children[i]; ++i);

    return i != ALPHABET_SIZE;
}

bool hasChild(struct TrieNode *trieNode, char ch)
{
    return trieNode && trieNode->children[CHAR_TO_INDEX(ch)];
}

bool deleteRecursion(struct TrieNode *pCrawl, const char key[], int level)
{
    /*
     * params
     * @pCrawl: crawler pointer alongside the trie tree nodes
     * @key: a string key to delete
     * @level: the index of characters in key
     *
     * return:
     * bool, indicates whether the child node can be deleted in the key removing
     * process
     */
    if (!pCrawl) {
        return false;
    }
    int len = strlen(key);
    int index = CHAR_TO_INDEX(key[level]);
    bool eligible = false;

    // base case
    if (level == len) {
        // the leaf node has no branches, in which case it can be
        // deleted, and it's leaf
        if (pCrawl->isLeaf) {
            eligible = !hasBranches(pCrawl);
            // mark as not leaf to "softly" delete the key
            pCrawl->isLeaf = false;
        }
    } else { // recursion
        // key doesn't exist, so this child pointer to node is NULL
        bool childEligible = deleteRecursion(pCrawl->children[index], key, level + 1);
        if (childEligible) {
            FREE(pCrawl->children[index]);
            //printf("pCrawl->child: %d, char: %c, level: %d, len: %d\n",
                    //pCrawl->children[index] != NULL,key[level], level, len);
        }
        eligible = childEligible && !pCrawl->isLeaf;
    }

    return eligible;
}

void deleteIteration(struct Trie *pTrie, const char key[])
{
    return;
}

void deleteKey(struct Trie* pTrie, const char key[])
{
    /**
     * Cut the TAIL. The tail is the longest path ending with an edge and is without branches
     *
     * Method 1: RECURSION
     * A node is eligible only if its descendants are eligible and this node is not
     * one of another key's nodes.
     *
     * Method 2: ITERATION
     * A pointer p to keep track of last node that contains branches (multiple valid children).
     * Then we can: 1. mark the key's leaf node 2. delete pointer p's descendants till the leaf node.
     *
     */
    int len = strlen(key);

    if (len) {
        deleteRecursion(pTrie->root, key, 0);
    }
    return;
}

// Driver
int main()
{
    // Input keys (use only 'a' through 'z' and lower case)
    char keys[][8] = { "the", "a", "there", "answer", "any",
        "by", "bye", "their", "she", "sells", "sea", "shore", "sheer" };
    char output[][32] = { "Not present in trie", "Present in trie" };

    struct TrieNode *root = new TrieNode();
    struct Trie *pTrie = new Trie(root);
    // Construct tree
    unsigned long i;
    for (i = 0; i < ARRAY_SIZE(keys); i++) {
        insert(root, keys[i]);
        printf("inserted %s\n", keys[i]);
    }

    // search for different keys
    printf("%s --- %s\n", "the", output[search(root, "the")]);
    printf("%s --- %s\n", "these", output[search(root, "these")]);
    printf("%s --- %s\n", "their", output[search(root, "their")]);
    printf("%s --- %s\n", "thaw", output[search(root, "thaw")]);

    printf("%s %s\n", "she", search(root, "she") ? "Present in trie" : "Not present in trie");
    deleteKey(pTrie, "sheer");
    deleteKey(pTrie, "she");
    printf("%s %s\n", "she", search(root, "she") ? "Present in trie" : "Not present in trie");
    printf("%s %s\n", "sheer", search(root, "sheer") ? "Present in trie" : "Not present in trie");

    printf("%s %s\n", "by", search(root, "by") ? "Present in trie" : "Not present in trie");
    deleteKey(pTrie, "by");
    printf("%s %s\n", "by", search(root, "by") ? "Present in trie" : "Not present in trie");

    return 0;
}
