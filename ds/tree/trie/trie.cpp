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

    Trie()
    {
        this->root = new TrieNode();
        this->count = 0;
    }

    void insert(const char *key);
    bool search(const char *key);
    void deleteKey(const char key[]);
    static bool deleteRecursion(struct TrieNode *pCrawl, const char key[], int level);
    static bool deleteIteration(struct Trie *pTrie, const char key[]);
    // TODO: keys that start with
    char* startsWith(const char *key);

    static bool hasChild(struct TrieNode *trieNode, char ch);
    static int numberOfChildren(struct TrieNode *trieNode);
    static bool hasBranches(struct TrieNode *trieNode);

};

// If not present, inserts key into trie
// If the key is prefix of trie node, just marks leaf node
void Trie::insert(const char* key)
{
    int level;
    int length = strlen(key);
    int index;

    TrieNode* pCrawl = this->root;
    printf("INSERT %s\n", key);
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

bool Trie::search(const char* key)
{
    int level;
    int length = strlen(key);
    int index;
    TrieNode* pCrawl = this->root;

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

bool Trie::hasChild(struct TrieNode *trieNode, char ch)
{
    return trieNode && trieNode->children[CHAR_TO_INDEX(ch)];
}

int Trie::numberOfChildren(struct TrieNode *trieNode)
{
    if (!trieNode) {
        return false;
    }
    int i, j;
    for (i = 0, j = 0; i < ALPHABET_SIZE; ++i) {
        if (trieNode->children[i]) {
            j++;
        }
    }
    return j;
}

bool Trie::hasBranches(struct TrieNode *trieNode)
{
    return numberOfChildren(trieNode);
}

bool Trie::deleteRecursion(struct TrieNode *pCrawl, const char key[], int level)
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

    // key doesn't exist, so this child pointer to node is NULL
    if (!pCrawl) {
        return false;
    }
    int len = strlen(key);
    int index = CHAR_TO_INDEX(key[level]);
    bool eligible = false;

    // base case
    if (level == len) {
        // the leaf node has no branches, in which case it can be deleted
        if (pCrawl->isLeaf) {
            eligible = !hasBranches(pCrawl);
            // mark as not leaf to "softly" delete the key
            pCrawl->isLeaf = false;
        }
        // if the node is not leaf, then the key doesn't exist in the trie tree
    } else { // recursion
        bool childEligible = deleteRecursion(pCrawl->children[index], key, level + 1);
        if (childEligible) {
            FREE(pCrawl->children[index]);
            //printf("pCrawl->child: %d, char: %c, level: %d, len: %d\n",
                    //pCrawl->children[index] != NULL,key[level], level, len);
        }
        // current node is eligible to delete if and only if it's not leaf and has
        // no more children
        eligible = childEligible && !pCrawl->isLeaf && !numberOfChildren(pCrawl);
    }

    return eligible;
}

bool Trie::deleteIteration(struct Trie *pTrie, const char key[])
{
    // TODO: delete a key iteratively using stack data structure
    return true;
}

void Trie::deleteKey(const char key[])
{
    /**
     * Cut the TAIL. The tail is the longest path ending with an edge and is without branches
     *
     * Method 1: RECURSION
     * A node is eligible only if its descendants are eligible and this node is not
     * part of another key's nodes. Being part of some key means it's a leaf or has children.
     *
     * Method 2: ITERATION
     * A pointer p to keep track of last node that contains branches (multiple valid children).
     * Then we can: 1. mark the key's leaf node 2. delete pointer p's descendants till the leaf node.
     *
     */
    int len = strlen(key);

    printf("DELETE %s\n", key);
    if (len) {
        deleteRecursion(this->root, key, 0);
    }
    return;
}

// Driver
int main()
{
    // Input keys (use only 'a' through 'z' and lower case)
    char keys[][8] = { "the", "a", "there", "answer", "any",
        "by", "bye", "their", "she", "sells", "sea", "shore", "sheer", "apple", "apply" };
    char output[][32] = { "Not present in trie", "Present in trie" };

    struct Trie *pTrie = new Trie();
    // Construct tree
    unsigned long i;
    for (i = 0; i < ARRAY_SIZE(keys); i++) {
        pTrie->insert(keys[i]);
    }

    // search for different keys
    printf("%s --- %s\n", "the", output[pTrie->search("the")]);
    printf("%s --- %s\n", "these", output[pTrie->search("these")]);
    printf("%s --- %s\n", "their", output[pTrie->search("their")]);
    printf("%s --- %s\n", "thaw", output[pTrie->search("thaw")]);
    printf("%s --- %s\n", "by", output[pTrie->search("by")]);
    printf("%s --- %s\n", "bye", output[pTrie->search("bye")]);
    printf("%s --- %s\n", "she", output[pTrie->search("she")]);
    printf("%s --- %s\n", "sheer", output[pTrie->search("sheer")]);
    printf("%s --- %s\n", "apple", output[pTrie->search("apple")]);
    printf("%s --- %s\n", "apply", output[pTrie->search("apply")]);

    pTrie->deleteKey("she");
    printf("%s --- %s\n", "she", output[pTrie->search("she")]);
    printf("%s --- %s\n", "sheer", output[pTrie->search("sheer")]);

    pTrie->deleteKey("bye");
    printf("%s --- %s\n", "by", output[pTrie->search("by")]);
    printf("%s --- %s\n", "bye", output[pTrie->search("bye")]);

    pTrie->deleteKey("apple");
    printf("%s --- %s\n", "apple", output[pTrie->search("apple")]);
    printf("%s --- %s\n", "apply", output[pTrie->search("apply")]);

    return 0;
}
