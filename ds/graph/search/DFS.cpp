/*
 * Depth First Traversal for Graph
 *
 * Depth First Traversal (or Search) for a graph is similar to Depth First
 * Traversal of a tree. The only catch here is, unlike trees, graphs may
 * contain cycles, so we may come to the same node again. To avoid
 * processing a node more than once, we use a boolean visited array.
 * For example, in the following graph, we start traversal from vertex 2.
 * When we come to vertex 0, we look for all adjacent vertices of it. 2 is
 * also an adjacent vertex of 0. If we don’t mark visited vertices, then 2
 * will be processed again and it will become a non-terminating process.
 * Depth First Traversal of the following graph is 2, 0, 1, 3
*/

#include <iostream>
#include <list>
#include <stack>

using namespace std;

class Graph
{
    int V;          // NO. of vertices
    list<int> *adj; // Pointer to an array containing adjacency lists
    void DFSVisit(int v, bool visited[]);
    void DFSIterative(int v, bool visited[]);

  public:
    Graph(int V);               // Constructor
    void addEdge(int v, int w); // function to add an edge to graph
    void DFS(bool iterative);   // prints DFS traversal of the complete graph
};

Graph::Graph(int V) : V(V)
{
    this->V = V;
    adj = new list<int>[V];
}

void Graph::addEdge(int v, int w)
{
    adj[v].push_back(w);
}

void Graph::DFSVisit(int v, bool visited[])
{
    // Mark the current node as visited and print it
    visited[v] = true;
    cout << v << " ";

    // Recur for all the vertices adjacent to this vertex
    list<int>::iterator i;
    for (i = adj[v].begin(); i != adj[v].end(); i++)
        if (!visited[*i])
            DFSVisit(*i, visited);
}

// The function to do DFS traversal.It uses recursive DFSVisit()
// Time Complexity:O(V+E)
void Graph::DFS(bool iterative)
{
    // Mark all the vertices as not visited
    bool *visited = new bool[V];
    for (int i = 0; i < V; i++)
        visited[i] = false;

    // Call the recursive helper function to print DFS traversal
    // starting from all vertices one by one
    for (int i = 0; i < V; i++)
        if (!visited[i]) {
            if (iterative) {
                DFSIterative(i, visited);
            } else {
                DFSVisit(i, visited);
            }
        }
}


// iterative depth-first search all vertices reachable from 'v',
// implemented with stack
void Graph::DFSIterative(int v, bool visited[])
{
    // iteratively depth-first search
    // initialize the stack
    stack<int> stack;
    stack.push(v);
    visited[v] = true;

    // 'i' will be used to get all adjacent vertices
    // of a vertex
    list<int>::iterator i;

    while(!stack.empty()) {
        // Pop a vertex from stack and mark it visited, print it
        int vertex = stack.top();
        visited[vertex] = true;
        cout << vertex << " ";
        stack.pop();

        // Get all adjacent vertices of the popped vertex s
        // If a adjacent has not been visited, then push it to the stack
        for(i = adj[vertex].begin(); i != adj[vertex].end(); ++i) {
            if (!visited[*i]) {
                stack.push(*i);
            }
        }
    }

}

int main()
{
    // Create a graph given in the above diagram
    Graph g(4);
    g.addEdge(0, 1);
    g.addEdge(0, 2);
    g.addEdge(1, 2);
    g.addEdge(2, 0);
    g.addEdge(2, 3);
    g.addEdge(3, 3);

    cout << "RECURSION. Following is Depth First Traversal (starting from vertex 2)\n";
    g.DFS(false);
    cout << "\nITERATION. Following is Depth First Traversal (starting from vertex 2)\n";
    g.DFS(true);

    return 0;
}
