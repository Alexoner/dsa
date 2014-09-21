/*
 * Topological Sorting
 *
 * Topological sorting for Directed Acyclic Graph (DAG) is a linear
 * ordering of vertices such that for every directed edge uv, vertex u
 * comes before v in the ordering. Topological Sorting for a graph is not
 * possible if the graph is not a DAG.
 * For example, a topological sorting of the following graph is
 * “5 4 2 3 1 0″.
 * There can be more than one topological sorting for a graph. For example,
 * another topological sorting of the following graph is “4 5 2 3 1 0″. The
 * first vertex in topological sorting is always a vertex with in-degree
 * as 0 (a vertex with no
 * in-coming edges).
 *
 * graph
 *
 * Topological Sorting vs Depth First Traversal (DFS):
 * In DFS, we print a vertex and then recursively call DFS for its adjacent
 * vertices. In topological sorting, we need to print a vertex before its
 * adjacent vertices. For example, in the given graph, the vertex ’5′
 * should be printed before vertex ’0′, but unlike DFS, the vertex ’4′
 * should also be printed before vertex ’0′. So Topological sorting is
 * different from DFS. For example, a DFS of the above graph is
 * “5 2 3 1 0 4″, but it is not a topological sorting
 *
 * Algorithm to find Topological Sorting:
 * We recommend to first see implementation of DFS here. We can modify DFS
 * to find Topological Sorting of a graph. In DFS, we start from a vertex,
 * we first print it and then recursively call DFS for its adjacent
 * vertices. In topological sorting, we use a temporary stack. We don’t
 * print the vertex immediately, we first recursively call topological
 * sorting for all its adjacent vertices, then push it to a stack. Finally,
 * print contents of stack. Note that a vertex is pushed to stack only when
 * all of its adjacent vertices (and their adjacent vertices and so on)
 * are already in stack.
 *
 * Topological Sorting:Sorting by DFS finishing time stamp!
*/

// A C++ program to print topological sorting of a DAG
#include <iostream>
#include <list>
#include <stack>

using namespace std;

// Class to represent a graph
class Graph
{
    int V; // No. of vertices

    // Pointer to an array containing adjacency lists List
    list<int> *adj;

    // A function used by topologicalSort
    void topologicalSortUtil(int v, bool visited[], stack<int> &stack);

  public:
    Graph(int V); // constructor

    // function to add an edge to graph
    void addEdge(int v, int w);

    // prints a Topological Sort of the complete graph
    void topologicalSort();
};

Graph::Graph(int V)
{
    this->V = V;
    adj = new list<int>[V];
}

void Graph::addEdge(int v, int w)
{
    adj[v].push_back(w); // Add w to v's adj list.
}

// A recursive function used by toplogicalSort
void Graph::topologicalSortUtil(int v, bool visited[], stack<int> &Stack)
{
    // Mark the current node as visited
    visited[v] = true;

    // Recur for all the vertices adjancent to this vertex
    list<int>::iterator i;
    for (i = adj[v].begin(); i != adj[v].end(); ++i)
        if (!visited[*i])
            topologicalSortUtil(*i, visited, Stack);

    // Push current vertex to stack which stores result
    Stack.push(v);
}

// the function to do topological sort,
void Graph::topologicalSort()
{
    stack<int> Stack;

    // Mark all the vertices as not visited
    bool *visited = new bool[V];
    for (int i = 0; i < V; i++)
        visited[i] = false;

    // Call the recursive helper function to store Topological sort
    // starting from all vertices one by one
    for (int i = 0; i < V; i++)
        if (visited[i] == false)
            topologicalSortUtil(i, visited, Stack);

    // print contents of stack
    while (Stack.empty() == false)
    {
        cout << Stack.top() << " ";
        Stack.pop();
    }
}

// driver program
int main()
{
    // Create a graph given in the above diagram
    Graph g(6);
    g.addEdge(5, 2);
    g.addEdge(5, 0);
    g.addEdge(4, 0);
    g.addEdge(4, 1);
    g.addEdge(2, 3);
    g.addEdge(3, 1);

    cout << "Following is a Topological Sort of the given graph \n";
    g.topologicalSort();

    return 0;
}
