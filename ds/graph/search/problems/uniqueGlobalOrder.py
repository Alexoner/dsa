#!/usr/bin/env python
# -*- coding: utf-8 -*-

"""
Given a list of lists, each list represents a local order of events.

Is there a unique global order of events?


Example:
Input: [e1, e2, e3], [e2], [e2, e4, e3].
Output: [e1, e2, e4, e3].

================================================================================
SOLUTION

1. Interval merging problem
Local order can be merged into global order, but the problem is some of lists
can not be merged directly. This is due to transitive relation.

Speaking of transitive relation, GRAPH data structure appears.

2. Graph problem

Model it as a graph problem.
Vertices are the events, and edges are the 'exact before' relation in the
local lists.

This looks like a topological order except that it requires unique ordering.

Then, the to verify whether there is such a unique global order, is to find a
Hamiltonian path(visiting every vertex exactly once) on the graph.

Path finding can be solved by DEPTH FIRST SEARCH or breadth first search.

And the start vertex must be the one with 0 in-degree.

The adjacency list represented graph of the example:

1: 2
2: 3, 4
3:
4: 3

Then such Hamiltonian path is: 1->2->4->3.

Note, if there is a CYCLE, definitely there is no solution!

"""

# TODO: implementation

from collections import defaultdict, Counter

def findOrder(events):
    # build graph
    adj = defaultdict(list)
    # adj = {}
    indegree = Counter()
    for localOrder in events:
        for i in range(len(localOrder)):
            if i < len(localOrder) - 1:
                adj[localOrder[i]].append(localOrder[i + 1])
                indegree[localOrder[i + 1]] += 1
            else:
                adj[localOrder[i]] = []
                indegree[localOrder[i]] = 0
    visited = set()

    # total number of vertices?
    for v in indegree:
        pass

    # find start vertex
    start = None

    def dfs(u):
        for v in adj[u]:
            if v in visited: continue
            pass
        pass

    path = []
    dfs(start)
    return path
