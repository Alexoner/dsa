#!/usr/bin/python2


class Graph:

    def __init__(self,vertices,edges):
        self.V = []     # list of vertex
        self.E = []     # list of edge,

        self.adj_mat = []   # adjacency matrix

        self.adj = []       # adjacency-list representation


    def DFS(G):
        '''
            Depth-first search.Recursion (Stack).
        '''
        for vertex in G.V:
            u.color = WHITE
            u.predecessor = None
        time = 0

        for vertex in G.V:
            if u.color == WHITE:
                DFS_VISIT(G, u)


    def DFS_VISIT(G, u):
        time = time + 1     # time stamp
        u.d = time          # discovery time
        u.color = GRAY      # GRAY:DFS visiting

        for v in G.adj[u]:
            if v.color == WHITE:    # WHITE: unvisited
                v.predecessor = u
                DFS_VISITT(G,v)

        # time stamp increased by 1,representing the finishing time
        u.color = BLACK     # BLACK: visited
        time = time + 1
        u.f = time          # finishing time
