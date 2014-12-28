#!/usr/bin/python2

import sys
import Queue


class Graph:

    def __init__(self, vertices, edges):
        self.V = []     # list of vertex
        self.E = []     # list of edge,

        self.adj_mat = []   # adjacency matrix

        self.adj = []       # adjacency-list representation


time = 0
ts_time = 0


def BFS(G, s):
    """
    Breadth-first search.
    QUEUE.
    """

    # initialization
    # for vertex in G.V:
    for u in G.V:
        u.color = WHITE
        u.d = sys.maxint
        u.predecessor = None

    s.color = GRAY
    s.d = 0

    Q = Queue.Queue()
    Q.put(s)

    # maintenance
    # Elements in the QUEUE are the ones that have NOT been processed
    # POP it out of the QUEUE and visit it,and PUSH its successors
    # into the queue
    while not Q.empty():
        u = Q.get()
        for v in G.adj[u]:
            if v.color == WHITE:
                v.color = GRAY
                v.d = u.d + 1
                v.predecessor = u
                Q.put(v)
        u.color = BLACK


def DFS(G):
    '''
        Depth-first search.
        Recursion (Stack).
    '''

    # Initialization
    for u in G.V:
        u.color = WHITE
        u.predecessor = None
    global time
    time = 0

    # Maintenance
    for u in G.V:
        if u.color == WHITE:
            DFS_VISIT(G, u)


def DFS_VISIT(G, u):
    time = time + 1     # time stamp
    u.d = time          # discovery time
    u.color = GRAY      # GRAY:DFS visiting

    for v in G.adj[u]:
        if v.color == WHITE:    # WHITE: unvisited
            v.predecessor = u
            DFS_VISITT(G, v)

    # time stamp increased by 1,representing the finishing time
    u.color = BLACK     # BLACK: visited
    time = time + 1
    u.f = time          # finishing time


def topological_sort(G):
    for u in G.V:
        u.color = WHITE
        u.predecessor = None
    global ts_time
    ts_time = 0
    sequence = []

    for u in G.V:
        if u.color == WHITE:
            ts_visit(G, u, sequence)


def ts_visit(G, u, sequence):
    ts_time = ts_time + 1
    u.d = ts_time
    u.color = GRAY

    for v in G.adj[u]:
        if v.color == WHITE:
            v.predecessor = u
            ts_visit(G, v)

    u.color = BLACK
    ts_time = ts_time + 1
    u.f = time
    sequence.insert(0, u)
