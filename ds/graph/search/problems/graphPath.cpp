/**
 *
 * Hamiltonian path problem or Euler Path?
 *
 * Euler Path is to visit every EDGE exactly once(like seven bridges problem).
 * Hamiltonian path is visiting every VERTEX exactly once.
 *
 * #############################################################################################
 * Google interview question:
 * 一堆密码箱，每个密码都是四位0-9之间，算一个暴力破解序列，包含所有可能的四位序列，让这个序列尽量短.
 *
 * =============================================================================================
 * SOLUTION
 *
 * The password has 10^4 possible combinations.
 *
 * In naive method, generate all possible combinations will enumerate all the possible cases.
 * But one password can transfer to another one by adding a digit.
 *
 * State transition is involved. Treat this as a graph problem.
 *
 * To construct the graph, we need to define proper state(vertex) and state transition(edges).
 *
 * 1) Each vertex is a 4 digits password combination, and each edge corresponds to a digit.
 * Then in this graph search problem, the objective is to visit all vertices, at least once.
 * Actually this is a Hamiltonian circuit.
 *
 * 2) Each vertex is a 3 digits combination, each edge is a 4 digit combination.
 * Then in this graph search problem, the objective is to visit all edges, at least once.
 * Then this is a Euler circuit. For example vertices "012", "123" connected by edge "0123".
 *
 * Euler circuit can be proven by considering in-dgrees and out-degrees of vertices.
 *
 * One problem: What if every digit has only odd possible values, like 1-9, is this Euler circuit?
 *
 * ---------------------------------------------------------------------------------------------
 * Similar problems:
 * https://en.wikipedia.org/wiki/De_Bruijn_sequence
 * https://en.wikipedia.org/wiki/Lyndon_word
 * http://poj.org/problem?id=1780
 *
 * Reference: http://www.geeksforgeeks.org/backtracking-set-7-hamiltonian-cycle/
 * http://www.1point3acres.com/bbs/forum.php?mod=redirect&goto=findpost&pid=2176735&ptid=166111
 *
 * ---------------------------------------------------------------------------------------------
 * 1. Brute force depth first search
 *
 * Define state:
 * 4 digit sequence, denoted by s.
 *
 * At each step, choose a possible digit to form a new 4 digit sequence s'. If s' is not visited
 * yet, add it to the queue and mark it as visited, increase the count of explored vertices by 1.
 *
 * One problem: if a vertex is restricted to being visited exactly once, then does it assure all
 * vertices will be visited? But if we don't limit that one vertex can be only visited once, then
 * there will be cycle in the graph, leading to infinite search.
 *
 * Answer: If we run into a dead end: not able to move on because all connected vertices of current
 * search frontier have been visited. Then it's essential to start search
 *
 * Problem: since we are trying to reach every vertex, is it possible to use breadth first search?
 * In bfs, we need to pass copies of state, to simulate the backtracking process in dfs, which
 * would require more memory.
 *
 * TODO: prove it
 *
 * 2. Iterative solution
 * dfs may explode the stack
 *
 *
 */
