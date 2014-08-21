# -*- coding:utf-8 -*-*


class FA(object):

    """Docstring for FA. """

    def __init__(self):
        """@todo: to be defined1. """
        pass

    def finite_automata_matcher(self, T, delta, m):
        """@todo: Docstring for finite_automata_matcher.

        Time Complexity:O(n)
        :text: input text
        :delta:transition function
        :m: the only accepted state
        :returns: @todo

        """
        n = len(T)
        q = 0
        for i in range(n):
            q = delta[q][T[i]]
            if q == m:
                print "Pattern occurs at shift {}".format(i - m + 1)

    def compute_transition_function(self, P, sigma):
        """
        :pattern: given pattern
        :input_alphabet: input alphabet

        """
        m = len(P)
        # delta:transition funciton
        delta = [[0 for i in range(sigma)] for j in range(m)]
        for q in range(m):
            for a in sigma:
                k = min(m + 1, q + 2)
                k = k - 1
                while not self.is_suffix_of(P[0:k], P[0:q] + a):
                    k = k - 1
                delta[q][a] = k
        return delta

    def is_suffix_of(self, suffix, text):
        l1 = len(suffix)
        l2 = len(text)
        dl = l2 - l1
        if l1 > l2:
            return False
        if l1 == 0:
            return True
        for i in xrange(l1):
            if suffix[i] != text[i + dl]:
                return False

        return True

    def kmp_matcher(self, T, P):
        """
        Time Complexity:O(n)
        text:input text
        pattern: pattern text

        KMP algorithm avoids the explicit computation of the
        transition function DELTA altogether.
        pi[q] is the length of the longest prefix of P that is a proper
        suffix of P[0]...P[q]
        """
        n = len(T)
        m = len(P)

        # prefix function
        pi = self.compute_prefix_function(P)
        q = 0  # match length
        for i in range(n):
            while q > 0 and P[q] != T[i]:
                q = pi[q - 1]
            if P[q] == T[i]:
                q = q + 1
            if q == m:
                q = pi[q - 1]
                print "Pattern occurs with shift {}".format(i - m + 1)

    def compute_prefix_function(self, P):
        """
        Time Complexity:O(m)
        Prefix function has the property of recurrence.
        """

        m = len(P)
        pi = [0 for i in range(m)]
        k = 0  # the match length
        for q in range(1, m, 1):
            while k > 0 and P[k] != P[q]:
                k = pi[k - 1]
            if P[k] == P[q]:
                k = k + 1
            pi[q] = k

        return pi

if __name__ == "__main__":
    fa = FA()
    fa.kmp_matcher("ABABDABACDABABCABAB", "ABABCABAB")
    fa.kmp_matcher("AABAACAADAABAAABAA", "AABA")
    fa.kmp_matcher("THIS IS A TEST TEXT", "TEST")
