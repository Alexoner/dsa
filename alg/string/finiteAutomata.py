# -*- coding:utf-8 -*-*


class FA(object):

    """Docstring for FA. """

    def __init__(self):
        """@todo: to be defined1. """
        pass

    def finite_automata_matcher(self, text, tf, m):
        """@todo: Docstring for finite_automata_matcher.

        :text: input text
        :tf:transition functio
        :m: the only accepted state
        :returns: @todo

        """
        n = len(text)
        q = 0
        for i in range(n):
            q = tf[q][text[i]]
            if q == m:
                print "Pattern occurs at shift {}".format(i - m + 1)

    def compute_transition_function(self, pattern, input_alphabet):
        """
        :pattern: given pattern
        :input_alphabet: input alphabet

        """
        m = len(pattern)
        tf = [[0 for i in range(input_alphabet)] for j in range(m)]
        for q in range(m):
            for a in input_alphabet:
                k = min(m + 1, q + 2)
                k = k - 1
                while not self.is_suffix_of(pattern[0:k], pattern[0:q] + a):
                    k = k - 1
                tf[q][a] = k
        return tf
