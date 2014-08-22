# -*- coding:utf-8 -*-
'''
Greatest Common Divisor,Euclid Algorithm
'''


class gcd(object):

    """gcd algorithm"""

    def __init__(self):
        """@todo: to be defined1. """
        pass

    def euclid(self, a, b):
        if b == 0:
            return a
        else:
            return self.euclid(b, a % b)

    def extended_euclid(self, a, b):
        """ extended gcd algorithm,returning the x,y,
        for which gcd(a,b) = ax + by
        """
        if b == 0:
            return (a, 1, 0)
        else:
            d1, x1, y1 = self.extended_euclid(b, a % b)
            d, x, y = d1, y1, x1 - (a / b) * y1
            return (d, x, y)

if __name__ == "__main__":
    print gcd().euclid(30, 21)
    print gcd().extended_euclid(99, 78)
