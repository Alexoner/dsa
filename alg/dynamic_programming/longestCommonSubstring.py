def longest_common_substring(s1, s2):
    m = [[0] * (1 + len(s2)) for i in xrange(1 + len(s1))]
    longest, x_longest = 0, 0
    for x in xrange(1, 1 + len(s1)):
        for y in xrange(1, 1 + len(s2)):
            if s1[x - 1] == s2[y - 1]:
                m[x][y] = m[x - 1][y - 1] + 1
                if m[x][y] > longest:
                    longest = m[x][y]
                    x_longest = x
            else:
                m[x][y] = 0
    return s1[x_longest - longest: x_longest]


class Solution:

    def longestCommonSubstring(self, query, text):
        table = [[0 for i in xrange(len(text) + 1)]
                 for j in xrange(len(query) + 1)]
        length = 0
        end = 0
        for x in xrange(1, 1 + len(query)):
            for y in xrange(1, 1 + len(text)):
                if query[x - 1] == text[y - 1]:
                    table[x][y] = table[x - 1][y - 1] + 1
                    if table[x][y] > length:
                        length = table[x][y]
                        end = x
                else:
                    table[x][y] = 0

        return query[end - length:end]

    def longestCommonSubstring2(self, query, text):
        table = [[0 for i in xrange(len(text) + 1)]
                 for j in xrange(len(query) + 1)]
        length = 0
        # end = 0
        for x in xrange(1, 1 + len(query)):
            for y in xrange(1, 1 + len(text)):
                if query[x - 1] == text[y - 1]:
                    table[x][y] = table[x - 1][y - 1] + 1
                    # end = x
                else:
                    table[x][y] = max(table[x - 1][y], table[x][y - 1])
                if table[x][y] > length:
                    length = table[x][y]

        return length


if __name__ == "__main__":
    print Solution().longestCommonSubstring("acbac", "acaccbabb")
    print Solution().longestCommonSubstring2("acbac", "acaccbabb")
    # print longest_common_substring("acbac", "acaccbabb")
