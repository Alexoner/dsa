### sort

    $ cat input.txt
    3       tomato
    1       onion
    4       beet
    2       pepper
    2       apple

    $ cat input.txt | sort -k 1,1n -k 2,2h # sort by multiple columns
    2       apple
    2       pepper
    3       tomato
    4       beet
    10      onion

    $ cat input.txt | sort -k 1,1nr -k 2d,2 # column 1: numeric, reverse, column 2: dictionary

    10      onion
    4       beet
    3       tomato
    2       apple
    2       pepper

    $ cat input.txt | sort -k 1,1nr -k 2d,2r # column 1: numeric, reverse, column 2: dictionary, reverse
    10      onion
    4       beet
    3       tomato
    2       pepper
    2       apple

### uniq - report or omit repeated lines

It can be used to group or aggregate results.

    $ cat input.txt
    a
    c
    a
    c
    a
    b

    $ cat a.txt | sort |uniq -c  |sort -k1,1nr
    3 a
    2 b
    1 c

uniq -c, --count: prefix line by the number of occurrences



