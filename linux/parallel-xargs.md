Parallel processing
-------------------
- Use GNU/parallel or xargs command.
- Use wait built-in command with &.
- Use xargs command.

### background task with `&`

    prog1 &
    prog2 &
    wait
    prog3

###  `parallel`
Refer to `man parallel_tutorial`

    # use ::: to input data
    $ parallel --no-notice echo {} ::: A B C
    A
    B
    C

    # PIPE data into parallel
    $ echo -e 'a\nb\nc'  |parallel --no-notice echo processed {}
    processed a
    processed b
    processed c

    $ parallel echo {} ::: A B C ::: D E F
    A D
    A E
    A F
    B D
    B E
    B F
    C D
    C E
    C F

    # want to copy files parallely? rsync -R for relative to keep file hierarchy
    $ find src/ -not -path .git |parallel rsync -avPR {} dst/

- `{}` for replacement string(placeholder)

### `xargs`
Sequentially execute batch tasks.

    $ ls
    A B C
    $ find . -type f |xargs -I {} echo "Found {}"
    Found A
    Found B
    Found C
    $ find . -type f -exec echo 'Found {}' \;
    Found A
    Found B
    Found C
    $ # find . -type f |xargs -I {} sed -i -r 's/pattern/target/g' |awk ...

- `-I replace-str`: replace occurrences of string `replace-str` with names read from standard input. 

### `find`

    # https://stackoverflow.com/questions/602706/batch-renaming-files-with-bash
    find . -type f |sed -n -r 's/(.+)pattern(.+)/mv \1pattern\2 \1target\2/p' |sh # batch renaming multiple files


