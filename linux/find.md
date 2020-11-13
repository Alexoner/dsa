#### find

    find . -regextype posix-extended -regex '.*(perftest|unittest|ficus)' -type f |parallel rm -v {} # delete files with name matching regex
    find . -type f -regextype posix-extended -regex '.*\.(h|hpp|cpp|cxx)' # search for files with names matching regular expression
    find src -type f -regextype posix-extended -regex '.*\.(h|hpp|cpp|cxx)' | while read f; do ln -sfv /mnt/disk/hdu/$f /mnt/disk/jacksp/src_cpu/${f:6} ; done # symbol link all source files to another directory
    find . -maxdepth 1 -iname '*namepattern'

