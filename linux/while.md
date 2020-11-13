### while 

    # keep testing until fail
    while true; do ./program || break; done # keep running a program until fail

    # heredoc piped into while read
    # heredoc with indentation of tab, piped into while, split string with IFS
    IFS=" " cat <<-EOF | while read a b c d
    1 2 3 4 
    5 6 7 8
    EOF
    do echo $a,$b,$c,$d
    done | parallel echo "processing {}"


