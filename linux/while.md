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

	# heredoc piped into while loop for read like this
    IFS=" " cat <<-EOF |
    1 2 3 4 
    5 6 7 8
	EOF
	while read a b c d
		do echo $a,$b,$c,$d
    done | parallel echo "processing {}"

### Examples

Find which pip package contains a certain file:

    pip list |awk '{print $1}' |while read f
	do
		echo $f
		pip show -f $f |grep 'filename'
	done
