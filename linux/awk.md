# awk - pattern scanning and processing language
A versatile programming language.

Execution order

Refer to:
- man page `man awk`
- [tutorialspoint](https://www.tutorialspoint.com/awk/awk_workflow.htm)
- [linuxhandbook](https://linuxhandbook.com/awk-command-tutorial/)
- [An intro to the great language with the strange name](https://www.ibm.com/developerworks/library/l-awk1/index.html)

![image](./data/awk_workflow.jpg)


For each input file, if a BEGINFILE rule exists, gawk executes the associated code before processing
the contents of the file. Similarly, gawk executes the code associated with ENDFILE after processing the file.

For each RECORD in the input, gawk TESTS to see if it matches any PATTERN in the AWK program.
For each pattern that the record matches, gawk executes the associated action.
The patterns are tested in the order they occur in the program.

Finally, after all the input is exhausted, gawk executes the code in the END rule(s) (if any).

## options

- -F, --field-separator fs. Use fs for the input field separator (the value of the FS predefined variable).

## variables

Records
: normally records are separated by new line characters, which can be controlled with variable `RS`, by assigning single character or regular expression.

Fields
: controlled by `FS`, default to be white spaces. 
Each field in the input record may be referenced by its position: `$1`, `$2`, and so on `$n`.  `$0` is the whole record, including leading and trailing whitespace.

### builtin Variables
- `$n`: bulitin variables - extract field, where n is a number starting with 1. `n=0` means the entire record.
- `RS`: record separator
- `FS`: field separator
- `NF`: number of fields in the current input record
- `NR`: number of input Records seen so far, starting with 1. if RS is set to the empty string, then records are separated by sequences consisting of a `<newline>` plus one or more blank lines.
- x: any variable defined by user

Using arrays
All arrays in AWK are `ASSOCIATIVE ARRAYS`, so they allow associating an arbitrary string with another value

## operators

- `$` field reference
- `~ !~` regular expression match: `$0 ~ expression`

## I/O statement

- `print` print the current record
- `next` stop processing the current input.

## functions

- `match(s, r [, a])`       Return the position in s where the regular expression r occurs. `a` is cleared and then elements 1 through  n are  filled  with  the portions of s that match the corresponding `parenthesized subexpression` in r.  The `zero'th` element of a contains the portion of s matched by the entire regular expression r.  Subscripts `a[n, "start"]`, and `a[n, "length"]` provide the starting index in the string and length respectively, of each matching substring.
- `gsub(r, s [, t])`        For  each  substring matching the regular expression `r` in the string `t`, substitute the string `s`, and return the number of substitutions.  If `t` is not supplied, use `$0`.

## regular expression

...

## Examples

    # PRINT first and last field of each line, separated by ','
    $ cat input | awk '{print $1, $NF}'

    # PRINT second-to-last column
    echo 'a b c d'|awk '{print $1, $(NF-1)}'

    # print first n
    cat input |awk '{if (NR>N) next; print $0}'

    # awk print from nth to last column (removing leading space), removing first, second columns
    echo 'a b c d' | awk '{$1=$2=$3="";print $0}' |sed -r 's/^\s+//g'

    # FORMAT PRINT
    $ echo 1 2 | awk '{printf "input is %s and %s", $1, $2}'
    input is 1 and 2

    # REGULAR EXPRESSION MATCHING and array accumulate
    $ echo "input: 1;\ninput: 2;\ninput: 3;" |awk 'match($0, /input: ([^;]+)/, x){a[NR] += x[1]} END{printf "input is %s, %s, %s", a[1], a[2], a[3]}'
    $ echo "input: 1;\ninput: 2;\ninput: 3;" |awk '$0 ~ /input: ([^;]+)/{a[NR] += $2} END{printf "input is %s, %s, %s", a[1], a[2], a[3]}'
    $ echo "input: 1;\ninput: 2;\ninput: 3;" |awk '{if(match($0, /input: ([^;]+)/, x))a[NR] += x[1]} END{printf "input is %s, %s, %s", a[1], a[2], a[3]}'
    input is 1, 2, 3

    # CONDITIONAL STATEMENT: search for [zZ] pattern and filter duplicate
    $ awk '/[zZ]/ && !a[$2]++ {print $2}'
    # kill zombie process
    kill $(ps -A -ostat,ppid | awk '/[zZ]/ && !a[$2]++ {print $2}') # [zZ] for pattern, a[$2]++ to filter duplicate ppid.

    # access CAPTURED GROUP from line pattern
    $ echo "abcdefgh" | gawk 'match($0, /b(.*)e((f).+)/, a) {print a[1]"\t"a[2]}'
    cd    f
    # back reference
    $ echo abbc | awk '{ print gensub(/a(b*)c/, "Here are bees: \\1", "g", $1);}'
    Here are bees: bb

    # multiple variables assignment
    read -r a b c <<<$(echo 1 2 3) ; echo "$a|$b|$c"
    # process a csv file, copy all files at the first field, and substitue destination name by replacing pattern with target
    $ cat feature.3030.csv|awk '{FS=","}NR > 1 {print $1}' |while read f
    do
        cp -v $f  /tmp/features/$(basename $f|sed -r 's/pattern/target/g')
    done

    $ sum column 3
    cat input | awk 'BEGIN{a=0}{a+=$3}END{print "sum is: ", a}'

    # REPLACE string but SKIP first line with CONDITIONAL STATEMENT
    $ echo -e "This is first line.\nThis is PATTERN1. END" | awk 'NR==1{print}NR>1{sub(/PATTERN1/,"PATTERN2");print}'
    This is first line.
    This is PATTERN2. END

    # generate a tabular separated value file: prepend a header line, sort by columns 1 and 2 numerically
    # NOTE: sort will skip first header line.
    $ cat input.txt | awk 'BEGIN{print "col1\tcol2\tcol3\tcol4"} {print $1"\t"$2"\t"$3"\t"$4 | "sort -k 1,1n -k 2,2n"}'

    # ignore first two lines and sort with awk
    cat input.txt | awk 'NR<3{print $0;next}{print $0| "sort -r"}' 

    # SET operation
    # generate Cartesian product of two files
    $ awk 'NR==FNR {a[$0]; next}{for (i in a) print i"\t"$0}' file1.txt file2.txt

    # get elements in file 1 excluding elements in file 2
    $ awk 'NR==FNR {a[$0] = 1; next} a[$0] == 0 {print $0}' file2.xt file1.txt

    # join two files row wise
    awk 'NR==FNR {a[NR] = $0; next}{print a[FNR]"\t"$0}' file1.txt file2.txt


