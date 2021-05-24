# Here document(heredoc)

## Introduction

    In computing, a here document (here-document, here-text, heredoc, hereis, here-string or here-script) is a file literal or input stream literal: it is a section of a source code file that is treated as if it were a separate file. The term is also used for a form of multiline string literals that use similar syntax, preserving line breaks and other whitespace (including indentation) in the text.

    In POSIX shell but not csh/tcsh, appending a minus sign to the << (i.e. <<-) has the effect that leading tabs are ignored. This allows indenting here documents in shell scripts (primarily for alignment with existing indentation) without changing their value:

## Format

For file literal format is

    [n]<<[-]word
            here-document
    delimiter

    [n]<<[-]"word"
            here-document
    delimiter


Specification:

    No parameter and variable expansion, command substitution, arithmetic expansion, or filename expansion is performed on word. If any part of word is quoted, the delimiter is the result of quote removal on word, and the lines in the here-document are not expanded. If word is unquoted, all lines of the here-document are subjected to parameter expansion, command substitution, and arithmetic expansion, the character sequence \newline is ignored, and ‘\’ must be used to quote the characters ‘\’, ‘$’, and ‘`’.

    If the redirection operator is '<<-', then all leading tab characters are stripped from input lines and the line containing delimiter. This allows here-documents within shell scripts to be indented in a natural fashion.


## Common usage

``` shell

# cat with heredoc
$ cat << EOF
> \$ Working dir "$PWD" `pwd`
> EOF
$ Working dir "/home/user" /home/user``shell

# pipe with heredoc
IFS=" " cat <<-EOF|
1 2 3 4
5 6 7 8
		EOF
while read a b c d
do
  echo $a $b $c $d
done |
parallel echo "processing {}"

```

## Reference
https://en.wikipedia.org/wiki/Here_document

https://www.gnu.org/savannah-checkouts/gnu/bash/manual/bash.html#Here-Documents
