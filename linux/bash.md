
# bash

## flags
-c        If the -c option is present, then commands are read from the first non-option argument command_string.
-l        Make bash act as if it had been invoked as a login shell (see INVOCATION below).

### read from command string

	bash -c "command here"
	bash -o pipefail -c "echo hello |tee a b"

### exit on error

	set -e
	bash -e

### login shell

	set -l
	bash -l

## bash options
### pipefail
Set the exit status `$?` to the exit code of last program to exit non-zero in a piped command.

	set -o pipefail
	bash -o pipefail


## variables

`$?` exit status code of last command.
`$@` all arguments.
`$1, $2, ..., ` 1, 2, 3nd argument.
