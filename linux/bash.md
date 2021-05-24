
# bash

## flags
-c        If the -c option is present, then commands are read from the first non-option argument command_string.
-l        Make bash act as if it had been invoked as a login shell (see INVOCATION below).

### read from command string

	bash -c "command here"
	bash -o pipefail -c "echo hello |tee a b"

### verbose

	set -x

### exit on error

	set -e
	set +e  # turn -e off
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

## common use cases

### wait until a file exists
https://superuser.com/questions/878640/unix-script-wait-until-a-file-exists

	wait_file() {
	  local file="$1"; # shift # shift is a bash built-in which kind of removes arguments from the beginning of the argument list
	  local wait_seconds="${2:-10}"; # shift # 10 seconds as default timeout

	  until test $((wait_seconds--)) -eq 0 -o -e "$file" ; do sleep 1; done

	  ((++wait_seconds))
	}

	# Wait at most 5 seconds for the server.log file to appear
	server_log=/var/log/jboss/server.log
	wait_file "$server_log" 5 || {
	  echo "JBoss log file missing after waiting for $? seconds: '$server_log'"
	  exit 1
	}

