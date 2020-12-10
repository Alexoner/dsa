## su
`su` - run a command with substitute user and group ID.

OPTIONS
```text
		-, -l, --login
              Start the shell as a login shell with an environment similar to a real login:

                 o      clears all the environment variables except TERM and variables specified by --whitelist-environment

                 o      initializes the environment variables HOME, SHELL, USER, LOGNAME, and PATH

                 o      changes to the target user's home directory

                 o      sets argv[0] of the shell to '-' in order to make the shell a login shell
		-c, --command=command
			 Pass command to the shell with the -c option.
```
## sudo
sudo, sudoedit — execute a command as another user

OPTIONS
     -E, --preserve-env
                 Indicates to the security policy that the user wishes to preserve their existing environment variables.  The security policy may return an error if the user does not have permission to preserve the environment.

