# SSH (secure shell)

## Common Usage
```shell
# execute command
ssh $user@$host 'echo hello'

# execute command from local shell script
ssh -t $user@$host 'bash -s' < local_script.sh

# execute command with sudo
#ssh -t $user@$host "sudo ls"

## execute command with bash heredoc ssh
ssh -t $user@$host bash <<EOF
	ls
	whoami
EOF

```
