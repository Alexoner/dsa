### lsof

Options:

	-p PID
	-i i   select by IPv[46] address: [46][proto][@host|addr][:svc_list|port_list]

Examples:

    lsof -p $PID # list opened files by process with $PID
	lsof |grep $FILE # filter opened files/directories matching $FILE
	lsof |grep $DIRECTORY # filter opened files/directories matching $DIRECTORY
	lsof -u [user-name]

