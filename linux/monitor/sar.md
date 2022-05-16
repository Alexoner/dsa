# sar

sar: system activity reporter.

## install

    sudo apt install sysstat
	# edit /etc/sysstat to enable
	systemctl start sysstat

## CPU statistics

    sar -u 1 10 

## memory statistics

    sar -r 1 10 

## View I/O stats 

    sar -b 1 10 

## View disk Device status 

    sar -d 1 5 
