# network troubleshooting commands

- physical/link layer: `ip addr`
- IP layer: route table(`netstat -nr`, `ip route`), `traceroute`, `iptables`, http traceroute?
- DNS: `host`, `dig``
- socket: `netstat -nlpte` for TCP connections

## Overview

```shell
# network interfaces, address
ip addr # get ip address

# route table display
ip route # check route table
netstate -rn # check route table
route -n # display route table

# route table manipulation
# ip route add #
# ip route del 

# dns
cat /etc/resolve.conf # check local dns config
dig www.google.com  # dns query

# trace route packets

traceroute $IP
traceroute www.google.com # print route packets to network host
root@ubuntu:/# tcptraceroute 169.254.169.254
Selected device eth0, address 10.244.9.12, port 55397 for outgoing packets
Tracing the path to 169.254.169.254 on TCP port 80 (http), 30 hops max
 1  10.244.9.1  0.086 ms  0.094 ms  0.080 ms
  2  169.254.169.254 [open]  0.642 ms  0.554 ms  0.556 ms

traceroute -T -p <Port> <IP>

# listening ports
netstat -nlpte # check listening TCP ports

# firewall filtering settings
iptables # check firewall settings

```

## Example

	iptables-save
	iptables -t nat -L
    iptables -t raw -A OUTPUT -p tcp --destination 169.254.169.254 --dport 80 -j TRACE
	iptables -t raw -A PREROUTING -p tcp --destination 169.254.169.254 --dport 80 -j TRACE  # trace iptables 

    iptables -t nat -A OUTPUT -p tcp -d 192.168.1.101 --dport 1234 -j DNAT --to-destination 192.168.1.102:4321
	tcpdump -i eth0 host 192.168.1.102 or host 192.168.1.101
    telnet 192.168.1.101 8888  # route 1
	telnet 192.168.1.101 1234  # route 2

