# network troubleshooting commands

```shell
# network interfaces, address
ip addr # get ip address

# route table
ip route # check route table
netstate -rn # check route table

# dns
cat /etc/resolve.conf # check local dns config
dig www.google.com  # dns query

# trace route packets
traceroute $IP
traceroute www.google.com # print route packets to network host

# listening ports
netstat -nlpte # check listening TCP ports

# firewall filtering settings
iptables # check firewall settings

```
