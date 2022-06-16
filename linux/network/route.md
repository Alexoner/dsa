# network troubleshooting commands

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

# listening ports
netstat -nlpte # check listening TCP ports

# firewall filtering settings
iptables # check firewall settings

```
