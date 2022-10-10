# tcpdump - dump traffic on a network

Tcpdump prints out a description of the contents of packets on a network interface that match the boolean expression

`man tcpdump`: usage for tcpdump
`man pcap-filter`: packet filter syntax, used by the boolean expression

## Examples

    tcpdump -i any vvv [expression]
    tcpdump -i any tcp port 80 and host 10.244.9.12 and host 169.254.169.254 -vvv  # monitor http traffic, between two hosts, of a pod IP
    tcpdump -i any tcp and host 10.244.9.12 -vvv  # monitor TCP traffic, of a host. XXX: if iptable -t nat -A PREROUTING -j DNAT, can't restrict on destination host:port!
    tcpdump -i any 'tcp and ( host 10.244.9.12 or host 16.254.169.254 or port 2579 )' -vv
    tcpdump -l -i lo  # dump traffic on interface lo(local loop)
    tcpdump -n -t port 53 # dump traffic from/to port 53 (DNS request)

