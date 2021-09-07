# `iptables` - administrative tool for IPv4/IPv6 packet filtering and NAT

NAME
       iptables/ip6tables — administration tool for IPv4/IPv6 packet filtering and NAT

SYNOPSIS

       iptables [-t table] {-A|-C|-D} chain rule-specification
       ip6tables [-t table] {-A|-C|-D} chain rule-specification
       iptables [-t table] -I chain [rulenum] rule-specification

TABLES
       There are currently five independent tables (which tables are present at any time depends on the kernel configuration options and which modules are present).

       -t, --table table
              This  option  specifies the packet matching table which the command should operate on.  If the kernel is configured with automatic module loading, an attempt will be made to load the appro‐
              priate module for that table if it is not already there.

              The tables are as follows:

              nat:
                  This table is consulted when a packet that creates a new connection is encountered.  It consists of four built-ins: PREROUTING (for altering packets as soon as they come in), INPUT (for
                  altering packets destined for local sockets), OUTPUT (for altering locally-generated packets before routing), and POSTROUTING (for altering packets as they are about to go  out).   IPv6
                  NAT support is available since kernel 3.7.
			  ......

Man page:

	man iptables
	iptables -h

List rules as tables:

	iptables -L --line-number
	iptables -t nat -L --line-number

Redirect packets:

	# append: redirect all OUTPUT packets through port 9040, listened by tor.
	iptables -t nat -A OUTPUT -p tcp --syn -j REDIRECT --to-ports 9040

	# redirect dns
	iptables -t nat -A OUTPUT -p udp --dport 53 -j REDIRECT --to-ports 53

Forward traffic to local host to a remote host:port, [reference](https://unix.stackexchange.com/questions/182421/forwarding-a-localhostport-to-an-externalipnewport):

	## METHOD 1
	# 1) alter the packets that is to localhost:XXXX with the destination IP as Ext.er.nal.IP:YYYY
	iptables -t nat -A OUTPUT -m addrtype --src-type LOCAL --dst-type LOCAL -p tcp --dport 30000 -j DNAT --to-destination $REMOTE_IP:30001
	# 2) alter the source IP as the public ip of your machine.
	iptables -t nat -A POSTROUTING -m addrtype --src-type LOCAL --dst-type UNICAST -j MASQUERADE
	# 3) enable localhost/localnet route processing for your outbound interface
	sysctl -w net.ipv4.conf.all.route_localnet=1


Delete rule with number N:

	iptables -t nat -D OUTPUT $N

Flush all chains(delete all of firewall rules):

	iptables -F
	iptables -t nat -F

Drop packet from a server port:

    iptables -A INPUT --src $IP --port $PORT -j DROP
    iptables -A INPUT --src $IP --port $PORT --mode random --probability 0.9 -j DROP

Limit band width:

	iptables -A OUTPUT -m owner --uid-owner squid -m limit --limit 10/s -j ACCEPT
	iptables -A OUTPUT -m owner --uid-owner squid -j REJECT

Save & restore:

	iptables-save > iptables.rules.sh
	iptables-restore iptables.rules.sh
	service iptables save # persist iptables rules


