# DNS utility

## Tracing network packets

### DNS lookup utility

Different DNS resolution results may occur depending on whether to use `/etc/resolv.conf` or not.

	dig www.google.com
	dig +search +short www.google.com  # +[no]search Use [do not use] the search list defined by the searchlist or domain directive in resolv.conf (if any). The search list is not used by default.
	nslookup www.google.com
	host www.google.com

	dig +short myip.opendns.com @resolver1.opendns.com # get public IP address from special-purpose DNS server.

### Dump DNS network packets

	tcpdump port 53

### traceroute - print the route packets trace to network host

	sudo apt install -y traceroute
	traceroute www.google.com

### Change DNS

#### Change DNS server
Add `nameserver x.x.x.x` to `/etc/resolv.conf`

#### Add static DNS record to `/etc/hosts`

Add `x.x.x.x domain-name` to `/etc/hosts`.
