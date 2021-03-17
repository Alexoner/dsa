# environment variables

## proxy

	export http_proxy="http://PROXY_SERVER:PORT"
	export https_proxy="https://PROXY_SERVER:PORT"
	export https_proxy="https://USER:PASSWOR@PROXY_SERVER:PORT" # if password authentication is needed
	export all_proxy="http://PROXY_SERVER:PORT"  # all proxy, including HTTP, HTTPS, 
	export ftp_proxy="ftp://PROXY_SERVER:PORT"

Reference: https://www.shellhacks.com/linux-proxy-server-settings-set-proxy-command-line/

### man in the middle attack
A `mitmproxy` can do man in the middle attack against HTTPS connections by using self-issued root certificates.

	mitmweb --web-port 7778 -p 7777 # start the proxy listening at 7777, with web portal port 7778
	all_proxy=http://localhost:7777 REQUESTS_CA_BUNDLE=/etc/ssl/certs/mitmproxy-ca-cert.pem # using the mitm proxy, and also specifying the trusted CA.

## certificate: SSL system ca-certificates bundle
If we're performing man in the middle attack against HTTPS requests, we need to configure the HTTPS clients to
use system ca-certificates bundle to pass the server certificate verification.
We can either disable SSL verification or set the environment variable for trusted root certificate.

	# https://stackoverflow.com/questions/42982143/python-requests-how-to-use-system-ca-certificates-debian-ubuntu
	export REQUESTS_CA_BUNDLE=/usr/share/ca-certificates/extra/mitmproxy-ca-cert.crt
