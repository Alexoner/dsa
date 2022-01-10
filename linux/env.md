# environment variables

## proxy

	export http_proxy="http://PROXY_SERVER:PORT"
	# setting https_proxy to an HTTP address will use the server as a HTTPS forward proxy/tunnel.
	export https_proxy="http://PROXY_SERVER:PORT"
	# setting https_proxy to an HTTPS address will use the server as a HTTPS transparent/intercepting proxy,
	# needing to trust the CA certificate for the HTTPS intercepting proxy.
	export https_proxy="https://PROXY_SERVER:PORT"
	export https_proxy="https://USER:PASSWOR@PROXY_SERVER:PORT" # if password authentication is needed
	export all_proxy="http://PROXY_SERVER:PORT"  # all proxy, including HTTP, HTTPS, 
	export ftp_proxy="ftp://PROXY_SERVER:PORT"
	# NO_PROXY: A comma-separated list of host names that shouldn't go through any proxy is set in (only an asterisk, * matches all hosts)

Reference: https://www.shellhacks.com/linux-proxy-server-settings-set-proxy-command-line/

### forward proxy - tunnel - doesn't decrypt HTTPs packets just forward as encrypted

    http_proxy=http://host:port https_proxy=http://host:port curl -L 'https://www.google.com'
    all_proxy=http://host:port curl -L 'https://www.google.com'

### intercepting/transparent proxy - man in the middle attack - 
A `mitmproxy` can do man in the middle attack against HTTPS connections by using self-issued root certificates.

	mitmweb --web-port 7778 -p 7777 # start the proxy listening at 7777, with web portal port 7778
	# using intercepting proxy for HTTPS proxy
	http_proxy=http://localhost:7777 https_proxy=https://localhost:7777 REQUESTS_CA_BUNDLE=/etc/ssl/certs/mitmproxy-ca-cert.pem # using the mitm proxy, and also specifying the trusted CA.
	# mitm software can automatically detect HTTPS traffic and intercept, so setting https_proxy variable to http://localhost:7777 will also cause the traffic to be intercepted.
	all_proxy=http://localhost:7777 REQUESTS_CA_BUNDLE=/etc/ssl/certs/mitmproxy-ca-cert.pem # using the mitm proxy, and also specifying the trusted CA.

## certificate: SSL system ca-certificates bundle
If we're performing man in the middle attack against HTTPS requests, we need to configure the HTTPS clients to
use system ca-certificates bundle to pass the server certificate verification.
We can either disable SSL verification or set the environment variable for trusted root certificate.

	# https://stackoverflow.com/questions/42982143/python-requests-how-to-use-system-ca-certificates-debian-ubuntu
	export REQUESTS_CA_BUNDLE=/usr/share/ca-certificates/extra/mitmproxy-ca-cert.crt
