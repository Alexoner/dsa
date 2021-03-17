# man in the middle attack 

## mitmproxy

### Install

	# install the library: https://mitmproxy.org/#mitmproxy
	pip install mitmproxy

	# install mitmproxy certificate: http://mitm.it/
	sudo mkdir /usr/share/ca-certificates/extra
	sudo cp mitmproxy.crt /usr/share/ca-certificates/extra/mitmproxy.crt
	sudo dpkg-reconfigure ca-certificates
	# in case of a .pem file on Ubuntu, it must be converted to a .crt file:
	openssl x509 -in foo.pem -inform PEM -out foo.crt

	# view documentation for addons
	pydoc mitmproxy.http

### Start

	mitmweb --web-port 7778 -p 7777
	# start with CLI interface, proxy authentication, scripting, internet access
	mitmproxy -p 7777 --proxyauth sun:mingming -s scripts/hello.py --set block_global=false

#### Usage of mitmproxy & mitmweb

	z clear flows
	? view help

### Use the proxy

	# use the proxy through python requests HTTPS client. REQUESTS_CA_BUNDLE is the trusted CA environment varialbe recognized by python requests library.
	all_proxy=http://localhost:7777 REQUESTS_CA_BUNDLE=/etc/ssl/certs/mitmproxy-ca-cert.pem 
	# use the proxy through CURL command line.
	all_proxy=http://localhost:7777 CURL_CA_BUNDLE=/etc/ssl/certs/mitmproxy-ca-cert.pem 
	all_proxy=http://[user:password@]localhost:7777 CURL_CA_BUNDLE=/etc/ssl/certs/mitmproxy-ca-cert.pem 
