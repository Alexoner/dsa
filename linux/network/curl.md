#curl

## usage

	# curl dump SSL certificate
	# can be used with http_proxy, https_proxy
	curl --insecure -vvI https://www.example.com 2>&1 | awk 'BEGIN { cert=0 } /^\* SSL connection/ { cert=1 } /^\*/ { if (cert) print }'

	# ignore proxy setting
	https_proxy=https://proxy_endpoint curl --insecure -vvI --noproxy '*' https://www.google.com 2>&1 | awk 'BEGIN { cert=0 } /^\* SSL connection/ { cert=1 } /^\*/ { if (cert) print }'
	

    curl --http2-prior-knowledge host
