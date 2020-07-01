#!/bin/bash

# openssl standard commands:
# req:  PKCS#10 X.509 Certificate Signing Request (CSR) Management.
# rsa:  RSA key management
# x509: X.509 Certificate Data Management.
# pkcs12: PKCS#12 Data Management

######### GENERATE CA, server, client side key and certificate ############

# Certificate Authority side
# uncomment bellow commands to regenerate from scratch!
# Generate the CA Key and Certificate of which format is PEM
# openssl req -x509 -sha256 -newkey rsa:4096 -keyout ca.key -out ca.crt -days 356 -nodes -subj '/CN=Cert Authority 0'

# server certificate: generate the Certificate Signing Request, Server Key
openssl req -new -newkey rsa:4096 -keyout server.key -out server.csr -nodes -subj '/CN=myserver.com'
# generate X.509 certificate by Signing with the CA Certificate
openssl x509 -req -sha256 -days 365 -in server.csr -CA ca.crt -CAkey ca.key -set_serial 01 -out server.crt

# client certificate: generate the Certificate Signing Request, Client Key
openssl req -new -newkey rsa:4096 -keyout client.key -out client.csr -nodes -subj '/CN=myclient'
# generate X.509 certificate by Signing with the CA Certificate
openssl x509 -req -sha256 -days 365 -in client.csr -CA ca.crt -CAkey ca.key -set_serial 02 -out client.crt


#### CHECKING

# check a Certificate Signing Request(CSR)
openssl req -text -noout -verify -in client.csr
# check a private key
openssl rsa -in ca.key -check
# check a certificate information
openssl x509 -text -noout -in ca.crt |head -n 15
# check a PKCS#12 file (.pfx or .p12)
openssl pkcs12 -info -in client.pfx

#### VERIFY
# verify signature of X509 certificate with CA
openssl verify -CAfile ca.crt client.crt


#### CONVERTING
# (optional) key material can be combined into a single PKCS#12 PFX file.
openssl pkcs12 -export -out client.pfx -inkey client.key -in client.crt --certfile ca.crt
# read pfx file with openssl
# openssl pkcs12 -info -in client.pfx |openssl x509 -noout -text


#### ENCRYPT AND DECRYPT, SIGN AND VERIFY
# Create message to be encrypted
echo "Creating message file"
echo "---------------------"
echo "My secret message" > message.txt
echo "done\n"

# Create asymmetric keypair
echo "Creating asymmetric key pair"
echo "----------------------------"
openssl genrsa -out private.pem 1024
openssl rsa -in private.pem -out public.pem -pubout
echo "done\n"

# Encrypt with public & decrypt with private
echo "Public key encrypts and private key decrypts"
echo "--------------------------------------------"
openssl rsautl -encrypt -inkey public.pem -pubin -in message.txt         -out message_enc_pub.ssl
openssl rsautl -decrypt -inkey private.pem       -in message_enc_pub.ssl -out message_pub.txt
xxd message_enc_pub.ssl # Print the binary contents of the encrypted message
cat message_pub.txt # Print the decrypted message
echo "done\n"

# Encrypt with private & decrypt with public
echo "Private key encrypts and public key decrypts"
echo "--------------------------------------------"
openssl rsautl -sign    -inkey private.pem       -in message.txt          -out message_enc_priv.ssl
openssl rsautl -verify  -inkey public.pem -pubin -in message_enc_priv.ssl -out message_priv.txt
xxd message_enc_priv.ssl
cat message_priv.txt
diff message.txt message_priv.txt
echo "done\n"

#### using with nginx
# combine multiple certificates into one
# cat cert1.pem cert2.pem > bundle.pem

# configure server to enable client authentication
echo "enable ssl client certificate authentication, and reload nginx"
cat <<EOF
	ssl_verify_client on;
	ssl_verify_depth 2;
	ssl_client_certificate ca.crt;
EOF

# access server configured with client authentication
# curl -k -i https://localhost:44224 --cert client.crt --key client.key
