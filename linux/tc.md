### tc - traffic control

Rate limit for a specific host:

    #!/bin/sh
    # file: limittraffic


    DEVICE=bond0
    CLIENT_IP=${1:-10.40.46.23}

    echo "device: $DEVICE, IP: $CLIENT_IP"

    tc qdisc del dev $DEVICE root # delete root rule
    tc qdisc add dev $DEVICE root handle 1: htb default 10

    tc class add dev $DEVICE parent 1: classid 1:1 htb rate 1gbps ceil 1500mbps

    tc class add dev $DEVICE parent 1:1 classid 1:10 htb rate 1gbps ceil 1500mbps # default goes here

    tc class add dev $DEVICE parent 1:1 classid 1:11 htb rate 1gbps ceil 1gbps # matches limited IP goes here

    tc filter add dev $DEVICE protocol ip parent 1:0 prio 1 u32 match ip src ${CLIENT_IP} flowid 1:11
    tc filter add dev $DEVICE protocol ip parent 1:0 prio 1 u32 match ip dst ${CLIENT_IP} flowid 1:11


