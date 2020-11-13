#### sed
A simple text processing and transforming tool, mostly for regular expression matching.


    # substitute substring
    $ echo "Pattern" | sed -r 's/pattern/target/gI' # -r for extended regular expression, s for substitute, g for global, I for case insensitive
    target
    $ sed -r -i 's/pattern/target/g' # s for substitute, g for global, i for inplace
    $ sed -r -i '2,$s/pattern/target/g' # s for substitute, g for global, i for inplace, only operate between line 2 and last line

    # extract substring with regular expression pattern
    $ echo "ljljlsfs pattern jljslfjsdl" | sed -r 's/^.*(pattern).*$/\1/g' # s for substitute, g for global, i for inplace, \1 for back referencing
    pattern

    ## advanced example
    $ echo "hello cruel world" | sed -r 's/(h.+o)(.+)(w.+d)/\1, \3/g' # "hello cruel world" -> "hello, world"
    hello, world
    # parse text: extract fields(date, error code, error code literal name)
    $ cat leaf_node_service_worker_ficus.ERROR |sed -r -n -e 's/(E[0-9]+)[^a-zZ-Z]+?(\S+[ch]pp:[0-9]+).*error code: (-?[0-9]+), (\w+)/\1,\2,\3,\4/pg' > date-error-name.csv
    E0919,retrieval_storage_client.cpp:93,-22006,THRIFT_CANNOT_INIT_RPCCLIENT_ERROR
    E0919,retrieval_retrieval_service_3.cpp:241,-22006,THRIFT_CANNOT_INIT_RPCCLIENT_ERROR, list retrieval error
    E0919,retrieval_retrieval_service_3.cpp:220,-22006,THRIFT_CANNOT_INIT_RPCCLIENT_ERROR, list retrieval error, will retry in 1 seconds
    E0919,retrieval_storage_client.cpp:127,-22006,THRIFT_CANNOT_INIT_RPCCLIENT_ERROR
    E0919,retrieval_retrieval_service_3.cpp:271,-22006,THRIFT_CANNOT_INIT_RPCCLIENT_ERROR, list false track error
    E0919,retrieval_retrieval_service_3.cpp:222,-22006,THRIFT_CANNOT_INIT_RPCCLIENT_ERROR, list false track repo error, will retry in 1 seconds
    E0919,retrieval_storage_client.cpp:93,-22006,THRIFT_CANNOT_INIT_RPCCLIENT_ERROR
    E0919,retrieval_retrieval_service_3.cpp:241,-22006,THRIFT_CANNOT_INIT_RPCCLIENT_ERROR, list retrieval error
    E0919,retrieval_retrieval_service_3.cpp:220,-22006,THRIFT_CANNOT_INIT_RPCCLIENT_ERROR, list retrieval error, will retry in 1 seconds
    E0919,retrieval_storage_client.cpp:127,-22006,THRIFT_CANNOT_INIT_RPCCLIENT_ERROR


- -r, --regexp-extended: use extended regular expression
- -i: inplace


