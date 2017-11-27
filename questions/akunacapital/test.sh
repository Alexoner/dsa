#!/bin/sh

for i in `ls matchingEngine*.in`
do
	echo "running $i  <<<"
	cat < $i
	echo ">>>  --------------------------------------"
	BASENAME="$(basename $i .in)"
	RUNLOG=${BASENAME}.run
	OUTFILE=${BASENAME}.out
	../../build/bin/matchingEngine < $i > $RUNLOG && diff $RUNLOG $OUTFILE || exit -1
	echo "======================================\n"
done

echo "self test passed!"
