#!/bin/bash
# mk.sh NAME  -- generate configs/NAME.cfg is expected to exist; run TLC on it.
set -e
N=$1; shift
java -XX:+UseParallelGC -cp /home/ec2-user/tla2tools.jar tlc2.TLC \
     -workers 8 -config configs/$N.cfg -metadir /tmp/tlc-$N TPCC "$@" > logs/$N.log 2>&1 || true
grep -E "Error: (Invariant|The behavior)|states generated|Finished in" logs/$N.log | head -5
