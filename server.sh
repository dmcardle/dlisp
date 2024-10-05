#!/usr/bin/env sh
set -ex

PORT=8636
MAX_CONCURRENT_SESSIONS=5
MAX_PERCENT_CPU=5

socat -d -d \
    TCP-LISTEN:${PORT},reuseaddr,fork,max-children=${MAX_CONCURRENT_SESSIONS} \
    EXEC:"cpulimit -f -l ${MAX_PERCENT_CPU} -- $(realpath target/release/dlisp)"
