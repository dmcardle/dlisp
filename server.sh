#!/usr/bin/env sh
set -ex

PORT=8636
MAX_CONCURRENT_SESSIONS=5

systemd-run --scope -p CPUQuota=50% -p MemoryMax=256M -p MemoryHigh=512M --user -- \
  socat -d -d \
    TCP-LISTEN:${PORT},reuseaddr,fork,max-children=${MAX_CONCURRENT_SESSIONS} \
    EXEC:"$(realpath target/release/dlisp)"
