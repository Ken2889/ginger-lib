#!/bin/bash
# shellcheck disable=SC2086

set -xeo pipefail

retval=0
cd proof-systems
cargo $CARGOARGS check --features "print-trace" || retval="$?"
cargo $CARGOARGS check --features "darlin" || retval="$?"
cargo $CARGOARGS check --features "llvm_asm" || retval="$?"
exit "$retval"
