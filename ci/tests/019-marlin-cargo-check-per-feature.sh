#!/bin/bash
# shellcheck disable=SC2086

set -xeo pipefail

retval=0
cd proof-systems/src/darlin/marlin
cargo $CARGOARGS check --features "print-trace" || retval="$?"
cargo $CARGOARGS check --features "asm" || retval="$?"
exit "$retval"
