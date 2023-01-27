#!/bin/bash
# shellcheck disable=SC2086

set -xeo pipefail

retval=0
cd proof-systems/src/poly-commit
cargo $CARGOARGS check --features "asm" || retval="$?"
exit "$retval"