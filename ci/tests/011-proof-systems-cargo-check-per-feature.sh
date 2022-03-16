#!/bin/bash
# shellcheck disable=SC2086

set -xeo pipefail

retval=0
cd proof-systems
cargo $CARGOARGS check || retval="$?"
cargo $CARGOARGS check --features "circuit-friendly" || retval="$?"
exit "$retval"
