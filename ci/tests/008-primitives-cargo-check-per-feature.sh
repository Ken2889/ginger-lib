#!/bin/bash
# shellcheck disable=SC2086

set -xeo pipefail

retval=0
cd primitives
cargo $CARGOARGS check --features "merkle_tree" || retval="$?"
cargo $CARGOARGS check --features "prf" || retval="$?"
cargo $CARGOARGS check --features "signature" || retval="$?"
cargo $CARGOARGS check --features "vrf" || retval="$?"
cargo $CARGOARGS check --features "tweedle" || retval="$?"
exit "$retval"
