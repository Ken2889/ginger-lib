#!/bin/bash
# shellcheck disable=SC2086

set -xeo pipefail

retval=0
cd type-mappings
cargo $CARGOARGS check
cargo $CARGOARGS check --features "bn_382" || retval="$?"
cargo $CARGOARGS check --features "tweedle" || retval="$?"
cargo $CARGOARGS check --features "bn_382, groth16" || retval="$?"
cargo $CARGOARGS check --features "tweedle, groth16" || retval="$?"
cargo $CARGOARGS check --all-features || retval="$?"
exit "$retval"
