#!/bin/bash
# shellcheck disable=SC2086

set -xeo pipefail

retval=0
cd r1cs/gadgets/std
cargo $CARGOARGS check --features "full" || retval="$?"
cargo $CARGOARGS check --features "tweedle" || retval="$?"
cargo $CARGOARGS check --features "secp256k1" || retval="$?"
cargo $CARGOARGS check --features "ed25519" || retval="$?"
cargo $CARGOARGS check --features "nonnative" || retval="$?"
exit "$retval"
