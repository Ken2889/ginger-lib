#!/bin/bash
# shellcheck disable=SC2086

set -xeo pipefail

retval=0
cd algebra
cargo $CARGOARGS check --tests --features "parallel" || retval="$?"
cargo $CARGOARGS check --tests --features "fft" || retval="$?"
cargo $CARGOARGS check --tests --features "n_fold" || retval="$?"
cargo $CARGOARGS check --tests --features "tweedle" || retval="$?"
cargo $CARGOARGS check --tests --features "secp256k1" || retval="$?"
cargo $CARGOARGS check --tests --features "ed25519" || retval="$?"
cargo $CARGOARGS check --tests --features "full" || retval="$?"
exit "$retval"
