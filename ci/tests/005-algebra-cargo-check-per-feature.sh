#!/bin/bash
# shellcheck disable=SC2086

set -xeo pipefail

retval=0
cd algebra
cargo $CARGOARGS check --features "parallel" || retval="$?"
cargo $CARGOARGS check --features "fft" || retval="$?"
cargo $CARGOARGS check --features "n_fold" || retval="$?"
cargo $CARGOARGS check --features "llvm_asm" || retval="$?"
cargo $CARGOARGS check --features "derive" || retval="$?"
cargo $CARGOARGS check --features "tweedle" || retval="$?"
cargo $CARGOARGS check --features "secp256k1" || retval="$?"
cargo $CARGOARGS check --features "ed25519" || retval="$?"
cargo $CARGOARGS check --features "full" || retval="$?"
exit "$retval"
