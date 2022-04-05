#!/bin/bash
# shellcheck disable=SC2086

set -xeo pipefail

retval=0
cd r1cs/gadgets/crypto
cargo $CARGOARGS check --features "merkle_tree" || retval="$?"
cargo $CARGOARGS check --features "prf" || retval="$?"
cargo $CARGOARGS check --features "signature" || retval="$?"
cargo $CARGOARGS check --features "vrf" || retval="$?"
cargo $CARGOARGS check --features "tweedle" || retval="$?"
cargo $CARGOARGS check --features "llvm_asm" || retval="$?"
exit "$retval"
