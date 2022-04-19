#!/bin/bash
# shellcheck disable=SC2086

set -xeo pipefail

cd algebra
cargo $CARGOARGS check --benches --features "parallel"
cargo $CARGOARGS check --benches --features "fft"
cargo $CARGOARGS check --benches --features "n_fold"
cargo $CARGOARGS check --benches --features "tweedle"
cargo $CARGOARGS check --benches --features "secp256k1"
cargo $CARGOARGS check --benches --features "ed25519"
cargo $CARGOARGS check --benches --features "full"
cargo $CARGOARGS check --all-features --benches