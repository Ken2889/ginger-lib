#!/bin/bash
# shellcheck disable=SC2086

set -xeo pipefail

cd algebra
cargo $CARGOARGS test --all-features

cd ../primitives
cargo $CARGOARGS test --all-features

cd ../r1cs/core
cargo $CARGOARGS test --all-features

cd ../gadgets/crypto
cargo $CARGOARGS test --all-features

cd ../std
cargo $CARGOARGS test --features="full"