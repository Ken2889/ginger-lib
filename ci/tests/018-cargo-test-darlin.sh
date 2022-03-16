#!/bin/bash
# shellcheck disable=SC2086

set -xeo pipefail

cd proof-systems/src/darlin/fiat-shamir
cargo $CARGOARGS test

cd ../poly-commit
cargo $CARGOARGS test
cargo $CARGOARGS test --features="circuit-friendly"

cd ../marlin
cargo $CARGOARGS test
cargo $CARGOARGS test --features="circuit-friendly"

cd ..
cargo $CARGOARGS test
cargo $CARGOARGS test --features="circuit-friendly"