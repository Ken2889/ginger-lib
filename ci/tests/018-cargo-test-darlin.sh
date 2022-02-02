#!/bin/bash
# shellcheck disable=SC2086

set -xeo pipefail

cd proof-systems/src/darlin/poly-commit
cargo $CARGOARGS test
cargo $CARGOARGS test --features="circuit-friendly"

cd ../marlin
cargo $CARGOARGS test
cargo $CARGOARGS test --features="circuit-friendly"

cd ..
cargo $CARGOARGS test --features="darlin"