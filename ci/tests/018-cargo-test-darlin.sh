#!/bin/bash
# shellcheck disable=SC2086

set -xeo pipefail

cd proof-systems/src/darlin/poly-commit
cargo $CARGOARGS test

cd ../marlin
cargo $CARGOARGS test

cd ..
cargo $CARGOARGS test