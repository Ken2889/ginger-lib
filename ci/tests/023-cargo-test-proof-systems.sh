#!/bin/bash
# shellcheck disable=SC2086

set -xeo pipefail

cd proof-systems/src
cargo $CARGOARGS test --all-features

cd marlin
cargo $CARGOARGS test --all-features

cd ../poly-commit
cargo $CARGOARGS test --all-features
