#!/bin/bash
# shellcheck disable=SC2086

set -xeo pipefail

cd proof-systems/src/marlin
cargo $CARGOARGS check --all-features --benches --examples