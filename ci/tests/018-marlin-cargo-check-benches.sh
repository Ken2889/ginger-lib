#!/bin/bash
# shellcheck disable=SC2086

set -xeo pipefail

cd proof-systems/src/darlin/marlin
cargo $CARGOARGS check --all-features --benches
