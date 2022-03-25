#!/bin/bash
# shellcheck disable=SC2086

set -xeo pipefail

cd proof-systems
cargo $CARGOARGS check --all-features --benches

cd src/darlin/marlin
cargo $CARGOARGS check --benches --features "asm"
cargo $CARGOARGS check --benches --features "asm, circuit-friendly"

cd ../poly-commit
cargo $CARGOARGS check --benches --features "asm"
cargo $CARGOARGS check --benches --features "asm, circuit-friendly"