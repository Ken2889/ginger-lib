#!/bin/bash
# shellcheck disable=SC2086

set -xeo pipefail

cargo $CARGOARGS test --workspace --all-features --exclude "r1cs-std"
