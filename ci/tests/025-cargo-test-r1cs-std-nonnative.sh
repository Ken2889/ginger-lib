#!/bin/bash
# shellcheck disable=SC2086

set -xeo pipefail

cd r1cs/gadgets/std
cargo $CARGOARGS test nonnative --all-features
