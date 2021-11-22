#!/bin/bash

set -xeo pipefail

cd proof-systems/src/darlin/poly-commit

# shellcheck disable=SC2086

cargo $CARGOARGS test --all-features