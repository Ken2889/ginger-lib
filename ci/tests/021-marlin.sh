#!/bin/bash

set -xeo pipefail

cd proof-systems/src/darlin/marlin

# shellcheck disable=SC2086

cargo $CARGOARGS test --all-features