#!/bin/bash

set -xeo pipefail

cd proof-systems/src/darlin

# shellcheck disable=SC2086

cargo $CARGOARGS test --features "darlin"