#!/bin/bash
# shellcheck disable=SC2086

set -xeo pipefail

retval=0
cd proof-systems/src/darlin/poly-commit
cargo $CARGOARGS check || retval="$?"
cargo $CARGOARGS check --all-features --tests || retval="$?"
exit "$retval"
