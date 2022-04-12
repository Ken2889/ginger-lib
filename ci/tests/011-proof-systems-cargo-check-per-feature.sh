#!/bin/bash
# shellcheck disable=SC2086

set -xeo pipefail

retval=0

cd proof-systems/src/darlin/fiat-shamir
cargo $CARGOARGS check || retval="$?"

cd ../poly-commit
cargo $CARGOARGS check || retval="$?"
cargo $CARGOARGS check --features="minimize-proof-size" || retval="$?"

cd ../marlin
cargo $CARGOARGS check || retval="$?"
cargo $CARGOARGS check --features="circuit-friendly" || retval="$?"

cd ..
cargo $CARGOARGS check || retval="$?"
cargo $CARGOARGS check --features="circuit-friendly" || retval="$?"

exit "$retval"