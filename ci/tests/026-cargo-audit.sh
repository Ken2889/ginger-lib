#!/bin/bash

set -uo pipefail
echo -e "Start cargo audit\n"

if [ "$CARGO_AUDIT_EXIT_ON_ERROR" = "false" ]; then
  echo -e "\nCargo audit error disabled"
fi

# Ok: if we want to ignore the `cargo audit` fail but we would see the report
# we use $CARGO_AUDIT_EXIT_ON_ERROR set to false. In this case we ignore the
# `cargo audit` output value and we return always `true`.
cargo audit || ! `$CARGO_AUDIT_EXIT_ON_ERROR`
