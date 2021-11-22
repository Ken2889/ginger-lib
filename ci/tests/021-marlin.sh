#!/bin/bash

set -xeo pipefail

retval=0
cd proof-systems/src/darlin/marlin

# shellcheck disable=SC2086
cargo $CARGOARGS check --all-features || retval="$?"
cargo $CARGOARGS check --all-features --benches || retval="$?"
cargo $CARGOARGS test --all-features || retval="$?"

echo -e "Start cargo audit\n"
cargo audit --json > /tmp/audit.json
jq '.' /tmp/audit.json

VULNERABILITIES="$(jq '.vulnerabilities.found' /tmp/audit.json)"

if [ "$CARGO_AUDIT_EXIT_ON_ERROR" = "false" ]; then
  echo -e "\nCargo audit disabled"
elif [ "$VULNERABILITIES" = "true" ]; then
  echo -e "\nVulnerabilities have been found"
  jq '.vulnerabilities' /tmp/audit.json
  exit 1
else
  echo -e "\nNo vulnerabilities have been found"
fi

exit "$retval"