#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
#
# Proof Runner Gate. Runs the repository's own proof runner and reports its
# verdict. Three outcomes only: the runner is absent (red), the runner fails
# (red), the runner passes (green). Nothing here prints a success line it did
# not earn: the previous version of this gate echoed "All detected proofs
# executed successfully." with every command commented out.

set -euo pipefail

root=${GITHUB_WORKSPACE:-.}
runner=${PROOF_RUNNER:-scripts/check.sh}

if [[ ! -f "$root/$runner" ]]; then
  echo "::error::Proof runner $runner is absent. A repository that claims proofs ships a runner; a repository without proofs must not declare this gate."
  exit 1
fi

echo "Running proof runner $runner"
if ! (cd -- "$root" && bash "$runner"); then
  echo "::error::Proof runner $runner failed."
  exit 1
fi

echo "Proof runner $runner passed."
