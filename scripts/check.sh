#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."
prover="${AGDA:-agda}"
"$prover" --version
flags=(--safe --without-K --no-libraries --ignore-interfaces -i src)

# Check the entire positive set first. Missing imports, broken tooling, and
# unresolved holes must not turn into successful expected-rejection tests.
"$prover" "${flags[@]}" src/ResidualEvidence/All.agda
mkdir -p _build/check-logs
for name in FalsePresence FalseIdentification InconsistentCase; do
  file="tests/reject/$name.agda"
  log="_build/check-logs/$name.log"
  if "$prover" "${flags[@]}" -i tests/reject "$file" >"$log" 2>&1; then
    cat "$log"
    echo "ERROR: invalid proof accepted: $name" >&2
    exit 1
  fi
  # Demand a type-checking error at the intended declaration, not just a
  # nonzero exit or a filename printed while dependencies are being checked.
  if ! grep -Eq "/$name\.agda:[0-9]+,[0-9]+" "$log" ||
     ! grep -q 'when checking that' "$log" ||
     grep -Eq 'Not in scope|Failed to find|Unsolved|Parse error' "$log"; then
    cat "$log"
    echo "ERROR: unexpected failure while checking $name" >&2
    exit 1
  fi
  echo "PASS: rejected $name at its invalid declaration"
done
echo 'PASS: core proofs and all three expected rejections'
