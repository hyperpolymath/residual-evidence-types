#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."
prover="${AGDA:-agda}"
"$prover" --version
flags=(--safe --without-K --no-libraries --ignore-interfaces --double-check -i src)

# Check the entire positive set first. Missing imports, broken tooling, and
# unresolved holes must not turn into successful expected-rejection tests.
"$prover" "${flags[@]}" src/ResidualEvidence/All.agda
mkdir -p _build/check-logs

# Every module under tests/reject is an expected rejection: one invalid
# declaration per positive result. An empty set is a broken checkout, not a pass.
shopt -s nullglob
rejects=(tests/reject/*.agda)
shopt -u nullglob
if (( ${#rejects[@]} == 0 )); then
  echo 'ERROR: no expected-rejection modules found under tests/reject' >&2
  exit 1
fi
for file in "${rejects[@]}"; do
  name="$(basename -- "$file" .agda)"
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
echo "PASS: core proofs and all ${#rejects[@]} expected rejections"
