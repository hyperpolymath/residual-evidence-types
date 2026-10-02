#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
#
# The explorer correspondence, end to end:
#   1. bun harness: the model is loaded out of the unchanged explorer HTML and
#      its contract is tested. The test count is asserted, because `bun test`
#      exits 0 when it finds no tests at all.
#   2. regenerate ExplorerTable.agda from the HTML and diff it against the
#      committed copy (drift between the explorer and the table).
#   3. Agda proves Checker.table ≡ ExplorerTable.expected by refl
#      (drift between the table and the certified checker).
# Kept apart from `just check` so the fast core loop stays fast.
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."
bun="${BUN:-bun}"
prover="${AGDA:-agda}"
expected_tests=11

"$bun" --version
"$prover" --version

mkdir -p _build/correspondence
log=_build/correspondence/bun-test.log
if ! "$bun" test tests/correspondence >"$log" 2>&1; then
  cat "$log"
  echo 'ERROR: explorer harness failed' >&2
  exit 1
fi
plain="$(sed 's/\x1b\[[0-9;]*m//g' "$log")"
if ! grep -Eq "^ *${expected_tests} pass$" <<<"$plain" ||
   ! grep -Eq '^ *0 fail$' <<<"$plain"; then
  cat "$log"
  echo "ERROR: expected exactly ${expected_tests} passing harness tests and 0 failures" >&2
  exit 1
fi
echo "PASS: explorer harness, ${expected_tests} tests"

fresh=_build/correspondence/ExplorerTable.agda
"$bun" tests/correspondence/generate-table.js --out "$fresh"
if ! diff -u tests/correspondence/ExplorerTable.agda "$fresh"; then
  echo 'ERROR: committed ExplorerTable.agda differs from the explorer; regenerate it' >&2
  exit 1
fi
echo 'PASS: committed table matches the explorer byte for byte'

"$prover" --safe --without-K --no-libraries --ignore-interfaces --double-check \
  -i src -i tests/correspondence tests/correspondence/Correspondence.agda
echo 'PASS: Checker.table ≡ ExplorerTable.expected by refl'
