#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
set -euo pipefail
cd -P -- "$(dirname -- "${BASH_SOURCE[0]}")/.."
prover="${AGDA:-agda}"
"$prover" --version
flags=(--safe --without-K --no-libraries --ignore-interfaces --double-check -i src -i tests/integration)
echo_flags=(-i _build/dependencies/echo-types/proofs/agda -i _build/dependencies/standard-library/src)
epi_flags=(-i _build/dependencies/epistemic-types/src)

bash scripts/fetch-siblings.sh

# A missing dependency, broken toolchain or invalid positive theorem is a
# failure, never evidence that an expected-rejection control worked.
"$prover" "${flags[@]}" "${echo_flags[@]}" tests/integration/EchoComparison.agda
"$prover" "${flags[@]}" "${epi_flags[@]}" tests/integration/EpistemicComparison.agda

shopt -s nullglob
echo_rejects=(tests/integration/reject/FalseEcho*.agda)
epi_rejects=(tests/integration/reject/FalseEpistemic*.agda)
shopt -u nullglob
if (( ${#echo_rejects[@]} == 0 || ${#epi_rejects[@]} == 0 )); then
  echo 'ERROR: both Echo and Epistemic expected-rejection controls are required' >&2
  exit 1
fi

mkdir -p _build/check-logs
prefix_dir="$(mktemp -d "$PWD/_build/check-logs/sibling-prefix.XXXXXX")"
trap 'rm -rf -- "$prefix_dir"' EXIT

for file in "${echo_rejects[@]}" "${epi_rejects[@]}"; do
  name="$(basename -- "$file" .agda)"
  log="_build/check-logs/$name.log"
  prefix_log="_build/check-logs/$name-prefix.log"
  extra=("${epi_flags[@]}")
  if [[ "$name" == FalseEcho* ]]; then
    extra=("${echo_flags[@]}")
  fi

  # Controls end in one declaration named `invalid`. Reject malformed control
  # files instead of treating a type error in an earlier helper as a success.
  if ! invalid_start="$(awk '
    /^invalid[[:space:]]*:/ { signatures++; start = NR; next }
    /^invalid([[:space:]]+[^:]*)?=/ { definitions++; definition = NR; next }
    start && /^[^[:space:]]/ && !/^--/ { trailing = 1 }
    END {
      if (signatures != 1 || definitions != 1 || definition <= start || trailing)
        exit 1
      print start
    }
  ' "$file")"; then
    echo "ERROR: $file must end in one invalid signature and definition" >&2
    exit 1
  fi
  last_line="$(awk 'END { print NR }' "$file")"

  # Check every import and helper independently, retaining the original module
  # name in an isolated include directory. The failing declaration is omitted.
  awk -v start="$invalid_start" 'NR < start' "$file" > "$prefix_dir/$name.agda"
  if ! "$prover" "${flags[@]}" "${extra[@]}" -i "$prefix_dir" \
       "$prefix_dir/$name.agda" >"$prefix_log" 2>&1; then
    cat "$prefix_log"
    echo "ERROR: the supposedly valid prefix of $name does not type-check" >&2
    exit 1
  fi

  status=0
  "$prover" "${flags[@]}" "${extra[@]}" -i tests/integration/reject \
    "$file" >"$log" 2>&1 || status=$?
  if (( status == 0 )); then
    cat "$log"
    echo "ERROR: invalid sibling comparison accepted: $name" >&2
    exit 1
  fi

  # The pinned Agda 2.6.4.3 reports type errors with exit 42. A crash or signal,
  # a diagnostic from a dependency,
  # or a parse/scope/hole failure does not establish the intended rejection.
  diagnostic_line="$(awk -v path="$PWD/$file:" '
    index($0, path) == 1 {
      location = substr($0, length(path) + 1)
      if (location ~ /^[0-9]+,[0-9]+/) {
        split(location, positions, ",")
        print positions[1]
        exit
      }
    }
  ' "$log")"
  if (( status != 42 )) || [[ -z "$diagnostic_line" ]] ||
     (( diagnostic_line < invalid_start || diagnostic_line > last_line )) ||
     ! grep -q 'when checking that' "$log" ||
     grep -Eq 'Not in scope|Failed to find|Unsolved|Parse error' "$log"; then
    cat "$log"
    echo "ERROR: unexpected failure while checking $name (exit $status)" >&2
    exit 1
  fi
  echo "PASS: rejected $name at its invalid declaration; valid prefix checked"
done

echo "PASS: both sibling comparisons and all $(( ${#echo_rejects[@]} + ${#epi_rejects[@]} )) sibling expected rejections"
