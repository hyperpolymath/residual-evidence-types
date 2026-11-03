#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
# Evaluate the pinned K9 component and compare its data with this checkout.
# This gate checks proof configuration; it does not run or certify the proofs.
set -euo pipefail
cd -P -- "$(dirname -- "${BASH_SOURCE[0]}")/.."

offline=0
if [[ "${1:-}" == --offline ]]; then offline=1; shift; fi
if (( $# != 0 )); then
  echo 'Usage: bash scripts/check-contract.sh [--offline]' >&2
  exit 2
fi

for tool in python3 sha256sum awk sed grep head tail cmp tr basename dirname mktemp timeout uname; do
  command -v "$tool" >/dev/null || { echo "ERROR: required tool is missing: $tool" >&2; exit 1; }
done
if [[ "$(uname -s)" != Linux || "$(uname -m)" != x86_64 ]]; then
  echo 'ERROR: the verified Nickel asset supports Linux x86_64; use the CI environment on other hosts.' >&2
  exit 1
fi

standards_rev=d3e4b485a2af90c92a8e18af0888cd19cb132cd9
nickel_version=1.18.0
nickel_sha256=9cba4dd65ae9915ec61f73033aafcff307a377665a83fd8f530df086763318cb
cache="$PWD/_build/k9-tools"
standards="$cache/standards-$standards_rev"
nickel="$cache/nickel-$nickel_version"
validator_rel=1-formats/k9/tools/k9-validate.sh
contract_rel=1-formats/k9/spec/contract/k9_contract.ncl
component=contractiles/k9/proof-validation.k9.ncl
logs="$PWD/_build/check-logs/contract"
mkdir -p "$cache" "$logs"
tempdir="$(mktemp -d "$cache/check.XXXXXX")"
trap 'rm -rf -- "$tempdir"' EXIT

# Check every cached asset before use. A damaged cache fails closed rather
# than silently replacing the evidence of a mismatch. Downloads are installed
# into the ignored cache only after their pinned SHA-256 has been verified.
verify_digest() {
  local path="$1" digest="$2"
  [[ -f "$path" && ! -L "$path" ]] || { echo "ERROR: expected a regular cached file: $path" >&2; return 1; }
  printf '%s  %s\n' "$digest" "$path" | sha256sum --check --status - || {
    echo "ERROR: cached tool checksum mismatch: $path" >&2
    return 1
  }
}

fetch_checked() {
  local path="$1" digest="$2" url="$3" downloaded
  if [[ -e "$path" || -L "$path" ]]; then
    verify_digest "$path" "$digest"
    return
  fi
  if (( offline )); then
    echo "ERROR: required cached tool is missing in offline mode: $path" >&2
    return 1
  fi
  command -v curl >/dev/null || { echo 'ERROR: curl is required to fetch pinned tools.' >&2; return 1; }
  downloaded="$(mktemp "$tempdir/download.XXXXXX")"
  curl --fail --silent --show-error --location --retry 2 \
    --proto '=https' --proto-redir '=https' --tlsv1.2 \
    --output "$downloaded" "$url"
  verify_digest "$downloaded" "$digest"
  mkdir -p -- "$(dirname -- "$path")"
  mv -- "$downloaded" "$path"
}

fetch_checked "$nickel" "$nickel_sha256" \
  "https://github.com/tweag/nickel/releases/download/$nickel_version/nickel-x86_64-linux"
# Git blob 8ada4afecdbf3babb09567f7aae55f9c61ff055a at the pinned revision.
fetch_checked "$standards/$validator_rel" \
  8a48e109e10b14b5dc99de3dcbc31857a583839237f5a1aeed0701e6538d50c4 \
  "https://raw.githubusercontent.com/metadatastician/standards/$standards_rev/$validator_rel"
# Git blob 95aeb043ce5fb0d55fa2c7cfd259baf6f5fa993a; this contract has no imports.
fetch_checked "$standards/$contract_rel" \
  35e887762080acd2854849499662711a5d03038d1079ab5e194df40523136f97 \
  "https://raw.githubusercontent.com/metadatastician/standards/$standards_rev/$contract_rel"
chmod u+x "$nickel"
version_output="$("$nickel" --version)"
if ! grep -Eq '(^|[[:space:]])1\.18\.0([[:space:]]|$)' <<< "$version_output"; then
  echo "ERROR: unexpected Nickel version: $version_output" >&2
  exit 1
fi

# This consumer deliberately supports only its standalone, import-free Yard
# component. Do not let future component imports read arbitrary host paths.
[[ -f "$component" ]] || { echo "ERROR: missing proof component: $component" >&2; exit 1; }
if grep -qw import "$component"; then
  echo 'ERROR: the proof configuration must remain import-free (including documentation using the import keyword).' >&2
  exit 1
fi

# Ordinary L2 validation needs only the two canonical files fetched above.
# leash.ncl, capabilities.ncl and upstream fixtures belong to the validator's
# own --self-test, which this consumer does not substitute for its own checks.
if ! timeout 60s bash "$standards/$validator_rel" \
     --nickel "$nickel" --strict --layer L2 --json -- "$component" \
     > "$logs/canonical.json" 2> "$logs/canonical.log"; then
  cat "$logs/canonical.log" "$logs/canonical.json" >&2
  echo 'ERROR: canonical K9 L2 validation failed or timed out.' >&2
  exit 1
fi

# Preserve source line numbers while removing the non-Nickel envelope. The
# canonical validator has already checked the magic, pedigree and predicates;
# repeat its contract application while exporting the exact data we consume.
sed '1s/^K9!$/# K9! envelope removed for Nickel/' "$component" > "$tempdir/body.ncl"
python3 - "$standards/$contract_rel" "$tempdir/body.ncl" "$tempdir/driver.ncl" <<'PY'
import json
import pathlib
import sys
contract, body, destination = sys.argv[1:]
pathlib.Path(destination).write_text(
    f'let K9 = import {json.dumps(contract)} in\n'
    f'let k9_doc = import {json.dumps(body)} in\n'
    'k9_doc | K9.Component\n', encoding='utf-8')
PY
if ! timeout 60s "$nickel" export --format json "$tempdir/driver.ncl" \
     > "$logs/evaluated.json" 2> "$logs/export.log"; then
  cat "$logs/export.log" >&2
  echo 'ERROR: the evaluated K9 configuration could not be exported.' >&2
  exit 1
fi

python3 scripts/check-contract.py \
  --root "$PWD" --document "$logs/evaluated.json" --verdict "$logs/canonical.json" \
  --standards-revision "$standards_rev" --nickel-version "$nickel_version" \
  --nickel-sha256 "$nickel_sha256" --regression

# Negative semantic fixture: remove --safe from the configured value while
# retaining the predicate that requires it. Require the canonical Nickel
# contract error, not a parse error, missing tool, earlier layer or timeout.
python3 - "$component" "$tempdir/without-safe.k9.ncl" <<'PY'
import pathlib
import sys
source, destination = map(pathlib.Path, sys.argv[1:])
text = source.read_text(encoding='utf-8')
before = '        = ["--safe", "--without-K", "--no-libraries", "--ignore-interfaces", "--double-check"],'
after = before.replace('"--safe", ', '', 1)
if text.count(before) != 1:
    raise SystemExit('ERROR: could not construct the missing-safety-flag fixture unambiguously')
destination.write_text(text.replace(before, after, 1), encoding='utf-8')
PY
status=0
timeout 60s bash "$standards/$validator_rel" \
  --nickel "$nickel" --strict --layer L2 --json -- "$tempdir/without-safe.k9.ncl" \
  > "$logs/without-safe.json" 2> "$logs/without-safe.log" || status=$?
python3 - "$status" "$logs/without-safe.json" <<'PY'
import json
import pathlib
import sys
status = int(sys.argv[1])
result = json.loads(pathlib.Path(sys.argv[2]).read_text(encoding='utf-8'))
errors = [finding for finding in result['findings'] if finding['severity'] == 'error']
if (status != 1 or result['verdict'] != 'fail' or result['skipped'] != 0
        or len(errors) != 1 or errors[0]['rule'] != 'K9-N001'
        or errors[0]['layer'] != 'L2'
        or 'violates the K9.Component contract' not in errors[0]['message']):
    raise SystemExit('ERROR: the missing-safety-flag fixture did not fail at the intended Nickel contract')
print('PASS: Nickel rejects a configured safety-flag omission at K9-N001 / L2')
PY

echo 'PASS: proof configuration, checkout consistency and targeted rejection controls (proof execution is separate)'
