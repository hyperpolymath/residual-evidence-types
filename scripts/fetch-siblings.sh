#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
#
# Fetch the compared sibling revisions into _build/dependencies with plain git.
# The pins are the published revisions recorded in PROOF-STATUS.adoc. A
# checkout that does not resolve to the pinned commit is a failure, never a
# fallback to whatever the remote currently serves.
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."
deps=_build/dependencies

fetch() {
  local name=$1 repo=$2 sha=$3 dir
  dir=$deps/$name
  if [[ ! -d "$dir/.git" ]]; then
    git init -q "$dir"
    git -C "$dir" remote add origin "https://github.com/$repo.git"
  fi
  git -C "$dir" fetch -q --depth 1 origin "$sha"
  git -C "$dir" checkout -q --detach FETCH_HEAD
  test "$(git -C "$dir" rev-parse HEAD)" = "$sha"
  echo "$name @ $sha"
}

mkdir -p "$deps"
fetch echo-types       hyperpolymath/echo-types      9c4b72b52972c7e084c8f569635eb01caef64e7a
fetch epistemic-types  hyperpolymath/epistemic-types 3f4250f73899e6c797f6df01ac6eed8e3e3a1d7b
fetch standard-library agda/agda-stdlib              97bc55e47367c562b3032bf104f2a00b19716f88
