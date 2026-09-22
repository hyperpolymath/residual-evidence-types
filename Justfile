# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
set shell := ["bash", "-euo", "pipefail", "-c"]

# Core proofs and semantic expected-rejection controls (Agda builtins only).
check:
    bash scripts/check.sh

# Check against the actual epistemic-types source directory supplied by the caller.
check-epistemic epistemic_src:
    agda --safe --without-K --no-libraries --ignore-interfaces --double-check -i src -i tests/integration -i '{{epistemic_src}}' tests/integration/EpistemicComparison.agda

# Check against the actual echo-types source and Agda standard library.
check-echo echo_src stdlib_src:
    agda --safe --without-K --no-libraries --ignore-interfaces --double-check -i src -i tests/integration -i '{{echo_src}}' -i '{{stdlib_src}}' tests/integration/EchoComparison.agda

# Fetch the pinned sibling revisions into _build/dependencies with plain git.
fetch-siblings:
    bash scripts/fetch-siblings.sh

# The full hosted set, locally: core, rejections and both sibling comparisons.
check-all: check fetch-siblings
    just check-epistemic _build/dependencies/epistemic-types/src
    just check-echo _build/dependencies/echo-types/proofs/agda _build/dependencies/standard-library/src
