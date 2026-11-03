# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
set shell := ["bash", "-euo", "pipefail", "-c"]

# Evaluate the Yard K9 proof configuration and check it against this checkout.
check-contract:
    bash scripts/check-contract.sh

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

# Check both pinned sibling comparisons and their semantic rejection controls.
check-siblings:
    bash scripts/check-siblings.sh

# Core and sibling proofs, including both sets of expected-rejection controls.
# Explorer correspondence remains the separate `correspondence` target below.
check-all: check check-siblings

# Explorer correspondence: bun harness, table drift diff, and the refl proof
# that the certified checker agrees with the explorer on all 546 configurations.
correspondence:
    bash scripts/correspondence.sh
