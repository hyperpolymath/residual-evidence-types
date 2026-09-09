# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
set shell := ["bash", "-euo", "pipefail", "-c"]

# Core proofs and semantic expected-rejection controls (Agda builtins only).
check:
    bash scripts/check.sh

# Check against the actual epistemic-types source directory supplied by the caller.
check-epistemic epistemic_src:
    agda --safe --without-K --no-libraries --ignore-interfaces -i src -i tests/integration -i '{{epistemic_src}}' tests/integration/EpistemicComparison.agda

# Check against the actual echo-types source and Agda standard library.
check-echo echo_src stdlib_src:
    agda --safe --without-K --no-libraries --ignore-interfaces -i src -i tests/integration -i '{{echo_src}}' -i '{{stdlib_src}}' tests/integration/EchoComparison.agda
