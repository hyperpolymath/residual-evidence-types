#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0

set -euo pipefail

here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
fixture=$(mktemp -d)
trap 'rm -rf -- "$fixture"' EXIT

# No runner at all: red.
if GITHUB_WORKSPACE=$fixture "$here/check.sh"; then
  echo "absent proof runner unexpectedly passed" >&2
  exit 1
fi

# A runner that prints a success line but exits non-zero: red. This is the
# vacuous shape the gate replaced; its text must not be mistaken for a verdict.
mkdir -p "$fixture/scripts"
printf '#!/usr/bin/env bash\necho "All detected proofs executed successfully."\nexit 1\n' > "$fixture/scripts/check.sh"
if GITHUB_WORKSPACE=$fixture "$here/check.sh"; then
  echo "failing proof runner unexpectedly passed" >&2
  exit 1
fi

# A runner that passes: green, and its own output is shown.
printf '#!/usr/bin/env bash\necho "PASS: fixture proofs"\n' > "$fixture/scripts/check.sh"
out=$(GITHUB_WORKSPACE=$fixture "$here/check.sh")
grep -q 'PASS: fixture proofs' <<<"$out"

# A runner at a configured path is honoured; a configured path that is missing
# is red even though the default runner exists.
printf '#!/usr/bin/env bash\nexit 0\n' > "$fixture/verify.sh"
GITHUB_WORKSPACE=$fixture PROOF_RUNNER=verify.sh "$here/check.sh"
if GITHUB_WORKSPACE=$fixture PROOF_RUNNER=missing.sh "$here/check.sh"; then
  echo "missing configured proof runner unexpectedly passed" >&2
  exit 1
fi

echo 'proof-runner-check controls passed'
