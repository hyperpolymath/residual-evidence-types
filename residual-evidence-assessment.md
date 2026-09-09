<!-- SPDX-License-Identifier: CC-BY-SA-4.0 -->
<!-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell -->
# Residual Evidence: assessment and starting plan

**Recommended and accepted repository name: `hyperpolymath/residual-evidence`.**

The proposed technical description is **evidence-indexed residual types**. “Confounding types” remains the original working term and a prospective specialised family: first establish a coherent general framework, then develop the additional causal semantics. The README contains that history and future direction explicitly.

## The judgement

This is legitimate to investigate as a formal library. The current core does **not** establish a new primitive type, nor is splitting structured discrepancy from noise a new statistical idea. The promising work is an interface that keeps alternative decompositions and their evidence obligations attached as observations and claims are transformed.

The closest statistical predecessor found is discrepancy modelling: Kennedy and O’Hagan’s calibration work, followed by Brynjarsdottir and O’Hagan’s analysis of the distinction between model discrepancy and observation error and the identification problems that remain. [Kennedy and O’Hagan](https://www.tonyohagan.co.uk/academic/abs/calib.html), [Brynjarsdottir and O’Hagan](https://www.tonyohagan.co.uk/academic/pdf/simmach.pdf)

Uncertainty already has programming-language abstractions, including `Uncertain<T>`. Reasoning with sets of compatible values instead of an identified point also has a substantial foundation in partial identification. Consequently, broad claims such as “the first type for uncertainty” or “the first way to separate the error term” would be incorrect. [Uncertain<T>](https://www.cs.utexas.edu/~mckinley/papers/uncertainty-asplos-2014.pdf), [Manski’s introduction](https://www.cemmap.ac.uk/wp-content/legacy/forms/manskipaper.pdf)

The bounded literature review found no clear exact counterpart to the complete proposed interface, but it cannot certify uniqueness. More importantly, the interface is already expressible with ordinary dependent constructions. A mathematical equivalence in the starter makes that explicit.

## The minimal object

Declare a model/observation function, an observation, and evidence constraints:

\[
\operatorname{Candidate}(\mathrm{observe},r,E)
=\sum_{w:W}\bigl(\mathrm{observe}(w)=r\bigr)\times E(w).
\]

This is an evidence-refined preimage fibre, directly related to your Echo Types. A candidate is a possible world, not the recovered actual world. A claim is warranted within a case only if it holds for every admissible candidate. Connecting that conditional claim to reality requires the separate premise that the actual world is among those candidates.

Your existing Epistemic Types already supplies closely related ideas about warrants and sound proof transport. The research must compare against that strong combination, not only against a weak pair of numbers or independent uncertainty wrappers. [Echo Types](https://github.com/hyperpolymath/echo-types), [Epistemic Types](https://github.com/hyperpolymath/epistemic-types)

## The first discriminating example

Take natural-number contributions with

\[
r=u+n=2.
\]

With no additional restriction, `(u,n)=(0,2)` and `(2,0)` are both possible. A nonzero residual therefore does not establish a nonzero `u`.

Add the explicit assumption `n≤1`. Now `u` must be nonzero, but both `(1,1)` and `(2,0)` remain possible. You can establish **presence without identifying the value**. Identifying a value still need not identify its source or causal role.

The browser explorer uses a separate signed-integer model, so it can also show cancellation, loss of sign, and contradictory constraints. Its candidate counts are not probabilities.

## Agda and the proof ladder

**Agda is a suitable first choice, and the starter already checks with Agda 2.8.0.1 under `--safe --without-K`.** It uses bundled builtins only. Safe mode restricts logical escape hatches; without-K avoids assuming uniqueness of identity proofs through unrestricted equality elimination. [Safe Agda](https://agda.readthedocs.io/en/stable/language/safe-agda.html), [Without K](https://agda.readthedocs.io/en/stable/language/without-k.html)

| Stage | What to establish | Current evidence |
|---|---|---|
| 1 | Nonempty observation-indexed cases and the ordinary fibre encoding | Agda checked |
| 2 | Two indistinguishable observations can forbid exact recovery of a query | Agda checked |
| 3 | Presence under a noise bound, while exact value remains unidentified | Agda checked |
| 4 | Conditional claim soundness, refinement, feasible intersection and coarsening | Basic Agda laws checked |
| 5 | Preserve dependencies across composition; handle revision and retraction | Proposed |
| 6 | Certified finite checker and correspondence with the explorer | Prototype tested; proof pending |
| 7 | A small calculus, if it earns its place through comparison | Proposed |
| 8 | Confounding types with precise causal models and warrant-preserving embedding | Prospective specialisation |
| 9 | Quantitative uncertainty adapters and any executable interface | Later, driven by specific use cases |

Lean/Mathlib or Isabelle may become useful if the central obstacle becomes probability, measure theory or substantial statistical mathematics. There is no reason to port the constructive core merely to start. An Idris2/Zig interface should wait until there is an actual executable boundary to verify.

## What is in the starter

- Canonical `README.adoc` and `docs/EXPLAINME.adoc`.
- A primary-source prior-work review and explicit novelty/stop criteria.
- A proof ladder and naming/prover decision record.
- A dedicated note on the prospective confounding-types specialisation.
- Seven Agda modules and two deliberately invalid proofs that must be rejected.
- A dependency-free offline explorer and nine behavioral checks.
- A pinned Agda CI workflow, Just recipes, project STATE and a guarded overlay installer.
- Instructions for creating the project from the current canonical RSR template.

The first lines for a future creation are:

```bash
gh repo create hyperpolymath/residual-evidence \
  --template hyperpolymath/rsr-template-repo --private --clone
cd residual-evidence
just repo-init
```

Then follow `START-HERE.adoc` in the archive to checkpoint the instantiation, apply the payload and run the checks. **No GitHub repository has been created or published as part of this work.**

## Verification and limits

The Agda core and both expected-rejection controls pass. Nine behavioral checks pass under Node.js v24.19.0. The installer was checked on a temporary Git fixture, including dirty-target refusal and preservation of a legal file. The full RSR instantiation, remote CI and Bun execution have not been run. Browser visual inspection was blocked by the available browser’s local/data URL policy.

The decisive next work is dependency-preserving composition, a certified finite checker, and explicit evidence revision. If those bring no meaningful benefit beyond direct use of the existing fibre and warrant libraries, this can become an application module of those foundations. It need not be promoted into another fundamental type to be useful.
