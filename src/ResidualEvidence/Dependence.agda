{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
--
-- DECISION-002 test 1, re-proved against this repository's own record.
--
-- Assumption dependence is NOT a function of the candidate set.  Two
-- contexts with pointwise logically equivalent candidate sets — the same
-- worlds satisfying the same conditions, up to equivalence — differ in
-- what a claim can be made to rest on: the duplicated assumption can be
-- dropped in one and not in the other.  A box sees worlds; dependence
-- sees assumptions.  That is structure the frame forgets, and the
-- family half of DECISION-002 is checked here.
--
-- The mirror of this test ran first, in epistemic-types
-- (`EpistemicTypes.Kripke.Dependence`, epistemic-types@5422cd5): a faithful
-- mirror of this repository's Dependent.  This module does not import the
-- mirror: it re-proves the test against residual-evidence-types' own
-- Case, Ctx, thinning and Dependent records (same kernel, same shape).
--
-- Grade 3 (Agda-only), per the estate's mathematical architecture: this
-- module uses the Agda builtins and this repository's own modules only;
-- Agda 2.6.4.1, --safe --without-K, no axioms beyond the builtin ones.
-- The machinery is ordinary — a Σ-fibre, a list of assumptions, a
-- thinning order — and nothing here claims a new primitive type theory.

module ResidualEvidence.Dependence where

open import ResidualEvidence.Prelude
open import ResidualEvidence.Core
open import ResidualEvidence.Context
open import ResidualEvidence.Revision
open import Agda.Primitive using (lzero; lsuc)

-- A support is proper when it drops at least one assumption of Γ.
Proper : ∀ {w} {W : Set w} {Γ Δ : Ctx W} → Δ ⊆ Γ → Set
Proper done     = ⊥
Proper (keep t) = Proper t
Proper (drop t) = ⊤

-- A claim under Γ that rests on a proper (strictly weaker) support.
ProperlyDependent : ∀ {w o p} {W : Set w} {O : Set o} {observe : W → O} {r : O}
  {Γ : Ctx W} (c : Case observe r ⟦ Γ ⟧) (P : W → Set p) →
  Set (lsuc lzero ⊔ w ⊔ o ⊔ p)
ProperlyDependent c P = Σ (Dependent c P) (λ d → Proper (Dependent.thin d))

----------------------------------------------------------------------
-- The witness: two contexts with the same candidates.

data W : Set where
  u v : W

P : W → Set
P u = ⊤
P v = ⊥

Γ₁ Γ₂ : Ctx W
Γ₁ = P ∷ []
Γ₂ = P ∷ P ∷ []

-- The two candidate sets are pointwise logically equivalent: at every
-- world, Γ₂-evidence is Γ₁-evidence with the duplicated assumption twice.
same-candidates : ∀ w → (⟦ Γ₁ ⟧ w → ⟦ Γ₂ ⟧ w) × (⟦ Γ₂ ⟧ w → ⟦ Γ₁ ⟧ w)
same-candidates w = (λ { (p , tt) → p , p , tt }) , (λ { (p , _ , tt) → p , tt })

observe : W → ⊤
observe _ = tt

r : ⊤
r = tt

c₁ : Case observe r ⟦ Γ₁ ⟧
c₁ = inhabited (u , refl , tt , tt)

c₂ : Case observe r ⟦ Γ₂ ⟧
c₂ = inhabited (u , refl , tt , tt , tt)

-- Under Γ₂ the claim can rest on strictly less than Γ₂: the duplicated
-- assumption can be dropped (support P ∷ [] thins into P ∷ P ∷ []), and
-- the claim still holds under the support — at every candidate.
properly-in-Γ₂ : ProperlyDependent c₂ P
properly-in-Γ₂ = rests-on (P ∷ []) (drop (keep done)) claim , tt
  where
  claim : Holds (case-weaken (drop (keep done)) c₂) P
  claim (w , observed , (p , tt)) = p

-- Under Γ₁ it cannot.  The only proper supports are the empty context
-- (drop done — and P fails at v); keep done is not proper at all.
not-properly-in-Γ₁ : ProperlyDependent c₁ P → ⊥
not-properly-in-Γ₁ (rests-on _ (keep done) _ , ())
not-properly-in-Γ₁ (rests-on _ (drop done) claim , _) = claim (v , refl , tt)
