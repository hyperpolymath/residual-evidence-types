{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

module EpistemicComparison where

open import Agda.Primitive using (lzero)
open import ResidualEvidence.Prelude
open import ResidualEvidence.Core
open import ResidualEvidence.Context
open import ResidualEvidence.Composition
open import ResidualEvidence.Revision
open import ResidualEvidence.Examples.Presence
open import ResidualEvidence.Examples.Composition
  using (Bounded; NoNoisy; both; no-noise-two-ctx)
open import ResidualEvidence.Examples.Revision
  using (presence-rests-on-bound; drop-no-noise; to-balanced; balanced-ctx)
open import EpistemicTypes.Warrant

-- Imports the real sibling interface. The actual-world premises remain
-- explicit; a token for a conditional claim alone cannot establish reality.
actual-warrant : ∀ {w o e p} {W : Set w} {O : Set o}
  {observe : W → O} {r} {E : W → Set e} {P : W → Set p}
  (c : Case observe r E) (actual : W) → observe actual ≡ r → E actual →
  SoundWarrant {wℓ = w ⊔ o ⊔ e ⊔ p} ⊤ tt (P actual)
actual-warrant {P = P} c actual observed evidence =
  soundWarrant (mkWarrant (Holds c P))
    (λ claim → actual-world-sound c claim actual observed evidence)

-- Non-vacuity for the residual claim token (hyperpolymath/nextgen-typing#115 AC3).
-- Inhabitation rules out a candidate-wide proof of falsehood without
-- assuming that the chosen witness is the actual world.
holds-non-vacuous : ∀ {w o e} {W : Set w} {O : Set o}
  {observe : W → O} {r : O} {E : W → Set e}
  (c : Case observe r E) → ¬ Holds c (λ _ → ⊥)
holds-non-vacuous c token = token (Case.witness c)

-- The actual sibling's evidence projection is precisely that residual
-- claim type. This rules out a token for this transported SoundWarrant,
-- not arbitrary non-factive warrants in the sibling interface.
warrant-non-vacuous : ∀ {w o e} {W : Set w} {O : Set o}
  {observe : W → O} {r : O} {E : W → Set e}
  (c : Case observe r E) (actual : W)
  (observed : observe actual ≡ r) (evidence : E actual) →
  ¬ Warrant.Evidence (SoundWarrant.warrant
      (actual-warrant {P = λ _ → ⊥} c actual observed evidence))
warrant-non-vacuous c actual observed evidence = holds-non-vacuous c

-- Positive control for the sibling's deliberate non-factivity: a token
-- may purport to warrant falsehood without supplying a proof of falsehood.
unsound-bottom-token : Epi {wℓ = lzero} ⊤ tt ⊥
unsound-bottom-token = epi (mkWarrant ⊤) tt

-- Conflict prevents the residual Case component of this pair. The theorem
-- makes no claim that an arbitrary Epi token is impossible on its own.
conflict-admits-no-case-and-token : ∀ {A : Set} →
  ¬ Σ (Case observe 2 Conflict) (λ _ → Epi {wℓ = lzero} ⊤ tt A)
conflict-admits-no-case-and-token (c , _) = conflict-has-no-case c

-- Retraction changes the claim token's context. A sound warrant for an
-- actual world still requires observation equality and the remaining evidence.
retracted-warrant : ∀ {w o p} {W : Set w} {O : Set o}
  {observe : W → O} {r : O} {Γ Δ : Ctx W} {P : W → Set p}
  (ret : Retraction Γ Δ) (c : Case observe r ⟦ Γ ⟧)
  (actual : W) → observe actual ≡ r → ⟦ Δ ⟧ actual →
  SoundWarrant {wℓ = w ⊔ o ⊔ p} ⊤ tt (P actual)
retracted-warrant {P = P} ret c =
  actual-warrant {P = P} (retract-case ret c)

-- A retained support supplies the retracted warrant's token.
retract-warrant-sound : ∀ {w o p} {W : Set w} {O : Set o}
  {observe : W → O} {r : O} {Γ Δ : Ctx W} {P : W → Set p}
  (ret : Retraction Γ Δ) (c : Case observe r ⟦ Γ ⟧)
  (dep : Dependent c P) → support dep ⊆ Δ →
  (actual : W) → observe actual ≡ r → ⟦ Δ ⟧ actual → P actual
retract-warrant-sound {P = P} ret c dep retained actual observed evidence =
  sound-epi (retracted-warrant {P = P} ret c actual observed evidence)
    (survives-retraction ret c dep retained)

-- Revision requires support in the intermediate context and an explicitly
-- inhabited revised case. Neither is manufactured by an epistemic token.
revise-warrant-sound : ∀ {w o p} {W : Set w} {O : Set o}
  {observe : W → O} {r : O} {Γ Γ′ : Ctx W} {P : W → Set p}
  (rev : Revision Γ Γ′) (c : Case observe r ⟦ Γ ⟧)
  (c′ : Case observe r ⟦ Γ′ ⟧)
  (dep : Dependent c P) → support dep ⊆ middle rev →
  (actual : W) → observe actual ≡ r → ⟦ Γ′ ⟧ actual → P actual
revise-warrant-sound {P = P} rev c c′ dep retained actual observed evidence =
  sound-epi (actual-warrant {P = P} c′ actual observed evidence)
    (revise rev c c′ dep retained)

-- This support witness is checked positively before rejection controls try
-- to reuse its old-context thinning after NoNoise has been removed.
two-rests-on-no-noise : Dependent both (λ world → contribution world ≡ 2)
two-rests-on-no-noise =
  rests-on NoNoisy (⊆-++ʳ {Γ = Bounded} {Δ = NoNoisy}) no-noise-two-ctx

-- A concrete token proves presence at (1,1), with both actual-world
-- premises supplied. This world was excluded by the NoNoise assumption.
example : Present (1 , 1)
example = sound-epi
  (actual-warrant {P = Present} bounded (1 , 1) refl (s≤s z≤n))
  bounded-presence

-- Presence rests on the bound, so it survives removing NoNoise and also
-- replacing NoNoise by the balanced assumption (contribution equals noise).
retracted-example : Present (1 , 1)
retracted-example =
  retract-warrant-sound drop-no-noise both presence-rests-on-bound ⊆-refl
    (1 , 1) refl (s≤s z≤n , tt)

revised-example : Present (1 , 1)
revised-example =
  revise-warrant-sound to-balanced both balanced-ctx presence-rests-on-bound ⊆-refl
    (1 , 1) refl (s≤s z≤n , refl , tt)

-- Before retraction the NoNoise-dependent claim has a valid token and
-- establishes contribution 2 at the admissible world (2,0).
two-before-retraction : contribution (2 , 0) ≡ 2
two-before-retraction = sound-epi
  (actual-warrant {P = λ world → contribution world ≡ 2}
    both (2 , 0) refl (z≤n , refl , tt))
  (dependent-holds both two-rests-on-no-noise)
