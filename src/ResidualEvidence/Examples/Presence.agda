{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

module ResidualEvidence.Examples.Presence where

open import ResidualEvidence.Prelude
open import ResidualEvidence.Core

World : Set
World = Nat × Nat

contribution noise : World → Nat
contribution = fst
noise = snd

observe : World → Nat
observe world = contribution world + noise world

Unrestricted NoiseBound Conflict : World → Set
Unrestricted world = ⊤
NoiseBound world = noise world ≤ 1
Conflict world = NoiseBound world × (contribution world ≡ 0)

Present : World → Set
Present world = ¬ (contribution world ≡ 0)

zero-two : Candidate observe 2 Unrestricted
zero-two = (0 , 2) , refl , tt

two-zero : Candidate observe 2 Unrestricted
two-zero = (2 , 0) , refl , tt

unrestricted : Case observe 2 Unrestricted
unrestricted = inhabited zero-two

residual-alone-does-not-imply-presence : ¬ Holds unrestricted Present
residual-alone-does-not-imply-presence claim = claim zero-two refl

residual-alone-does-not-imply-absence : ¬ Holds unrestricted (λ w → contribution w ≡ 0)
residual-alone-does-not-imply-absence claim with claim two-zero
... | ()

one-one : Candidate observe 2 NoiseBound
one-one = (1 , 1) , refl , s≤s z≤n

bounded-two-zero : Candidate observe 2 NoiseBound
bounded-two-zero = (2 , 0) , refl , z≤n

bounded : Case observe 2 NoiseBound
bounded = inhabited one-one

two-not-at-most-one : ¬ (2 ≤ 1)
two-not-at-most-one (s≤s ())

bounded-presence : Holds bounded Present
bounded-presence ((zero , n) , refl , bound) eq = two-not-at-most-one bound
bounded-presence ((suc u , n) , observed , bound) ()

one-not-two : ¬ (1 ≡ 2)
one-not-two ()

bounded-value-not-identified : ¬ Identified bounded contribution
bounded-value-not-identified =
  different-candidates-refute-identification bounded contribution one-one bounded-two-zero one-not-two

-- Inconsistent constraints cannot provide an inhabited case.
conflict-has-no-candidate : ¬ Candidate observe 2 Conflict
conflict-has-no-candidate (world , observed , bound , absent) =
  bounded-presence (world , observed , bound) absent

conflict-has-no-case : ¬ Case observe 2 Conflict
conflict-has-no-case c = conflict-has-no-candidate (Case.witness c)

-- Positive control: exact value identification is possible with enough evidence.
NoNoise : World → Set
NoNoise world = noise world ≡ 0

no-noise : Case observe 2 NoNoise
no-noise = inhabited ((2 , 0) , refl , refl)

plus-zero : (n : Nat) → n + 0 ≡ n
plus-zero zero = refl
plus-zero (suc n) = cong suc (plus-zero n)

no-noise-identifies-two : Identified no-noise contribution
no-noise-identifies-two = 2 , λ { ((u , zero) , observed , refl) → trans (sym (plus-zero u)) observed }

bounded-warrants-actual-presence : (actual : World) →
  observe actual ≡ 2 → NoiseBound actual → Present actual
bounded-warrants-actual-presence = actual-world-sound bounded bounded-presence
