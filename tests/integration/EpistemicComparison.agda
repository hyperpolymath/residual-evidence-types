{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

module EpistemicComparison where

open import ResidualEvidence.Prelude
open import ResidualEvidence.Core
open import ResidualEvidence.Examples.Presence
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

-- A concrete token of the actual Epistemic interface proves model-relative
-- presence at (1,1), with observation equality and the noise bound supplied.
example : Present (1 , 1)
example = sound-epi
  (actual-warrant {P = Present} bounded (1 , 1) refl (s≤s z≤n))
  bounded-presence
