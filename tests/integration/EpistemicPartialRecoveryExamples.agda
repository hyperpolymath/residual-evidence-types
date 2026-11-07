{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

module EpistemicPartialRecoveryExamples where

open import ResidualEvidence.Prelude
open import ResidualEvidence.Core
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Maybe using (just)
open import EpistemicTypes.EchoBridge using (Retention)
open import EpistemicTypes.PartialRecovery
  using (PartialRecovery; ImageDecision; Decision; yes; partialSeparates;
         retainedPair; SuccessSound)
open import EpistemicPartialRecovery

data Source : Set where solo left right : Source

-- One fibre is a singleton; another collides. Identification at one
-- observation therefore cannot imply a decoder for the entire retention.
visible : Source → Bool
visible solo = true
visible left = false
visible right = false

colliding : Retention Source Bool ⊤
colliding = record
  { observe = visible; retain = λ _ → tt
  ; Cert = λ _ _ → ⊤; sound = λ _ → tt }

singleton : PairCase colliding true tt (λ _ → ⊤)
singleton = inhabited (solo , refl , tt)

only-solo : Holds singleton (λ x → x ≡ solo)
only-solo (solo , refl , tt) = refl
only-solo (left , () , tt)
only-solo (right , () , tt)

singleton-identified : Identified singleton (λ x → x)
singleton-identified = solo , only-solo

no-global-partial-recovery : ¬ PartialRecovery colliding
no-global-partial-recovery rec with partialSeparates rec {left} {right} refl
... | ()

-- Even decidable image membership does not repair the colliding fibre.
colliding-decide : ImageDecision colliding
colliding-decide true tt = yes (solo , refl)
colliding-decide false tt = yes (left , refl)

-- An explicit decision procedure supplies the converse's missing data.
-- Here the retained pair contains the whole source, so this is executable
-- recovery from the pair, with no candidate/Case witness as decoder input.
faithful : Retention Source Source ⊤
faithful = record
  { observe = λ x → x; retain = λ _ → tt
  ; Cert = λ _ _ → ⊤; sound = λ _ → tt }

faithful-decide : ImageDecision faithful
faithful-decide y tt = yes (y , refl)

faithful-identifies : AllPairCasesIdentified faithful
faithful-identifies y r = separation-identifies {C = faithful} (cong fst)

faithful-partial : PartialRecovery faithful
faithful-partial = identified-cases-to-partial {C = faithful}
  faithful-identifies faithful-decide

faithful-sound : SuccessSound faithful-partial
faithful-sound = identified-cases-success-sound {C = faithful}
  faithful-identifies faithful-decide

faithful-decodes-right : PartialRecovery.decode faithful-partial right tt ≡ just right
faithful-decodes-right = refl
