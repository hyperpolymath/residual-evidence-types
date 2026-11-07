{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

module FalseEpistemicWitnessRecovery where

open import ResidualEvidence.Prelude
open import ResidualEvidence.Core
open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Maybe using (just)
open import EpistemicTypes.PartialRecovery using (retainedPair)
open import EpistemicPartialRecovery
open import EpistemicPartialRecoveryExamples

collision-case : PairCase colliding false tt (λ _ → ⊤)
collision-case = inhabited (left , refl , tt)

-- Projecting this case's consistency witness gives left even when the
-- generated pair came from right. Its source projection is not a decoder.
chosen : Source
chosen = fst (Case.witness collision-case)

alternative : Candidate (retainedPair colliding) (false , tt) (λ _ → ⊤)
alternative = right , refl , tt

invalid : just chosen ≡ just (fst alternative)
invalid = refl
