{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

module FalseEpistemicLocalRecovery where

open import ResidualEvidence.Prelude
open import ResidualEvidence.Core
open import EpistemicTypes.PartialRecovery using (PartialRecovery)
open import EpistemicPartialRecovery
open import EpistemicPartialRecoveryExamples

-- This local identification is valid. The other fibre still collides,
-- so it cannot establish the global source-separation obligation.
local-identification : Identified singleton (λ x → x)
local-identification = singleton-identified

invalid : PartialRecovery colliding
invalid = identified-cases-to-partial {C = colliding}
  (λ _ _ _ → local-identification) colliding-decide
