{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

module FalseEpistemicNonVacuity where

open import ResidualEvidence.Prelude
open import EpistemicTypes.Warrant
open import EpistemicComparison using (unsound-bottom-token)

-- Must fail (hyperpolymath/nextgen-typing#115 AC3): a non-factive warrant and its token
-- do not provide the SoundWarrant required to extract the purported claim.
invalid : ⊥
invalid = sound-epi (Epi.warrant unsound-bottom-token)
  (Epi.evidence unsound-bottom-token)
