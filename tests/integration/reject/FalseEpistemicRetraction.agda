{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

module FalseEpistemicRetraction where

open import ResidualEvidence.Prelude
open import ResidualEvidence.Revision
open import ResidualEvidence.Examples.Presence
open import ResidualEvidence.Examples.Composition using (both)
open import ResidualEvidence.Examples.Revision using (drop-no-noise)
open import EpistemicComparison
  using (retract-warrant-sound; two-rests-on-no-noise)

-- Must fail (hyperpolymath/nextgen-typing#115 AC3): the support thinning valid before
-- retraction does not witness that NoNoise survives in the remaining context.
invalid : contribution (1 , 1) ≡ 2
invalid =
  retract-warrant-sound drop-no-noise both two-rests-on-no-noise
    (Dependent.thin two-rests-on-no-noise)
    (1 , 1) refl (s≤s z≤n , tt)
