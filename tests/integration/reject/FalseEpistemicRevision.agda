{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

module FalseEpistemicRevision where

open import ResidualEvidence.Prelude
open import ResidualEvidence.Revision
open import ResidualEvidence.Examples.Presence
open import ResidualEvidence.Examples.Composition using (both)
open import ResidualEvidence.Examples.Revision using (to-balanced; balanced-ctx)
open import EpistemicComparison
  using (revise-warrant-sound; two-rests-on-no-noise)

-- Must fail (hyperpolymath/nextgen-typing#115 AC3): revision replaces NoNoise with the
-- balanced assumption, so support from the old context cannot justify
-- carrying contribution = 2 into the revised world (1,1).
invalid : contribution (1 , 1) ≡ 2
invalid =
  revise-warrant-sound to-balanced both balanced-ctx two-rests-on-no-noise
    (Dependent.thin two-rests-on-no-noise)
    (1 , 1) refl (s≤s z≤n , refl , tt)
