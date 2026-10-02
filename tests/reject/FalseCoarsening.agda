{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
module FalseCoarsening where
open import ResidualEvidence.Prelude
open import ResidualEvidence.Core
open import ResidualEvidence.Composition
open import ResidualEvidence.Examples.Presence
open import ResidualEvidence.Examples.Composition using (positive)

-- Must fail: coarsening the observation to "positive or not" keeps every fine
-- candidate and admits (0 , 1) as well, which is silent.  A claim proved at
-- the fine observation therefore does not transfer to the coarse one; only
-- the other direction is available.
invalid : Holds bounded Present → Holds (coarsen-case positive bounded) Present
invalid = coarsen-claim positive bounded
