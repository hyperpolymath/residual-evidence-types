{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
module FalseWeakening where
open import ResidualEvidence.Prelude
open import ResidualEvidence.Context
open import ResidualEvidence.Examples.Presence

-- Must fail: a thinning restricts evidence from the larger context to the
-- smaller one. Read the other way it would manufacture a noise bound out
-- of no assumption at all (the bounded-observation fallacy).
invalid : (world : World) → ⟦ [] ⟧ world → ⟦ NoiseBound ∷ [] ⟧ world
invalid = weaken (drop {P = NoiseBound} done)
