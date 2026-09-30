{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

module FalseFiniteEntailment where

open import Agda.Builtin.Int using (pos)
open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import ResidualEvidence.Finite.Row using (exact; entailed)
open import ResidualEvidence.Finite.Checker using (config; presence)

-- Must fail: residual 2 with noise bound 6 through the exact view, assuming
-- the latent is zero, leaves only the world (0, 2), so the checker refutes
-- presence.  Claiming it is entailed is a closed false equation, and the
-- checker decides it by normalisation: refuted != entailed.
invalid : presence (config (pos 2) 6 exact true) ≡ entailed
invalid = refl
