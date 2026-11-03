{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

module FalseEchoComposition where

open import ResidualEvidence.Prelude
open import ResidualEvidence.Context
open import ResidualEvidence.Composition
open import ResidualEvidence.Examples.Presence
open import ResidualEvidence.Examples.Composition
  using (Bounded; NoNoisy; bounded-presence-ctx; no-noise-two-ctx)
open import EchoComparison

-- Replacing the explicitly inhabited joint case with the left case loses
-- the NoNoise premise needed for contribution ≡ 2.
invalid : EchoHolds echo-bounded (λ world → Present world × (contribution world ≡ 2))
invalid =
  compose-echo-claims {Γ = Bounded} {Δ = NoNoisy}
    echo-bounded echo-no-noise echo-bounded
    (λ x → bounded-presence-ctx (from-echo x))
    (λ x → no-noise-two-ctx (from-echo x))
