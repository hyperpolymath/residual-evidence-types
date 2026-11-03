{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

module FalseEchoCoarsening where

open import ResidualEvidence.Prelude
open import ResidualEvidence.Examples.Presence
open import ResidualEvidence.Examples.Composition using (positive)
open import EchoComparison

-- A fine-observation proof cannot consume a coarse candidate. The latter
-- includes (0 , 1), whose observation is positive but whose contribution is 0.
invalid : EchoHolds (coarsen-echo-case positive (to-echo-case bounded)) Present
invalid = λ x → bounded-presence (from-echo x)
