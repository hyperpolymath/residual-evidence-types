{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

module FalseRetraction where

open import ResidualEvidence.Prelude
open import ResidualEvidence.Core
open import ResidualEvidence.Context
open import ResidualEvidence.Revision
open import ResidualEvidence.Examples.Presence
open import ResidualEvidence.Examples.Composition using (bounded-ctx)
open import ResidualEvidence.Examples.Revision using (drop-bound; presence-rests-on-bounded)

-- Must fail: presence rests on NoiseBound, the very assumption drop-bound
-- retracts, so its support [NoiseBound] does not thin into the empty context.
invalid : Holds (retract-case drop-bound bounded-ctx) Present
invalid = survives-retraction drop-bound bounded-ctx presence-rests-on-bounded done
