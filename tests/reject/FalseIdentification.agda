{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
module FalseIdentification where
open import ResidualEvidence.Prelude
open import ResidualEvidence.Core
open import ResidualEvidence.Examples.Presence

-- Must fail: a compatible world need not have u = 2.
invalid : Identified bounded contribution
invalid = 2 , λ candidate → refl
