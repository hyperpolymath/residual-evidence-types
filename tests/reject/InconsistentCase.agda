{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
module InconsistentCase where
open import ResidualEvidence.Prelude
open import ResidualEvidence.Core
open import ResidualEvidence.Examples.Presence

-- Must fail: the proposed witness violates the noise bound.
invalid : Case observe 2 Conflict
invalid = inhabited ((0 , 2) , refl , (s≤s z≤n , refl))
