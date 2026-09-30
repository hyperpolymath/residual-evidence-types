{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

module FalseIntEquality where

open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import ResidualEvidence.Finite.Int

-- Must fail: −1 and 1 are different integers, so the decidable test is false.
invalid : (negsuc 0 ==ᵢ pos 1) ≡ true
invalid = refl
