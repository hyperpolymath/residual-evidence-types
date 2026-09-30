{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

module FalseFiniteSoundness where

open import Agda.Builtin.Equality using (_≡_)
open import ResidualEvidence.Core using (Holds)
open import ResidualEvidence.Finite.Checker
  using (Config; World; FiniteCase; observe; target; Bounded; Zero)
open import ResidualEvidence.Finite.Soundness using (finite-actual-sound)

-- Must fail: the explorer's loop bounds are an assumption about the world,
-- not a fact about it.  Transferring a finite verdict to an actual world
-- while supplying only the noise bound and the zero assumption leaves the
-- in-range premise unmet, and finite-actual-sound demands it explicitly.
invalid : ∀ (cfg : Config) (c : FiniteCase cfg) (claim : World → Set) → Holds c claim →
  (actual : World) → observe cfg actual ≡ target cfg →
  Bounded cfg actual → Zero cfg actual → claim actual
invalid cfg c claim holds actual observed bounded assumed =
  finite-actual-sound cfg c claim holds actual observed bounded assumed
