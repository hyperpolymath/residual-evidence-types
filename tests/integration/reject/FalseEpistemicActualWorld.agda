{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

module FalseEpistemicActualWorld where

open import ResidualEvidence.Prelude
open import ResidualEvidence.Examples.Presence
open import EpistemicTypes.Warrant
open import EpistemicComparison using (actual-warrant)

-- Must fail (hyperpolymath/nextgen-typing#115 AC3): the inhabited bounded case and an
-- observation match do not supply the noise bound for an arbitrary actual
-- world. Omitting that premise leaves a function, not a SoundWarrant.
invalid : (actual : World) → observe actual ≡ 2 → Present actual
invalid actual observed =
  sound-epi (actual-warrant {P = Present} bounded actual observed)
    bounded-presence
