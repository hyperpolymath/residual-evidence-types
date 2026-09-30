{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

-- The row vocabulary shared by the certified finite checker
-- (ResidualEvidence.Finite.Checker) and the table generated from the
-- explorer's JavaScript model (tests/correspondence/ExplorerTable.agda).
-- The correspondence theorem is `Checker.table ≡ ExplorerTable.expected`
-- by refl, so both producers must agree on this vocabulary exactly.
--
-- Integers are spelled with the builtin constructors: `pos n` for n ≥ 0 and
-- `negsuc n` for −(n+1).  So −6 is `negsuc 5` and 6 is `pos 6`.

module ResidualEvidence.Finite.Row where

open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.List using (List)

-- The explorer's three observation views:
-- exact = x ↦ x, sign = Math.sign, magnitude = Math.abs.
data View : Set where
  exact sign magnitude : View

-- decide(c, w => w.latent !== 0).status in the explorer.
data Verdict : Set where
  entailed refuted unresolved inconsistent : Verdict

-- identify(c, w => w.latent).status in the explorer; the explorer's
-- 'inconsistent' status for an empty candidate set is `no-candidate` here.
data IdStatus : Set where
  identified unidentified no-candidate : IdStatus

record Row : Set where
  constructor row
  field
    residual   : Int       -- −6 .. 6
    noiseBound : Nat       -- 0 .. 6
    view       : View
    assumeZero : Bool
    count      : Nat       -- c.candidates.length
    presence   : Verdict
    identity   : IdStatus
    values     : List Int  -- identify(c, w => w.latent).values: ascending, no duplicates
