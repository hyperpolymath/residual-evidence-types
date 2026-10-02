{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

-- The Presence example composed: a noise bound establishes presence, no noise
-- identifies the contribution, and under both assumptions together the
-- composed case yields Present × (contribution ≡ 2).  The composed case is
-- inhabited explicitly by the world (2 , 0).  Coarsening the observation to
-- "positive or not" keeps the candidate (0 , 1), which contributes nothing,
-- so presence is lost at the coarse observation while a claim proved there
-- (the observation is at least 1) transfers back to the fine case.

module ResidualEvidence.Examples.Composition where

open import ResidualEvidence.Prelude
open import ResidualEvidence.Core
open import ResidualEvidence.Context
open import ResidualEvidence.Composition
open import ResidualEvidence.Examples.Presence
open import Agda.Builtin.Bool using (Bool; true; false)

-- Each assumption as a one-element context, and their composition.
Bounded NoNoisy : Ctx World
Bounded = NoiseBound ∷ []
NoNoisy = NoNoise ∷ []

bounded-ctx : Case observe 2 ⟦ Bounded ⟧
bounded-ctx = inhabited ((1 , 1) , refl , s≤s z≤n , tt)

no-noise-ctx : Case observe 2 ⟦ NoNoisy ⟧
no-noise-ctx = inhabited ((2 , 0) , refl , refl , tt)

-- The composed case is inhabited explicitly; nothing derives it from the parts.
both : Case observe 2 ⟦ Bounded ++ NoNoisy ⟧
both = inhabited ((2 , 0) , refl , z≤n , refl , tt)

-- The Presence results, restated over contexts.
bounded-presence-ctx : Holds bounded-ctx Present
bounded-presence-ctx = refine-claim bounded bounded-ctx (λ world → fst) bounded-presence

no-noise-two-ctx : Holds no-noise-ctx (λ world → contribution world ≡ 2)
no-noise-two-ctx =
  refine-claim no-noise no-noise-ctx (λ world → fst) (snd no-noise-identifies-two)

-- [NoiseBound] ++ [NoNoise] yields presence and the identified value at once.
present-and-two : Holds both (λ world → Present world × (contribution world ≡ 2))
present-and-two = compose-claims bounded-ctx no-noise-ctx both bounded-presence-ctx no-noise-two-ctx

-- The composed case thins back to its components, keeping the world (2 , 0).
both-is-bounded : Case.witness (component-left {Γ = Bounded} {NoNoisy} both) ≡ ((2 , 0) , refl , z≤n , tt)
both-is-bounded = refl

both-is-no-noise : Case.witness (component-right {Γ = Bounded} {NoNoisy} both) ≡ ((2 , 0) , refl , refl , tt)
both-is-no-noise = refl

-- Coarsening: report only whether the observation is positive.
positive : Nat → Bool
positive zero = false
positive (suc _) = true

coarse-bounded : Case (λ world → positive (observe world)) true NoiseBound
coarse-bounded = coarsen-case positive bounded

-- The coarse case admits a silent world the fine case excludes.
silent-one : Candidate (λ world → positive (observe world)) true NoiseBound
silent-one = (0 , 1) , refl , s≤s z≤n

coarsening-forgets-presence : ¬ Holds coarse-bounded Present
coarsening-forgets-presence claim = claim silent-one refl

-- What does survive coarsening transfers back to the fine case.
coarse-observation-is-positive : Holds coarse-bounded (λ world → 1 ≤ observe world)
coarse-observation-is-positive (world , observed , _) with observe world | observed
... | zero  | ()
... | suc _ | _ = s≤s z≤n

fine-observation-is-positive : Holds bounded (λ world → 1 ≤ observe world)
fine-observation-is-positive = coarsen-claim positive bounded coarse-observation-is-positive
