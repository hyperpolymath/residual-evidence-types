{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

-- The Presence example under retraction and revision.  Presence rests on the
-- noise bound alone, so it survives retracting NoNoise; the identification
-- contribution ≡ 2 does not survive, and its loss is exhibited by the two
-- candidates (1 , 1) and (2 , 0) that remain under the bound alone.
-- Retracting the bound instead refutes presence at the world (0 , 2).
-- Replacing NoNoise by "contribution equals noise" keeps presence and
-- identifies contribution ≡ 1 at the supplied revised case (1 , 1);
-- replacing it by "contribution ≡ 0" admits no case at all, which is why
-- revise takes the revised case as an argument and never derives it.

module ResidualEvidence.Examples.Revision where

open import ResidualEvidence.Prelude
open import ResidualEvidence.Core
open import ResidualEvidence.Context
open import ResidualEvidence.Composition
open import ResidualEvidence.Revision
open import ResidualEvidence.Examples.Presence
open import ResidualEvidence.Examples.Composition

-- Presence under both assumptions rests on the noise bound alone.
presence-rests-on-bound : Dependent both Present
presence-rests-on-bound = rests-on Bounded (⊆-++ˡ {Γ = Bounded} {NoNoisy}) bounded-presence-ctx

-- The same claim under the bound alone, resting on all of it.
presence-rests-on-bounded : Dependent bounded-ctx Present
presence-rests-on-bounded = rests-on Bounded ⊆-refl bounded-presence-ctx

-- Retracting NoNoise from [NoiseBound] ++ [NoNoise] leaves [NoiseBound].
drop-no-noise : Retraction (Bounded ++ NoNoisy) Bounded
drop-no-noise = later first

-- Presence survives: its support is exactly what remains.
presence-survives : Holds (retract-case drop-no-noise both) Present
presence-survives = survives-retraction drop-no-noise both presence-rests-on-bound ⊆-refl

-- Under both assumptions the contribution is identified as 2 ...
both-identifies-two : Identified both contribution
both-identifies-two = 2 , λ x → snd (present-and-two x)

-- ... and after retracting NoNoise it is not: (1 , 1) and (2 , 0) both remain.
identification-lost : Disagreeing (retract-case drop-no-noise both) contribution
identification-lost =
  ((1 , 1) , refl , s≤s z≤n , tt) , ((2 , 0) , refl , z≤n , tt) , one-not-two

identification-not-recovered : ¬ Identified (retract-case drop-no-noise both) contribution
identification-not-recovered =
  disagreeing-not-identified (retract-case drop-no-noise both) contribution identification-lost

-- Retracting the bound instead: presence is refuted at the world (0 , 2).
drop-bound : Retraction Bounded []
drop-bound = first

presence-refuted : Refuted (retract-case drop-bound bounded-ctx) Present
presence-refuted = ((0 , 2) , refl , tt) , λ absent → absent refl

presence-not-held : ¬ Holds (retract-case drop-bound bounded-ctx) Present
presence-not-held = refuted-not-holds (retract-case drop-bound bounded-ctx) presence-refuted

-- A disagreement needs no premise to survive a further retraction.
identification-still-lost :
  Disagreeing (retract-case drop-bound (retract-case drop-no-noise both)) contribution
identification-still-lost =
  disagreeing-retract drop-bound (retract-case drop-no-noise both) identification-lost

-- Revision: replace NoNoise by "the contribution equals the noise".
Balanced : World → Set
Balanced world = contribution world ≡ noise world

to-balanced : Revision (Bounded ++ NoNoisy) (NoiseBound ∷ Balanced ∷ [])
to-balanced = retract-then-extend Bounded drop-no-noise (keep (drop done))

-- The revised case is supplied: the world (1 , 1) satisfies the new context.
balanced-ctx : Case observe 2 ⟦ NoiseBound ∷ Balanced ∷ [] ⟧
balanced-ctx = inhabited ((1 , 1) , refl , s≤s z≤n , refl , tt)

-- Presence transfers to the revised case through the kept bound.
presence-after-revision : Holds balanced-ctx Present
presence-after-revision = revise to-balanced both balanced-ctx presence-rests-on-bound ⊆-refl

-- The new assumption identifies a different contribution: 1, not 2.
half : (u n : Nat) → u ≡ n → u + n ≡ 2 → u ≡ 1
half zero .zero refl ()
half (suc zero) .(suc zero) refl _ = refl
half (suc (suc zero)) .(suc (suc zero)) refl ()
half (suc (suc (suc u))) .(suc (suc (suc u))) refl ()

balanced-one : Holds balanced-ctx (λ world → contribution world ≡ 1)
balanced-one (world , observed , _ , balanced , _) =
  half (contribution world) (noise world) balanced observed

balanced-identifies-one : Identified balanced-ctx contribution
balanced-identifies-one = 1 , balanced-one

-- Replacing NoNoise by "no contribution" instead is Conflict under a new
-- name: no case exists, so nothing could have derived the revised case.
Absent : World → Set
Absent world = contribution world ≡ 0

to-absent : Revision (Bounded ++ NoNoisy) (NoiseBound ∷ Absent ∷ [])
to-absent = retract-then-extend Bounded drop-no-noise (keep (drop done))

no-revised-case : ¬ Case observe 2 ⟦ NoiseBound ∷ Absent ∷ [] ⟧
no-revised-case (inhabited (world , observed , bound , absent , _)) =
  conflict-has-no-case (inhabited (world , observed , bound , absent))
