{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

-- Dependency-preserving composition of evidence, and coarsening of observations.
--
-- Two contexts compose by concatenation.  Evidence for Γ ++ Δ is exactly a
-- pair of evidence for Γ and for Δ (split / join, inverse on both sides), and
-- splitting is nothing but weakening along the two canonical thinnings
-- Γ ⊆ Γ ++ Δ and Δ ⊆ Γ ++ Δ (split-is-weaken-left / -right).  Claims compose
-- accordingly: a claim under Γ and a claim under Δ give a conjoined claim
-- under Γ ++ Δ — but only for a composed case supplied explicitly, since two
-- consistent contexts need not be jointly consistent (Conflict in
-- Examples.Presence is the standing example).  The composed case does thin
-- back to each component (component-left / component-right).
--
-- Two observations taken together are one observation into a pair; a
-- candidate for the paired observation is the same thing as a world with both
-- observations (to-pair / from-pair, inverse on both sides).
--
-- Coarsening an observation along f : O → O′ (reporting f ∘ observe instead of
-- observe) keeps every candidate and may admit more.  So a claim that holds
-- at the coarse observation holds at the fine one (coarsen-claim); the
-- converse is false, and tests/reject/FalseCoarsening shows the prover
-- refusing it while Examples.Composition exhibits the counter-world.

module ResidualEvidence.Composition where

open import ResidualEvidence.Prelude
open import ResidualEvidence.Core
open import ResidualEvidence.Context

infixr 5 _++_
_++_ : ∀ {a} {A : Set a} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

-- Evidence for a concatenation is a pair of evidence.
split : ∀ {w} {W : Set w} (Γ Δ : Ctx W) (world : W) →
  ⟦ Γ ++ Δ ⟧ world → ⟦ Γ ⟧ world × ⟦ Δ ⟧ world
split [] Δ world evidence = tt , evidence
split (P ∷ Γ) Δ world (p , rest) =
  (p , fst (split Γ Δ world rest)) , snd (split Γ Δ world rest)

join : ∀ {w} {W : Set w} (Γ Δ : Ctx W) (world : W) →
  ⟦ Γ ⟧ world × ⟦ Δ ⟧ world → ⟦ Γ ++ Δ ⟧ world
join [] Δ world (_ , evidence) = evidence
join (P ∷ Γ) Δ world ((p , left) , right) = p , join Γ Δ world (left , right)

join-split : ∀ {w} {W : Set w} (Γ Δ : Ctx W) (world : W)
  (evidence : ⟦ Γ ++ Δ ⟧ world) → join Γ Δ world (split Γ Δ world evidence) ≡ evidence
join-split [] Δ world evidence = refl
join-split (P ∷ Γ) Δ world (p , rest) = cong (λ z → p , z) (join-split Γ Δ world rest)

split-join : ∀ {w} {W : Set w} (Γ Δ : Ctx W) (world : W)
  (evidence : ⟦ Γ ⟧ world × ⟦ Δ ⟧ world) → split Γ Δ world (join Γ Δ world evidence) ≡ evidence
split-join [] Δ world (_ , evidence) = refl
split-join (P ∷ Γ) Δ world ((p , left) , right) =
  cong (λ z → (p , fst z) , snd z) (split-join Γ Δ world (left , right))

-- The two canonical thinnings into a concatenation.
⊆-empty : ∀ {w} {W : Set w} {Δ : Ctx W} → [] ⊆ Δ
⊆-empty {Δ = []} = done
⊆-empty {Δ = P ∷ Δ} = drop ⊆-empty

⊆-++ˡ : ∀ {w} {W : Set w} {Γ Δ : Ctx W} → Γ ⊆ Γ ++ Δ
⊆-++ˡ {Γ = []} = ⊆-empty
⊆-++ˡ {Γ = P ∷ Γ} = keep ⊆-++ˡ

⊆-++ʳ : ∀ {w} {W : Set w} {Γ Δ : Ctx W} → Δ ⊆ Γ ++ Δ
⊆-++ʳ {Γ = []} = ⊆-refl
⊆-++ʳ {Γ = P ∷ Γ} = drop ⊆-++ʳ

weaken-refl : ∀ {w} {W : Set w} (Γ : Ctx W) (world : W) (evidence : ⟦ Γ ⟧ world) →
  weaken ⊆-refl world evidence ≡ evidence
weaken-refl [] world evidence = refl
weaken-refl (P ∷ Γ) world (p , rest) = cong (λ z → p , z) (weaken-refl Γ world rest)

-- Splitting is weakening along those thinnings: nothing new is introduced.
split-is-weaken-left : ∀ {w} {W : Set w} (Γ Δ : Ctx W) (world : W)
  (evidence : ⟦ Γ ++ Δ ⟧ world) →
  weaken (⊆-++ˡ {Γ = Γ} {Δ}) world evidence ≡ fst (split Γ Δ world evidence)
split-is-weaken-left [] Δ world evidence = refl
split-is-weaken-left (P ∷ Γ) Δ world (p , rest) =
  cong (λ z → p , z) (split-is-weaken-left Γ Δ world rest)

split-is-weaken-right : ∀ {w} {W : Set w} (Γ Δ : Ctx W) (world : W)
  (evidence : ⟦ Γ ++ Δ ⟧ world) →
  weaken (⊆-++ʳ {Γ = Γ} {Δ}) world evidence ≡ snd (split Γ Δ world evidence)
split-is-weaken-right [] Δ world evidence = weaken-refl Δ world evidence
split-is-weaken-right (P ∷ Γ) Δ world (p , rest) = split-is-weaken-right Γ Δ world rest

-- A composed case is a case for each component; the world and observation
-- are kept.  The converse needs joint consistency and is never derived.
component-left : ∀ {w o} {W : Set w} {O : Set o} {observe : W → O} {r : O}
  {Γ Δ : Ctx W} → Case observe r ⟦ Γ ++ Δ ⟧ → Case observe r ⟦ Γ ⟧
component-left {Γ = Γ} {Δ} = case-weaken (⊆-++ˡ {Γ = Γ} {Δ})

component-right : ∀ {w o} {W : Set w} {O : Set o} {observe : W → O} {r : O}
  {Γ Δ : Ctx W} → Case observe r ⟦ Γ ++ Δ ⟧ → Case observe r ⟦ Δ ⟧
component-right {Γ = Γ} {Δ} = case-weaken (⊆-++ʳ {Γ = Γ} {Δ})

-- Claims compose over a composed case that is supplied, not manufactured:
-- every candidate of Γ ++ Δ is a candidate of Γ and a candidate of Δ.
compose-claims : ∀ {w o p q} {W : Set w} {O : Set o} {observe : W → O} {r : O}
  {Γ Δ : Ctx W} {P : W → Set p} {Q : W → Set q}
  (left : Case observe r ⟦ Γ ⟧) (right : Case observe r ⟦ Δ ⟧)
  (both : Case observe r ⟦ Γ ++ Δ ⟧) →
  Holds left P → Holds right Q → Holds both (λ world → P world × Q world)
compose-claims {Γ = Γ} {Δ} left right both claimP claimQ (world , observed , evidence) =
  claimP (world , observed , fst (split Γ Δ world evidence)) ,
  claimQ (world , observed , snd (split Γ Δ world evidence))

-- Two observations at once are one observation into a pair.
pair-observation : ∀ {w o₁ o₂} {W : Set w} {O₁ : Set o₁} {O₂ : Set o₂} →
  (W → O₁) → (W → O₂) → W → O₁ × O₂
pair-observation observe₁ observe₂ world = observe₁ world , observe₂ world

PairCandidate : ∀ {w o₁ o₂ e} {W : Set w} {O₁ : Set o₁} {O₂ : Set o₂} →
  (W → O₁) → (W → O₂) → O₁ → O₂ → (W → Set e) → Set (w ⊔ o₁ ⊔ o₂ ⊔ e)
PairCandidate {W = W} observe₁ observe₂ r₁ r₂ E =
  Σ W (λ world → (observe₁ world ≡ r₁) × (observe₂ world ≡ r₂) × E world)

to-pair : ∀ {w o₁ o₂ e} {W : Set w} {O₁ : Set o₁} {O₂ : Set o₂}
  {observe₁ : W → O₁} {observe₂ : W → O₂} {r₁ : O₁} {r₂ : O₂} {E : W → Set e} →
  PairCandidate observe₁ observe₂ r₁ r₂ E →
  Candidate (pair-observation observe₁ observe₂) (r₁ , r₂) E
to-pair (world , refl , refl , evidence) = world , refl , evidence

from-pair : ∀ {w o₁ o₂ e} {W : Set w} {O₁ : Set o₁} {O₂ : Set o₂}
  {observe₁ : W → O₁} {observe₂ : W → O₂} {r₁ : O₁} {r₂ : O₂} {E : W → Set e} →
  Candidate (pair-observation observe₁ observe₂) (r₁ , r₂) E →
  PairCandidate observe₁ observe₂ r₁ r₂ E
from-pair (world , observed , evidence) =
  world , cong fst observed , cong snd observed , evidence

pair-from-to : ∀ {w o₁ o₂ e} {W : Set w} {O₁ : Set o₁} {O₂ : Set o₂}
  {observe₁ : W → O₁} {observe₂ : W → O₂} {r₁ : O₁} {r₂ : O₂} {E : W → Set e}
  (x : PairCandidate observe₁ observe₂ r₁ r₂ E) → from-pair (to-pair x) ≡ x
pair-from-to (world , refl , refl , evidence) = refl

pair-to-from : ∀ {w o₁ o₂ e} {W : Set w} {O₁ : Set o₁} {O₂ : Set o₂}
  {observe₁ : W → O₁} {observe₂ : W → O₂} {r₁ : O₁} {r₂ : O₂} {E : W → Set e}
  (x : Candidate (pair-observation observe₁ observe₂) (r₁ , r₂) E) →
  to-pair (from-pair x) ≡ x
pair-to-from (world , refl , evidence) = refl

-- Coarsening an observation along f keeps every candidate.
coarsen-candidate : ∀ {w o o′ e} {W : Set w} {O : Set o} {O′ : Set o′}
  {observe : W → O} {r : O} {E : W → Set e} (f : O → O′) →
  Candidate observe r E → Candidate (λ world → f (observe world)) (f r) E
coarsen-candidate f (world , observed , evidence) = world , cong f observed , evidence

coarsen-case : ∀ {w o o′ e} {W : Set w} {O : Set o} {O′ : Set o′}
  {observe : W → O} {r : O} {E : W → Set e} (f : O → O′) →
  Case observe r E → Case (λ world → f (observe world)) (f r) E
coarsen-case f (inhabited witness) = inhabited (coarsen-candidate f witness)

-- A claim at the coarse observation holds at the fine one.  Not the converse:
-- the coarse case may admit worlds the fine case excludes.
coarsen-claim : ∀ {w o o′ e p} {W : Set w} {O : Set o} {O′ : Set o′}
  {observe : W → O} {r : O} {E : W → Set e} {P : W → Set p}
  (f : O → O′) (c : Case observe r E) →
  Holds (coarsen-case f c) P → Holds c P
coarsen-claim f c claim x = claim (coarsen-candidate f x)
