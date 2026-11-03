{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

module EchoComparison where

open import ResidualEvidence.Prelude
open import ResidualEvidence.Core
open import ResidualEvidence.Context
open import ResidualEvidence.Composition
open import ResidualEvidence.Examples.Presence
open import ResidualEvidence.Examples.Composition
  using (Bounded; NoNoisy; bounded-ctx; no-noise-ctx; both;
         bounded-presence-ctx; no-noise-two-ctx; positive;
         coarse-observation-is-positive; silent-one)
import Echo

-- The actual Echo library, not a copy of its definition.
EvidenceOverEcho : ∀ {w o e} {W : Set w} {O : Set o} →
  (W → O) → O → (W → Set e) → Set (w ⊔ o ⊔ e)
EvidenceOverEcho observe r E = Σ (Echo.Echo observe r) (λ x → E (fst x))

to-echo : ∀ {w o e} {W : Set w} {O : Set o}
  {observe : W → O} {r} {E : W → Set e} →
  Candidate observe r E → EvidenceOverEcho observe r E
to-echo = to-fibre

from-echo : ∀ {w o e} {W : Set w} {O : Set o}
  {observe : W → O} {r} {E : W → Set e} →
  EvidenceOverEcho observe r E → Candidate observe r E
from-echo = from-fibre

from-to-echo : ∀ {w o e} {W : Set w} {O : Set o}
  {observe : W → O} {r} {E : W → Set e} (x : Candidate observe r E) →
  from-echo (to-echo x) ≡ x
from-to-echo = from-to

to-from-echo : ∀ {w o e} {W : Set w} {O : Set o}
  {observe : W → O} {r} {E : W → Set e} (x : EvidenceOverEcho observe r E) →
  to-echo (from-echo x) ≡ x
to-from-echo = to-from

-- Cases retain a consistency witness, while claims quantify over every
-- evidence-refined Echo fibre element, not just the chosen witness.
record EchoCase {w o e} {W : Set w} {O : Set o}
  (observe : W → O) (r : O) (E : W → Set e) : Set (w ⊔ o ⊔ e) where
  constructor echo-inhabited
  field
    witness : EvidenceOverEcho observe r E

EchoHolds : ∀ {w o e p} {W : Set w} {O : Set o}
  {observe : W → O} {r} {E : W → Set e} →
  EchoCase observe r E → (W → Set p) → Set (w ⊔ o ⊔ e ⊔ p)
EchoHolds {observe = observe} {r} {E} c P =
  (x : EvidenceOverEcho observe r E) → P (fst (fst x))

to-echo-case : ∀ {w o e} {W : Set w} {O : Set o}
  {observe : W → O} {r} {E : W → Set e} →
  Case observe r E → EchoCase observe r E
to-echo-case (inhabited x) = echo-inhabited (to-echo x)

from-echo-case : ∀ {w o e} {W : Set w} {O : Set o}
  {observe : W → O} {r} {E : W → Set e} →
  EchoCase observe r E → Case observe r E
from-echo-case (echo-inhabited x) = inhabited (from-echo x)

-- Transport ResidualEvidence.Composition.compose-claims over the actual
-- Echo interface (hyperpolymath/nextgen-typing#115, AC2). This is composition
-- of evidence contexts; it does not identify it with Echo's function-
-- composition isomorphism. Joint consistency remains an explicit premise.
compose-echo-claims : ∀ {w o p q} {W : Set w} {O : Set o}
  {observe : W → O} {r : O} {Γ Δ : Ctx W} {P : W → Set p} {Q : W → Set q}
  (left : EchoCase observe r ⟦ Γ ⟧) (right : EchoCase observe r ⟦ Δ ⟧)
  (both-echo : EchoCase observe r ⟦ Γ ++ Δ ⟧) →
  EchoHolds left P → EchoHolds right Q →
  EchoHolds both-echo (λ world → P world × Q world)
compose-echo-claims {Γ = Γ} {Δ} left right both-echo claimP claimQ ((world , observed) , evidence) =
  compose-claims {Γ = Γ} {Δ = Δ}
    (from-echo-case left) (from-echo-case right) (from-echo-case both-echo)
    (λ x → claimP (to-echo x)) (λ x → claimQ (to-echo x))
    (world , observed , evidence)

-- A coarse observation keeps every fine candidate and can admit more.
-- Consequently only a coarse claim is transported back to a fine claim.
coarsen-echo-case : ∀ {w o o′ e} {W : Set w} {O : Set o} {O′ : Set o′}
  {observe : W → O} {r : O} {E : W → Set e} (f : O → O′) →
  EchoCase observe r E → EchoCase (λ world → f (observe world)) (f r) E
coarsen-echo-case f c = to-echo-case (coarsen-case f (from-echo-case c))

coarsen-echo-claim : ∀ {w o o′ e p} {W : Set w} {O : Set o} {O′ : Set o′}
  {observe : W → O} {r : O} {E : W → Set e} {P : W → Set p}
  (f : O → O′) (c : EchoCase observe r E) →
  EchoHolds (coarsen-echo-case f c) P → EchoHolds c P
coarsen-echo-claim f c claim x =
  coarsen-claim f (from-echo-case c) (λ y → claim (to-echo y)) (from-echo x)

-- Concrete composition: [NoiseBound] ++ [NoNoise] proves both claims.
echo-bounded : EchoCase observe 2 ⟦ Bounded ⟧
echo-bounded = to-echo-case bounded-ctx

echo-no-noise : EchoCase observe 2 ⟦ NoNoisy ⟧
echo-no-noise = to-echo-case no-noise-ctx

echo-both : EchoCase observe 2 ⟦ Bounded ++ NoNoisy ⟧
echo-both = to-echo-case both

echo-present-and-two : EchoHolds echo-both (λ world → Present world × (contribution world ≡ 2))
echo-present-and-two =
  compose-echo-claims {Γ = Bounded} {Δ = NoNoisy}
    echo-bounded echo-no-noise echo-both
    (λ x → bounded-presence-ctx (from-echo x))
    (λ x → no-noise-two-ctx (from-echo x))

echo-fine-positive : EchoHolds (to-echo-case bounded) (λ world → 1 ≤ observe world)
echo-fine-positive =
  coarsen-echo-claim positive (to-echo-case bounded)
    (λ x → coarse-observation-is-positive (from-echo x))

-- The converse fails constructively at a newly admitted silent world.
echo-coarsening-forgets-presence :
  ¬ EchoHolds (coarsen-echo-case positive (to-echo-case bounded)) Present
echo-coarsening-forgets-presence claim = claim (to-echo silent-one) refl
