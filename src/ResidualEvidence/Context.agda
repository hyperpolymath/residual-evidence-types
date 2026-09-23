{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

-- Contexts of assumptions and the thinnings between them.
--
-- A context is a list of predicates on worlds; its meaning ⟦ Γ ⟧ is their
-- conjunction, which is exactly the evidence parameter E of a Core case.
-- A thinning Γ ⊆ Δ embeds Γ into Δ in order: Δ assumes everything Γ does
-- and possibly more.  Three consequences are proved, each by reduction
-- to Core:
--   weaken            stronger evidence yields weaker evidence (⟦ Δ ⟧ → ⟦ Γ ⟧);
--   case-weaken       a Δ-case is a Γ-case, keeping its world and observation;
--   claim-strengthen  a claim established under Γ still holds under Δ.
-- The converse directions are not available; tests/reject/FalseWeakening
-- shows the prover refusing the first of them.

module ResidualEvidence.Context where

open import ResidualEvidence.Prelude
open import ResidualEvidence.Core
open import Agda.Primitive using (lzero; lsuc)
open import Agda.Builtin.List using (List; []; _∷_) public

-- A context over worlds W: assumptions are level-zero predicates on W.
Ctx : ∀ {w} → Set w → Set (lsuc lzero ⊔ w)
Ctx W = List (W → Set)

-- The conjunction of a context, as evidence in the sense of Core.
⟦_⟧ : ∀ {w} {W : Set w} → Ctx W → W → Set
⟦ [] ⟧ world = ⊤
⟦ P ∷ Γ ⟧ world = P world × ⟦ Γ ⟧ world

-- Order-preserving embeddings between contexts.
infix 4 _⊆_
data _⊆_ {w} {W : Set w} : Ctx W → Ctx W → Set (lsuc lzero ⊔ w) where
  done : [] ⊆ []
  keep : ∀ {P : W → Set} {Γ Δ} → Γ ⊆ Δ → (P ∷ Γ) ⊆ (P ∷ Δ)
  drop : ∀ {P : W → Set} {Γ Δ} → Γ ⊆ Δ → Γ ⊆ (P ∷ Δ)

⊆-refl : ∀ {w} {W : Set w} {Γ : Ctx W} → Γ ⊆ Γ
⊆-refl {Γ = []} = done
⊆-refl {Γ = P ∷ Γ} = keep ⊆-refl

⊆-trans : ∀ {w} {W : Set w} {Γ Δ Θ : Ctx W} → Γ ⊆ Δ → Δ ⊆ Θ → Γ ⊆ Θ
⊆-trans thin done = thin
⊆-trans thin (drop thin′) = drop (⊆-trans thin thin′)
⊆-trans (keep thin) (keep thin′) = keep (⊆-trans thin thin′)
⊆-trans (drop thin) (keep thin′) = drop (⊆-trans thin thin′)

-- Evidence for the larger context restricts to evidence for the smaller one.
weaken : ∀ {w} {W : Set w} {Γ Δ : Ctx W} →
  Γ ⊆ Δ → (world : W) → ⟦ Δ ⟧ world → ⟦ Γ ⟧ world
weaken done world evidence = tt
weaken (keep thin) world (p , rest) = p , weaken thin world rest
weaken (drop thin) world (p , rest) = weaken thin world rest

-- A case under the stronger assumptions is a case under the weaker ones:
-- the witness keeps its world and its observation.
case-weaken : ∀ {w o} {W : Set w} {O : Set o} {observe : W → O} {r : O}
  {Γ Δ : Ctx W} → Γ ⊆ Δ → Case observe r ⟦ Δ ⟧ → Case observe r ⟦ Γ ⟧
case-weaken thin (inhabited witness) =
  inhabited (refine-candidate (weaken thin) witness)

-- A claim established under the weaker assumptions holds under the stronger
-- ones.  Both cases are explicit: strengthening never manufactures inhabitation.
claim-strengthen : ∀ {w o p} {W : Set w} {O : Set o} {observe : W → O} {r : O}
  {Γ Δ : Ctx W} {P : W → Set p} →
  Γ ⊆ Δ → (old : Case observe r ⟦ Γ ⟧) (new : Case observe r ⟦ Δ ⟧) →
  Holds old P → Holds new P
claim-strengthen thin old new = refine-claim old new (weaken thin)

-- A non-empty context never thins into the empty one.
no-thinning-into-empty : ∀ {w} {W : Set w} {P : W → Set} {Γ : Ctx W} →
  ¬ ((P ∷ Γ) ⊆ [])
no-thinning-into-empty ()
