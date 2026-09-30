{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

-- Constructive refutation, retraction of assumptions, and revision.
--
-- A claim is refuted by exhibiting a candidate at whose world it fails
-- (Refuted); an identification is refuted by exhibiting two candidates that
-- disagree on the query (Disagreeing).  Both are positive data: a witness
-- world, never the bare negation of an abstract statement.  ¬ Holds and
-- ¬ Identified are consequences (refuted-not-holds, disagreeing-not-identified),
-- not definitions.
--
-- Retracting one assumption from a context Γ leaves Δ with Δ ⊆ Γ: a retraction
-- is a thinning read downwards, and the case travels down it for free
-- (retract-case), keeping its world and observation.  Evidence for Γ is
-- exactly the retracted assumption paired with evidence for Δ
-- (retract-split / retract-join, inverse on both sides), and the second
-- component is nothing but weakening (retract-is-weaken).
--
-- The two kinds of statement travel in opposite directions along thinnings:
--   claims go UP     (claim-strengthen, Context): more assumptions, same claim;
--   refutations and disagreements go DOWN (refuted-thin, disagreeing-thin):
--                    fewer assumptions, same counter-world.
-- So a refutation always survives a retraction (refuted-retract), while a
-- claim survives only when it does not rest on the retracted assumption.
-- A Dependent claim names the support it rests on; survives-retraction asks
-- that the support thins into the retracted context and proves the claim
-- there.  tests/reject/FalseRetraction shows the prover refusing the claim
-- when the retracted assumption is the very one the claim rests on.
--
-- A revision retracts one assumption and then assumes what the new context
-- adds (Revision, replace-head).  The revised case is always an explicit
-- argument to revise: the new assumption need not be consistent with the
-- rest, and nothing here manufactures inhabitation.

module ResidualEvidence.Revision where

open import ResidualEvidence.Prelude
open import ResidualEvidence.Core
open import ResidualEvidence.Context
open import Agda.Primitive using (lzero; lsuc)

-- A claim refuted at a witness world of the case.
Refuted : ∀ {w o e p} {W : Set w} {O : Set o}
  {observe : W → O} {r} {E : W → Set e} →
  Case observe r E → (W → Set p) → Set (w ⊔ o ⊔ e ⊔ p)
Refuted {observe = observe} {r} {E} c P = Σ (Candidate observe r E) (λ x → ¬ P (fst x))

-- Two witness worlds of the case that disagree on a query.
Disagreeing : ∀ {w o e q} {W : Set w} {O : Set o} {Q : Set q}
  {observe : W → O} {r} {E : W → Set e} →
  Case observe r E → (W → Q) → Set (w ⊔ o ⊔ e ⊔ q)
Disagreeing {observe = observe} {r} {E} c query =
  Σ (Candidate observe r E) (λ x → Σ (Candidate observe r E) (λ y →
    ¬ (query (fst x) ≡ query (fst y))))

-- The negative statements follow from the witnesses; they are not the definitions.
refuted-not-holds : ∀ {w o e p} {W : Set w} {O : Set o}
  {observe : W → O} {r} {E : W → Set e} {P : W → Set p}
  (c : Case observe r E) → Refuted c P → ¬ Holds c P
refuted-not-holds c (x , fails) claim = fails (claim x)

disagreeing-not-identified : ∀ {w o e q} {W : Set w} {O : Set o} {Q : Set q}
  {observe : W → O} {r} {E : W → Set e}
  (c : Case observe r E) (query : W → Q) → Disagreeing c query → ¬ Identified c query
disagreeing-not-identified c query (x , y , disagree) =
  different-candidates-refute-identification c query x y disagree

-- Refutations and disagreements travel down a thinning: the counter-world
-- keeps its observation and loses only the assumptions that were dropped.
refuted-thin : ∀ {w o p} {W : Set w} {O : Set o} {observe : W → O} {r : O}
  {Γ Δ : Ctx W} {P : W → Set p} (thin : Γ ⊆ Δ) (c : Case observe r ⟦ Δ ⟧) →
  Refuted c P → Refuted (case-weaken thin c) P
refuted-thin thin c ((world , observed , evidence) , fails) =
  (world , observed , weaken thin world evidence) , fails

disagreeing-thin : ∀ {w o q} {W : Set w} {O : Set o} {Q : Set q}
  {observe : W → O} {r : O} {Γ Δ : Ctx W} {query : W → Q}
  (thin : Γ ⊆ Δ) (c : Case observe r ⟦ Δ ⟧) →
  Disagreeing c query → Disagreeing (case-weaken thin c) query
disagreeing-thin thin c ((x , xo , xe) , (y , yo , ye) , disagree) =
  (x , xo , weaken thin x xe) , (y , yo , weaken thin y ye) , disagree

-- Δ is Γ with exactly one assumption retracted, named by its position.
data Retraction {w} {W : Set w} : Ctx W → Ctx W → Set (lsuc lzero ⊔ w) where
  first : ∀ {P : W → Set} {Γ} → Retraction (P ∷ Γ) Γ
  later : ∀ {P : W → Set} {Γ Δ} → Retraction Γ Δ → Retraction (P ∷ Γ) (P ∷ Δ)

-- The assumption a retraction removes.
retracted : ∀ {w} {W : Set w} {Γ Δ : Ctx W} → Retraction Γ Δ → W → Set
retracted (first {P = P}) = P
retracted (later ret) = retracted ret

-- A retraction is a thinning of the smaller context into the larger one.
retract-⊆ : ∀ {w} {W : Set w} {Γ Δ : Ctx W} → Retraction Γ Δ → Δ ⊆ Γ
retract-⊆ first = drop ⊆-refl
retract-⊆ (later ret) = keep (retract-⊆ ret)

-- Evidence for Γ is the retracted assumption paired with evidence for Δ.
retract-split : ∀ {w} {W : Set w} {Γ Δ : Ctx W} (ret : Retraction Γ Δ) (world : W) →
  ⟦ Γ ⟧ world → retracted ret world × ⟦ Δ ⟧ world
retract-split first world (p , rest) = p , rest
retract-split (later ret) world (q , rest) =
  fst (retract-split ret world rest) , q , snd (retract-split ret world rest)

retract-join : ∀ {w} {W : Set w} {Γ Δ : Ctx W} (ret : Retraction Γ Δ) (world : W) →
  retracted ret world × ⟦ Δ ⟧ world → ⟦ Γ ⟧ world
retract-join first world (p , rest) = p , rest
retract-join (later ret) world (p , q , rest) = q , retract-join ret world (p , rest)

retract-join-split : ∀ {w} {W : Set w} {Γ Δ : Ctx W} (ret : Retraction Γ Δ) (world : W)
  (evidence : ⟦ Γ ⟧ world) →
  retract-join ret world (retract-split ret world evidence) ≡ evidence
retract-join-split first world (p , rest) = refl
retract-join-split (later ret) world (q , rest) =
  cong (λ z → q , z) (retract-join-split ret world rest)

retract-split-join : ∀ {w} {W : Set w} {Γ Δ : Ctx W} (ret : Retraction Γ Δ) (world : W)
  (evidence : retracted ret world × ⟦ Δ ⟧ world) →
  retract-split ret world (retract-join ret world evidence) ≡ evidence
retract-split-join first world (p , rest) = refl
retract-split-join (later ret) world (p , q , rest) =
  cong (λ z → fst z , q , snd z) (retract-split-join ret world (p , rest))

-- Retracting evidence is weakening along the retraction's thinning.
retract-evidence : ∀ {w} {W : Set w} {Γ Δ : Ctx W} (ret : Retraction Γ Δ) (world : W) →
  ⟦ Γ ⟧ world → ⟦ Δ ⟧ world
retract-evidence ret = weaken (retract-⊆ ret)

retract-is-weaken : ∀ {w} {W : Set w} {Γ Δ : Ctx W} (ret : Retraction Γ Δ) (world : W)
  (evidence : ⟦ Γ ⟧ world) →
  retract-evidence ret world evidence ≡ snd (retract-split ret world evidence)
retract-is-weaken first world (p , rest) = weaken-refl′ _ world rest
  where
  weaken-refl′ : ∀ {w} {W : Set w} (Γ : Ctx W) (world : W) (evidence : ⟦ Γ ⟧ world) →
    weaken ⊆-refl world evidence ≡ evidence
  weaken-refl′ [] world evidence = refl
  weaken-refl′ (P ∷ Γ) world (p , rest) = cong (λ z → p , z) (weaken-refl′ Γ world rest)
retract-is-weaken (later ret) world (q , rest) =
  cong (λ z → q , z) (retract-is-weaken ret world rest)

-- A case under Γ is a case under Δ: the world and observation are kept.
retract-case : ∀ {w o} {W : Set w} {O : Set o} {observe : W → O} {r : O}
  {Γ Δ : Ctx W} → Retraction Γ Δ → Case observe r ⟦ Γ ⟧ → Case observe r ⟦ Δ ⟧
retract-case ret = case-weaken (retract-⊆ ret)

-- Refutations and disagreements survive any retraction, unconditionally.
refuted-retract : ∀ {w o p} {W : Set w} {O : Set o} {observe : W → O} {r : O}
  {Γ Δ : Ctx W} {P : W → Set p} (ret : Retraction Γ Δ) (c : Case observe r ⟦ Γ ⟧) →
  Refuted c P → Refuted (retract-case ret c) P
refuted-retract ret = refuted-thin (retract-⊆ ret)

disagreeing-retract : ∀ {w o q} {W : Set w} {O : Set o} {Q : Set q}
  {observe : W → O} {r : O} {Γ Δ : Ctx W} {query : W → Q}
  (ret : Retraction Γ Δ) (c : Case observe r ⟦ Γ ⟧) →
  Disagreeing c query → Disagreeing (retract-case ret c) query
disagreeing-retract ret = disagreeing-thin (retract-⊆ ret)

-- A claim under Γ that names the assumptions it rests on: it is established
-- for every candidate satisfying just the support, which thins into Γ.
record Dependent {w o p} {W : Set w} {O : Set o} {observe : W → O} {r : O}
  {Γ : Ctx W} (c : Case observe r ⟦ Γ ⟧) (P : W → Set p) :
  Set (lsuc lzero ⊔ w ⊔ o ⊔ p) where
  constructor rests-on
  field
    support : Ctx W
    thin    : support ⊆ Γ
    claim   : Holds (case-weaken thin c) P

open Dependent public using (support)

-- Naming the support costs nothing: the claim holds under all of Γ.
dependent-holds : ∀ {w o p} {W : Set w} {O : Set o} {observe : W → O} {r : O}
  {Γ : Ctx W} {P : W → Set p} (c : Case observe r ⟦ Γ ⟧) → Dependent c P → Holds c P
dependent-holds c (rests-on support thin claim) =
  claim-strengthen thin (case-weaken thin c) c claim

-- A claim survives a retraction when its support thins into what remains.
-- The premise is against the retracted context Δ, never against Γ.
survives-retraction : ∀ {w o p} {W : Set w} {O : Set o} {observe : W → O} {r : O}
  {Γ Δ : Ctx W} {P : W → Set p} (ret : Retraction Γ Δ) (c : Case observe r ⟦ Γ ⟧)
  (dep : Dependent c P) → support dep ⊆ Δ → Holds (retract-case ret c) P
survives-retraction ret c (rests-on support thin claim) avoid =
  claim-strengthen avoid (case-weaken thin c) (retract-case ret c) claim

-- The surviving claim still rests on the same support.
survives-dependent : ∀ {w o p} {W : Set w} {O : Set o} {observe : W → O} {r : O}
  {Γ Δ : Ctx W} {P : W → Set p} (ret : Retraction Γ Δ) (c : Case observe r ⟦ Γ ⟧)
  (dep : Dependent c P) → support dep ⊆ Δ → Dependent (retract-case ret c) P
survives-dependent ret c (rests-on support thin claim) avoid = rests-on support avoid claim

-- A revision retracts one assumption and then assumes what the new context adds.
record Revision {w} {W : Set w} (Γ Γ′ : Ctx W) : Set (lsuc lzero ⊔ w) where
  constructor retract-then-extend
  field
    middle  : Ctx W
    retract : Retraction Γ middle
    extend  : middle ⊆ Γ′

open Revision public using (middle)

-- Replacing the first assumption by another.
replace-head : ∀ {w} {W : Set w} {A B : W → Set} {Γ : Ctx W} → Revision (A ∷ Γ) (B ∷ Γ)
replace-head {Γ = Γ} = retract-then-extend Γ first (drop ⊆-refl)

-- A claim resting on assumptions the revision keeps transfers to the revised
-- case, which is supplied: the new assumption need not be consistent with
-- the kept ones, and nothing here derives c′ from c.
revise : ∀ {w o p} {W : Set w} {O : Set o} {observe : W → O} {r : O}
  {Γ Γ′ : Ctx W} {P : W → Set p} (rev : Revision Γ Γ′)
  (c : Case observe r ⟦ Γ ⟧) (c′ : Case observe r ⟦ Γ′ ⟧)
  (dep : Dependent c P) → support dep ⊆ middle rev → Holds c′ P
revise (retract-then-extend middle ret extend) c c′ dep avoid =
  claim-strengthen extend (retract-case ret c) c′ (survives-retraction ret c dep avoid)
