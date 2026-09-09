{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

module ResidualEvidence.Core where

open import ResidualEvidence.Prelude

-- Ordinary evidence-refined preimage fibre, not a new primitive type.
Candidate : ∀ {w o e} {W : Set w} {O : Set o} →
  (W → O) → O → (W → Set e) → Set (w ⊔ o ⊔ e)
Candidate {W = W} observe r E = Σ W (λ world → (observe world ≡ r) × E world)

-- A case must carry a witness of consistency. Claims still quantify over
-- ALL candidates, not merely this chosen inhabitant.
record Case {w o e} {W : Set w} {O : Set o}
  (observe : W → O) (r : O) (E : W → Set e) : Set (w ⊔ o ⊔ e) where
  constructor inhabited
  field
    witness : Candidate observe r E

Holds : ∀ {w o e p} {W : Set w} {O : Set o}
  {observe : W → O} {r} {E : W → Set e} →
  Case observe r E → (W → Set p) → Set (w ⊔ o ⊔ e ⊔ p)
Holds {observe = observe} {r} {E} c P = (x : Candidate observe r E) → P (fst x)

Identified : ∀ {w o e q} {W : Set w} {O : Set o} {Q : Set q}
  {observe : W → O} {r} {E : W → Set e} →
  Case observe r E → (W → Q) → Set (w ⊔ o ⊔ e ⊔ q)
Identified {Q = Q} c query = Σ Q (λ value → Holds c (λ world → query world ≡ value))

-- Applying a conditional claim to an actual world needs BOTH premises.
actual-world-sound : ∀ {w o e p} {W : Set w} {O : Set o}
  {observe : W → O} {r} {E : W → Set e} {P : W → Set p}
  (c : Case observe r E) → Holds c P →
  (actual : W) → observe actual ≡ r → E actual → P actual
actual-world-sound c claim actual observed evidence = claim (actual , observed , evidence)

-- Two admissible worlds that disagree on a query refute identification.
different-candidates-refute-identification :
  ∀ {w o e q} {W : Set w} {O : Set o} {Q : Set q}
  {observe : W → O} {r} {E : W → Set e}
  (c : Case observe r E) (query : W → Q)
  (x y : Candidate observe r E) →
  ¬ (query (fst x) ≡ query (fst y)) → ¬ Identified c query
different-candidates-refute-identification c query x y disagree (value , agrees) =
  disagree (trans (agrees x) (sym (agrees y)))

-- Evidence strengthening alone does not promise a consistent new case.
refine-candidate : ∀ {w o e f} {W : Set w} {O : Set o}
  {observe : W → O} {r} {E : W → Set e} {F : W → Set f} →
  ((world : W) → F world → E world) → Candidate observe r F → Candidate observe r E
refine-candidate entails (world , observed , evidence) = world , observed , entails world evidence

refine-claim : ∀ {w o e f p} {W : Set w} {O : Set o}
  {observe : W → O} {r} {E : W → Set e} {F : W → Set f} {P : W → Set p} →
  (old : Case observe r E) → (new : Case observe r F) →
  ((world : W) → F world → E world) → Holds old P → Holds new P
refine-claim old new entails claim x = claim (refine-candidate entails x)

-- Expose the ordinary fibre packaging with pointwise inverse laws.
Fibre : ∀ {w o} {W : Set w} {O : Set o} → (W → O) → O → Set (w ⊔ o)
Fibre {W = W} observe r = Σ W (λ world → observe world ≡ r)

RefinedFibre : ∀ {w o e} {W : Set w} {O : Set o} →
  (W → O) → O → (W → Set e) → Set (w ⊔ o ⊔ e)
RefinedFibre observe r E = Σ (Fibre observe r) (λ x → E (fst x))

to-fibre : ∀ {w o e} {W : Set w} {O : Set o}
  {observe : W → O} {r} {E : W → Set e} → Candidate observe r E → RefinedFibre observe r E
to-fibre (world , observed , evidence) = (world , observed) , evidence

from-fibre : ∀ {w o e} {W : Set w} {O : Set o}
  {observe : W → O} {r} {E : W → Set e} → RefinedFibre observe r E → Candidate observe r E
from-fibre ((world , observed) , evidence) = world , observed , evidence

from-to : ∀ {w o e} {W : Set w} {O : Set o}
  {observe : W → O} {r} {E : W → Set e} (x : Candidate observe r E) →
  from-fibre (to-fibre x) ≡ x
from-to (world , observed , evidence) = refl

to-from : ∀ {w o e} {W : Set w} {O : Set o}
  {observe : W → O} {r} {E : W → Set e} (x : RefinedFibre observe r E) →
  to-fibre (from-fibre x) ≡ x
to-from ((world , observed) , evidence) = refl
