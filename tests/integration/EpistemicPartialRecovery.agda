{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

module EpistemicPartialRecovery where

open import ResidualEvidence.Prelude
open import ResidualEvidence.Core
open import Agda.Builtin.Maybe using (just)
open import EpistemicTypes.EchoBridge using (Retention)
open import EpistemicTypes.PartialRecovery
  using (retainedPair; Image; Separates; PartialRecovery; ImageDecision;
         SuccessSound; partialSeparates; partialComplete; fromImageDecision;
         imageDecisionSound; soundPartialDecidesImage)

-- The observation is the JOINT visible/residue pair. Evidence may refine
-- its fibre further; a certificate alone need not separate sources.
PairCase : {A B R : Set} (C : Retention A B R) →
  B → R → (A → Set) → Set
PairCase C y r E = Case (retainedPair C) (y , r) E

-- With trivial evidence, a residual candidate is the sibling's actual,
-- proof-relevant image fibre. Neither direction computes an unknown source:
-- the source is already supplied in the input witness.
candidate-image : {A B R : Set} {C : Retention A B R} {y : B} {r : R} →
  Candidate (retainedPair C) (y , r) (λ _ → ⊤) → Image C y r
candidate-image (x , same , tt) = x , same

image-candidate : {A B R : Set} {C : Retention A B R} {y : B} {r : R} →
  Image C y r → Candidate (retainedPair C) (y , r) (λ _ → ⊤)
image-candidate (x , same) = x , same , tt

candidate-image-candidate : {A B R : Set} {C : Retention A B R} {y : B} {r : R}
  (x : Candidate (retainedPair C) (y , r) (λ _ → ⊤)) →
  image-candidate {C = C} (candidate-image {C = C} x) ≡ x
candidate-image-candidate (x , same , tt) = refl

image-candidate-image : {A B R : Set} {C : Retention A B R} {y : B} {r : R}
  (x : Image C y r) → candidate-image {C = C} (image-candidate {C = C} x) ≡ x
image-candidate-image (x , same) = refl

-- Inhabitation supplies an identified value, and separation proves that
-- ALL candidates agree with it. No equality of evidence proofs is needed.
separation-identifies : {A B R : Set} {C : Retention A B R}
  {y : B} {r : R} {E : A → Set} →
  Separates C → (c : PairCase C y r E) → Identified c (λ x → x)
separation-identifies separates c =
  fst (Case.witness c) , λ x → separates
    (trans (fst (snd x)) (sym (fst (snd (Case.witness c)))))

-- The converse needs identification for EVERY inhabited pair fibre with
-- trivial evidence. Identification of one evidence-refined case is weaker.
AllPairCasesIdentified : {A B R : Set} → Retention A B R → Set
AllPairCasesIdentified {B = B} {R = R} C =
  (y : B) (r : R) (c : PairCase C y r (λ _ → ⊤)) →
  Identified c (λ x → x)

all-cases-separate : {A B R : Set} {C : Retention A B R} →
  AllPairCasesIdentified C → Separates C
all-cases-separate {C = C} identify {x} {z} same =
  trans (snd identified (x , refl , tt))
    (sym (snd identified (z , sym same , tt)))
  where
  c = inhabited (x , refl , tt)
  identified = identify (Retention.observe C x) (Retention.retain C x) c

partial-recovery-identifies : {A B R : Set} {C : Retention A B R}
  {y : B} {r : R} {E : A → Set} →
  PartialRecovery C → (c : PairCase C y r E) → Identified c (λ x → x)
partial-recovery-identifies {C = C} rec =
  separation-identifies {C = C} (partialSeparates rec)

-- Sound success is necessary for THIS direction's image decision:
-- roundtrip alone constrains generated inputs, not successful off-image
-- outputs. These are constructive implications, not equality of decoders.
sound-partial-to-identified-decided : {A B R : Set} {C : Retention A B R}
  (rec : PartialRecovery C) → SuccessSound rec →
  AllPairCasesIdentified C × ImageDecision C
sound-partial-to-identified-decided {C = C} rec sound =
  (λ y r → partial-recovery-identifies {C = C} rec) ,
  soundPartialDecidesImage rec sound

-- This applies an ALREADY SUPPLIED decoder to a candidate's pair. The
-- source witness just proves completeness; it does not implement decode.
decode-candidate : {A B R : Set} {C : Retention A B R}
  (rec : PartialRecovery C) {y : B} {r : R} {E : A → Set}
  (x : Candidate (retainedPair C) (y , r) E) →
  PartialRecovery.decode rec y r ≡ just (fst x)
decode-candidate rec (x , same , evidence) = partialComplete rec (x , same)

-- A decoder requires the additional, constructive image-decision input.
-- No search procedure, choice principle or off-image success law follows
-- from case identification. The sibling supplies both construction/law.
identified-cases-to-partial : {A B R : Set} {C : Retention A B R} →
  AllPairCasesIdentified C → ImageDecision C → PartialRecovery C
identified-cases-to-partial {C = C} identify decide =
  fromImageDecision (all-cases-separate {C = C} identify) decide

identified-cases-success-sound : {A B R : Set} {C : Retention A B R}
  (identify : AllPairCasesIdentified C) (decide : ImageDecision C) →
  SuccessSound (identified-cases-to-partial {C = C} identify decide)
identified-cases-success-sound {C = C} identify decide =
  imageDecisionSound (all-cases-separate {C = C} identify) decide
