{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

-- Composition and revision transport beyond the Echo.Echo and
-- SoundWarrant interfaces.
--
-- Checked question: do the composition transport (Composition.agda) and the
-- revision transport (Revision.agda) extend beyond the interfaces this
-- repository compares against — Echo.Echo (echo-types @
-- 9c4b72b52972c7e084c8f569635eb01caef64e7a, proofs/agda/Echo.agda:
-- Echo f y = Σ A (λ x → f x ≡ y)) and SoundWarrant (epistemic-types @
-- dd948fbdddbdd06282cda8425e3e644e013c11ff, src/EpistemicTypes/Warrant.agda:
-- a Warrant with Evidence : Set, plus sound : Evidence → A)?
--
-- Checked answer: YES, both extend beyond the interfaces.
--
-- Composition. Echo.Echo observe r is the fibre of ONE observation and
-- carries no evidence predicate, no context of assumptions and no claims;
-- its laws (echo-intro, map-over-id / -comp, map-square, Echo-comp-iso,
-- cancel-iso, the pentagon iso) relate fibres of related FUNCTIONS over a
-- fixed codomain. The composition transport composes CLAIMS over TWO
-- concatenated evidence contexts: it rests on the concatenation
-- isomorphism ⟦Γ++Δ⟧ ≅ ⟦Γ⟧ × ⟦Δ⟧ (Composition.split / join, inverse on
-- both sides) and is stated for a composed case that is supplied
-- explicitly. No Echo.Echo law instantiates it: there is no context
-- parameter, no concatenation and no claims in Echo.Echo. The one
-- transport Echo.Echo does provide is candidate-level (echo-coarsen below,
-- its map-square law): it moves the fibre along coarsening, not claims
-- across concatenated assumptions.
--
-- Revision. SoundWarrant is a static record: a warrant with a FIXED
-- Evidence : Set and a FIXED sound : Evidence → A. Its only transport is
-- sound-epi (sound-extract below). The revision transport retracts one
-- assumption and assumes another, transferring claims whose support is
-- kept; it needs retraction data (first / later), the thinning
-- retract-⊆ : Δ ⊆ Γ, the split/join inverse laws for retracted evidence,
-- dependent claims (support ⊆ Γ) and the revision record
-- (retract-then-extend). None of this is present in SoundWarrant.
--
-- The two interface encodings below are faithful to the pinned revisions
-- and are ordinary types, so the comparison needs no cross-repository build
-- dependency. Each minimal transport is checked over the Echo.Echo fibre
-- encoding; the precise statements of what the interfaces lack are the
-- comments plus the checked laws the transports rest on.

module ResidualEvidence.Beyond where

open import ResidualEvidence.Prelude
open import ResidualEvidence.Core
open import ResidualEvidence.Context
open import ResidualEvidence.Composition
open import ResidualEvidence.Revision
open import ResidualEvidence.Examples.Presence
open import ResidualEvidence.Examples.Composition using
  (Bounded; NoNoisy; both; present-and-two)
open import ResidualEvidence.Examples.Revision using
  (drop-no-noise; presence-survives; balanced-ctx; presence-after-revision)
open import Agda.Primitive using (Level; lsuc; _⊔_)

-- ===========================================================================
-- The two interfaces, encoded faithfully from the pinned revisions.
-- ===========================================================================

-- Echo.Echo (echo-types @ 9c4b72b, proofs/agda/Echo.agda):
-- Echo f y = Σ A (λ x → f x ≡ y).  The fibre of one observation; it
-- carries no evidence predicate and no context of assumptions.
Echo : ∀ {w o} {W : Set w} {O : Set o} →
  (W → O) → O → Set (w ⊔ o)
Echo {W = W} observe r = Σ W (λ world → observe world ≡ r)

-- SoundWarrant (epistemic-types @ dd948fb, src/EpistemicTypes/Warrant.agda):
-- a Warrant over K at κ for A with a soundness field
-- sound : Warrant.Evidence warrant → A.  Static: the evidence type and the
-- soundness function are fixed at construction.  (Levels as in the pinned
-- source; the κ / A arguments carry their own levels.)
record Warrant {kℓ ℓ wℓ : Level} (K : Set kℓ) (κ : K) (A : Set ℓ) :
  Set (kℓ ⊔ ℓ ⊔ lsuc wℓ) where
  field
    Evidence : Set wℓ

record SoundWarrant {kℓ ℓ wℓ : Level} (K : Set kℓ) (κ : K) (A : Set ℓ) :
  Set (kℓ ⊔ ℓ ⊔ lsuc wℓ) where
  constructor soundWarrant
  field
    warrant : Warrant {kℓ = kℓ} {ℓ = ℓ} {wℓ = wℓ} K κ A
    sound   : Warrant.Evidence warrant → A

-- ===========================================================================
-- What the interfaces transport, and nothing more.
-- ===========================================================================

-- Echo.Echo's own transport, specialised to coarsening: the fibre moves
-- along the commuting square observe → f ∘ observe (Echo.map-square with
-- the identity on worlds).  This is the ONLY composition-like transport
-- Echo.Echo provides, and it moves candidates, not claims.
echo-coarsen : ∀ {w o o′} {W : Set w} {O : Set o} {O′ : Set o′}
  {observe : W → O} {r : O} (f : O → O′) →
  Echo observe r → Echo (λ world → f (observe world)) (f r)
echo-coarsen f (world , observed) = world , cong f observed

-- SoundWarrant's only transport: a token of the (fixed) evidence type
-- extracts the claim (sound-epi in the pinned source).
sound-extract : ∀ {kℓ ℓ wℓ : Level} {K : Set kℓ} {κ : K} {A : Set ℓ}
  (sw : SoundWarrant {wℓ = wℓ} K κ A) → Warrant.Evidence (SoundWarrant.warrant sw) → A
sound-extract sw token = SoundWarrant.sound sw token

-- ===========================================================================
-- Composition transport beyond Echo.Echo.
-- ===========================================================================

-- The minimal concatenation isomorphism the composition transport rests
-- on: ⟦ [E] ++ [F] ⟧ ≅ ⟦ [E] ⟧ × ⟦ [F] ⟧, inverse on both sides
-- (the singleton instance of Composition.split / join).  Echo.Echo has no
-- concatenation of contexts: this law has no counterpart among Echo's
-- laws, which are all laws of a single fibre.
split-singleton : ∀ {w} {W : Set w} (world : W)
  (E : W → Set) (F : W → Set) →
  ⟦ E ∷ F ∷ [] ⟧ world → ⟦ E ∷ [] ⟧ world × ⟦ F ∷ [] ⟧ world
split-singleton world E F (e , (f , tt)) = (e , tt) , (f , tt)

join-singleton : ∀ {w} {W : Set w} (world : W)
  (E : W → Set) (F : W → Set) →
  ⟦ E ∷ [] ⟧ world × ⟦ F ∷ [] ⟧ world → ⟦ E ∷ F ∷ [] ⟧ world
join-singleton world E F ((e , tt) , (f , tt)) = e , f , tt

join-singleton-split : ∀ {w} {W : Set w} (world : W)
  (E : W → Set) (F : W → Set)
  (evidence : ⟦ E ∷ F ∷ [] ⟧ world) →
  join-singleton world E F (split-singleton world E F evidence) ≡ evidence
join-singleton-split world E F (e , (f , tt)) = refl

split-singleton-join : ∀ {w} {W : Set w} (world : W)
  (E : W → Set) (F : W → Set)
  (evidence : ⟦ E ∷ [] ⟧ world × ⟦ F ∷ [] ⟧ world) →
  split-singleton world E F (join-singleton world E F evidence) ≡ evidence
split-singleton-join world E F ((e , tt) , (f , tt)) = refl

-- The composition transport in its minimal form: claims under two evidence
-- predicates E and F compose into a claim under their pointwise product
-- E × F, for a composed case that is supplied explicitly (the singleton
-- instance of Composition.compose-claims).  The fibre here is the Echo.Echo
-- fibre; what the transport additionally needs is the pointwise product of
-- the evidence — a structure Echo.Echo does not carry, since
-- Echo observe r has no evidence parameter at all.
composition-transport : ∀ {w o e f p q} {W : Set w} {O : Set o}
  {observe : W → O} {r : O} {E : W → Set e} {F : W → Set f}
  {P : W → Set p} {Q : W → Set q}
  (left : Case observe r E) (right : Case observe r F)
  (both : Case observe r (λ world → E world × F world)) →
  Holds left P → Holds right Q → Holds both (λ world → P world × Q world)
composition-transport left right both claimP claimQ
  (world , observed , (evidence-E , evidence-F)) =
  claimP (world , observed , evidence-E) ,
  claimQ (world , observed , evidence-F)

-- Minimal worked example: [NoiseBound] ++ [NoNoise] yields presence and
-- the identified value at once (Examples.Composition.present-and-two).
composition-example : Holds both (λ world → Present world × (contribution world ≡ 2))
composition-example = present-and-two

-- ===========================================================================
-- Revision transport beyond SoundWarrant.
-- ===========================================================================

-- The minimal retraction transport: retracting the LAST assumption of
-- E × F keeps the world and the observation (Revision.retract-case,
-- singleton instance).
retraction-case : ∀ {w o e f} {W : Set w} {O : Set o} {observe : W → O} {r : O}
  {E : W → Set e} {F : W → Set f} →
  Case observe r (λ world → E world × F world) → Case observe r E
retraction-case (inhabited (world , observed , (evidence-E , _))) =
  inhabited (world , observed , evidence-E)

-- A claim under the kept evidence E transfers to the case under E × F.
retraction-claim : ∀ {w o e f p} {W : Set w} {O : Set o} {observe : W → O} {r : O}
  {E : W → Set e} {F : W → Set f} {P : W → Set p} →
  (c : Case observe r (λ world → E world × F world)) →
  Holds (retraction-case c) P → Holds c P
retraction-claim c claim (world , observed , (evidence-E , _)) =
  claim (world , observed , evidence-E)

-- The minimal revision transport: retract F from E × F and assume G.  A
-- claim resting on E transfers to the revised case, which is supplied
-- (the singleton instance of Revision.survives-retraction / revise).
-- SoundWarrant has no such transport: its sound field is fixed at
-- construction for ONE evidence type, with no support condition and no
-- revision.
revision-transport : ∀ {w o e f g p} {W : Set w} {O : Set o} {observe : W → O} {r : O}
  {E : W → Set e} {F : W → Set f} {G : W → Set g} {P : W → Set p} →
  (c : Case observe r (λ world → E world × F world))
  (c′ : Case observe r (λ world → E world × G world)) →
  Holds (retraction-case c) P → Holds c′ P
revision-transport c c′ claim (world′ , observed′ , (evidence-E′ , _)) =
  claim (world′ , observed′ , evidence-E′)

-- Minimal worked examples of the retraction and revision transports:
-- presence survives retracting NoNoise, the assumption it does not rest on
-- (Examples.Revision.presence-survives); presence transfers to the revised
-- case after NoNoise is replaced by Balanced
-- (Examples.Revision.presence-after-revision).
retraction-example : Holds (retract-case drop-no-noise both) Present
retraction-example = presence-survives

revision-example : Holds balanced-ctx Present
revision-example = presence-after-revision
