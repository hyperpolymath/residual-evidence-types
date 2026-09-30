{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

-- Soundness of the finite checker with respect to the Core vocabulary.
--
-- ResidualEvidence.Finite.Checker computes verdicts by running the
-- explorer's loops over the −6..6 world.  This module proves that those
-- verdicts mean what the Core says a verdict means:
--
--   entailed-sound      every candidate has a nonzero latent (Holds c Present)
--   refuted-sound       every candidate has a zero latent   (Holds c Absent)
--   unresolved-sound    a supporting and a counterexample candidate both exist
--   inconsistent-sound  no candidate exists at all
--   entailed-complete   the converse of entailed-sound
--   identified-sound    every candidate has the one listed latent (Identified c latent)
--   unidentified-sound  two candidates disagree on the latent
--   finite-actual-sound a verdict transfers to an actual world only with all
--                       three assumptions of Evidence supplied explicitly
--
-- The bridge is enumerate-sound / enumerate-complete: the worlds the loops
-- produce are exactly the Core candidates for the configuration, and the
-- first assumption of Evidence — that the world lies in −6..6 — is what the
-- completeness direction needs.  The explorer never states that assumption;
-- here nothing can be concluded about an actual world without it.

module ResidualEvidence.Finite.Soundness where

open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _<_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import ResidualEvidence.Prelude
  using (⊤; tt; ⊥; ¬_; Σ; _×_; _,_; fst; snd; _≤_; z≤n; s≤s; sym; trans)
open import ResidualEvidence.Core
  using (Candidate; Case; Holds; Identified;
         actual-world-sound; different-candidates-refute-identification)
open import ResidualEvidence.Context using (⟦_⟧)
open import ResidualEvidence.Finite.Int
  using (_==ᵢ_; ==ᵢ-sound; ==ᵢ-complete; ==ᵢ-refutes; bool-clash; _∈_; here; there; range)
open import ResidualEvidence.Finite.Row
open import ResidualEvidence.Finite.Checker

------------------------------------------------------------------------
-- Booleans

absurd : ∀ {A : Set} → ⊥ → A
absurd ()

infixr 1 _⊎_
data _⊎_ (A B : Set) : Set where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

∧-sound : ∀ a b → (a ∧ b) ≡ true → (a ≡ true) × (b ≡ true)
∧-sound true  b e = refl , e
∧-sound false b ()

∧-complete : ∀ {a b} → a ≡ true → b ≡ true → (a ∧ b) ≡ true
∧-complete refl refl = refl

∨-false : ∀ {a b} → a ≡ false → b ≡ false → (a ∨ b) ≡ false
∨-false refl refl = refl

∨-left : ∀ a b → (a ∨ b) ≡ false → a ≡ false
∨-left true  b ()
∨-left false b _ = refl

∨-right : ∀ a b → (a ∨ b) ≡ false → b ≡ false
∨-right true  b ()
∨-right false b e = e

not-true : ∀ b → not b ≡ true → b ≡ false
not-true true  ()
not-true false _ = refl

not-false : ∀ b → not b ≡ false → b ≡ true
not-false true  _ = refl
not-false false ()

not-so : ∀ b → ¬ (b ≡ true) → b ≡ false
not-so true  h = absurd (h refl)
not-so false _ = refl

<-sound : ∀ m n → (m < suc n) ≡ true → m ≤ n
<-sound zero    n       _ = z≤n
<-sound (suc m) zero    ()
<-sound (suc m) (suc n) e = s≤s (<-sound m n e)

<-complete : ∀ m n → m ≤ n → (m < suc n) ≡ true
<-complete zero    n       z≤n     = refl
<-complete (suc m) (suc n) (s≤s p) = <-complete m n p

------------------------------------------------------------------------
-- Membership

∈-nil : ∀ {w : World} {ws} → ws ≡ [] → w ∈ ws → ⊥
∈-nil refl ()

∈-head : ∀ {x y : Int} {xs} → x ≡ y → x ∈ (y ∷ xs)
∈-head refl = here

∈-single : ∀ {a v : Int} {xs} → xs ≡ (v ∷ []) → a ∈ xs → a ≡ v
∈-single refl here      = refl
∈-single refl (there ())

∷-inj : ∀ {x y : Int} {xs ys} → (x ∷ xs) ≡ (y ∷ ys) → (x ≡ y) × (xs ≡ ys)
∷-inj refl = refl , refl

first-∈ : ∀ {xs : List Int} {v rest} → xs ≡ (v ∷ rest) → v ∈ xs
first-∈ refl = here

shift : ∀ (P : World → Set) w ws →
  Σ World (λ w' → (w' ∈ ws) × P w') → Σ World (λ w' → (w' ∈ (w ∷ ws)) × P w')
shift P w ws (w' , m , q) = w' , there m , q

------------------------------------------------------------------------
-- any

any-true : ∀ p ws → any p ws ≡ true → Σ World (λ w → (w ∈ ws) × (p w ≡ true))
any-true-step : ∀ p w ws b → p w ≡ b → (b ∨ any p ws) ≡ true →
  Σ World (λ w' → (w' ∈ (w ∷ ws)) × (p w' ≡ true))
any-true p []       ()
any-true p (w ∷ ws) e = any-true-step p w ws (p w) refl e
any-true-step p w ws true  e _ = w , here , e
any-true-step p w ws false _ e = shift (λ w' → p w' ≡ true) w ws (any-true p ws e)

any-false : ∀ p ws w → any p ws ≡ false → w ∈ ws → p w ≡ false
any-false p (_ ∷ ws)  w e here      = ∨-left (p w) (any p ws) e
any-false p (w' ∷ ws) w e (there m) = any-false p ws w (∨-right (p w') (any p ws) e) m

none-any : ∀ p ws → (∀ w → w ∈ ws → p w ≡ false) → any p ws ≡ false
none-any p []       h = refl
none-any p (w ∷ ws) h = ∨-false (h w here) (none-any p ws (λ w' m → h w' (there m)))

------------------------------------------------------------------------
-- The verdict classifier

classify-entailed : ∀ a b → classify a b ≡ entailed → b ≡ false
classify-entailed a     false _ = refl
classify-entailed false true  ()
classify-entailed true  true  ()

classify-refuted : ∀ a b → classify a b ≡ refuted → (a ≡ false) × (b ≡ true)
classify-refuted a     false ()
classify-refuted false true  _ = refl , refl
classify-refuted true  true  ()

classify-unresolved : ∀ a b → classify a b ≡ unresolved → (a ≡ true) × (b ≡ true)
classify-unresolved a     false ()
classify-unresolved false true  ()
classify-unresolved true  true  _ = refl , refl

classify-consistent : ∀ a b → ¬ (classify a b ≡ inconsistent)
classify-consistent a     false ()
classify-consistent false true  ()
classify-consistent true  true  ()

classify-false : ∀ a {b} → b ≡ false → classify a b ≡ entailed
classify-false a refl = refl

presenceOf-entailed : ∀ ws → presenceOf ws ≡ entailed → any absent ws ≡ false
presenceOf-entailed []       ()
presenceOf-entailed (w ∷ ws) e = classify-entailed (any present (w ∷ ws)) (any absent (w ∷ ws)) e

presenceOf-refuted : ∀ ws → presenceOf ws ≡ refuted → any present ws ≡ false
presenceOf-refuted []       ()
presenceOf-refuted (w ∷ ws) e = fst (classify-refuted (any present (w ∷ ws)) (any absent (w ∷ ws)) e)

presenceOf-unresolved : ∀ ws → presenceOf ws ≡ unresolved →
  (any present ws ≡ true) × (any absent ws ≡ true)
presenceOf-unresolved []       ()
presenceOf-unresolved (w ∷ ws) e = classify-unresolved (any present (w ∷ ws)) (any absent (w ∷ ws)) e

presenceOf-inconsistent : ∀ ws → presenceOf ws ≡ inconsistent → ws ≡ []
presenceOf-inconsistent []       _ = refl
presenceOf-inconsistent (w ∷ ws) e =
  absurd (classify-consistent (any present (w ∷ ws)) (any absent (w ∷ ws)) e)

presenceOf-complete : ∀ ws → Σ World (λ w → w ∈ ws) → any absent ws ≡ false →
  presenceOf ws ≡ entailed
presenceOf-complete []       (w , ()) _
presenceOf-complete (w ∷ ws) _        e = classify-false (any present (w ∷ ws)) e

------------------------------------------------------------------------
-- The listed latents

-- Every candidate's latent is listed.
from-covers : ∀ x ws w → w ∈ ws → latent w ∈ (x ∷ latentsFrom x ws)
step-here : ∀ b x w ws → (x ==ᵢ latent w) ≡ b → latent w ∈ (x ∷ latentsStep b x w ws)
step-there : ∀ b x w' ws w → (∀ x' → latent w ∈ (x' ∷ latentsFrom x' ws)) →
  latent w ∈ (x ∷ latentsStep b x w' ws)
from-covers x (_ ∷ ws)  w here      = step-here (x ==ᵢ latent w) x w ws refl
from-covers x (w' ∷ ws) w (there m) =
  step-there (x ==ᵢ latent w') x w' ws w (λ x' → from-covers x' ws w m)
step-here true  x w ws e = ∈-head (sym (==ᵢ-sound x (latent w) e))
step-here false x w ws _ = there here
step-there true  x w' ws w ih = ih x
step-there false x w' ws w ih = there (ih (latent w'))

latents-covers : ∀ ws w → w ∈ ws → latent w ∈ latents ws
latents-covers (_ ∷ ws)  w here      = here
latents-covers (w' ∷ ws) w (there m) = from-covers (latent w') ws w m

-- Every listed latent is some candidate's.
from-sound : ∀ x ws v → v ∈ latentsFrom x ws → Σ World (λ w → (w ∈ ws) × (latent w ≡ v))
step-sound : ∀ b x w ws v → v ∈ latentsStep b x w ws →
  Σ World (λ w' → (w' ∈ (w ∷ ws)) × (latent w' ≡ v))
from-sound x []       v ()
from-sound x (w ∷ ws) v m = step-sound (x ==ᵢ latent w) x w ws v m
step-sound true  x w ws v m         = shift (λ w' → latent w' ≡ v) w ws (from-sound x ws v m)
step-sound false x w ws _ here      = w , here , refl
step-sound false x w ws v (there m) = shift (λ w' → latent w' ≡ v) w ws (from-sound (latent w) ws v m)

-- The first latent listed after x is not x: repeats of the last listed
-- latent are dropped, so consecutive listed latents differ.
from-head : ∀ x ws v rest → latentsFrom x ws ≡ (v ∷ rest) → ¬ (x ≡ v)
step-head : ∀ b x w ws v rest → (x ==ᵢ latent w) ≡ b →
  (∀ v' rest' → latentsFrom x ws ≡ (v' ∷ rest') → ¬ (x ≡ v')) →
  latentsStep b x w ws ≡ (v ∷ rest) → ¬ (x ≡ v)
from-head x []       v rest ()
from-head x (w ∷ ws) v rest e = step-head (x ==ᵢ latent w) x w ws v rest refl (from-head x ws) e
step-head true  x w ws v rest _  ih e = ih v rest e
step-head false x w ws v rest ne _  e =
  λ xv → ==ᵢ-refutes x (latent w) ne (trans xv (sym (fst (∷-inj e))))

identityOf-identified : ∀ xs → identityOf xs ≡ identified → Σ Int (λ v → xs ≡ (v ∷ []))
identityOf-identified []          ()
identityOf-identified (v ∷ [])    _ = v , refl
identityOf-identified (_ ∷ _ ∷ _) ()

identityOf-unidentified : ∀ xs → identityOf xs ≡ unidentified →
  Σ Int (λ a → Σ Int (λ b → Σ (List Int) (λ rest → xs ≡ (a ∷ b ∷ rest))))
identityOf-unidentified []             ()
identityOf-unidentified (_ ∷ [])       ()
identityOf-unidentified (a ∷ b ∷ rest) _ = a , b , rest , refl

-- Two listed latents come from two candidates whose latents differ.
latents-split : ∀ ws a b rest → latents ws ≡ (a ∷ b ∷ rest) →
  Σ World (λ x → Σ World (λ y → (x ∈ ws) × (y ∈ ws) × (¬ (latent x ≡ latent y))))
latents-split []       a b rest ()
latents-split (w ∷ ws) a b rest e =
  w , fst r , here , there (fst (snd r)) ,
  λ eq → from-head (latent w) ws b rest e₂ (trans eq (snd (snd r)))
  where
    e₂ : latentsFrom (latent w) ws ≡ (b ∷ rest)
    e₂ = snd (∷-inj e)
    r : Σ World (λ w' → (w' ∈ ws) × (latent w' ≡ b))
    r = from-sound (latent w) ws b (first-∈ e₂)

------------------------------------------------------------------------
-- The loop condition

zero-sound : ∀ z l → zeroCheck z l ≡ true → Assumed z l
zero-sound false l _ = tt
zero-sound true  l e = ==ᵢ-sound l (pos 0) e

zero-complete : ∀ z l → Assumed z l → zeroCheck z l ≡ true
zero-complete false l _ = refl
zero-complete true  l e = ==ᵢ-complete l (pos 0) e

admits-sound : ∀ cfg w → admits cfg w ≡ true →
  (observe cfg w ≡ target cfg) × (Bounded cfg w × Zero cfg w)
admits-sound cfg w e =
  ==ᵢ-sound (observe cfg w) (target cfg) (snd e₂) ,
  <-sound (∣ noise w ∣) (noiseBound cfg) (fst e₁) ,
  zero-sound (assumeZero cfg) (latent w) (fst e₂)
  where
    b₁ = ∣ noise w ∣ < suc (noiseBound cfg)
    b₂ = zeroCheck (assumeZero cfg) (latent w)
    b₃ = observe cfg w ==ᵢ target cfg
    e₁ : (b₁ ≡ true) × ((b₂ ∧ b₃) ≡ true)
    e₁ = ∧-sound b₁ (b₂ ∧ b₃) e
    e₂ : (b₂ ≡ true) × (b₃ ≡ true)
    e₂ = ∧-sound b₂ b₃ (snd e₁)

admits-complete : ∀ cfg w → observe cfg w ≡ target cfg → Bounded cfg w → Zero cfg w →
  admits cfg w ≡ true
admits-complete cfg w obs bnd asm =
  ∧-complete (<-complete (∣ noise w ∣) (noiseBound cfg) bnd)
             (∧-complete (zero-complete (assumeZero cfg) (latent w) asm)
                         (==ᵢ-complete (observe cfg w) (target cfg) obs))

------------------------------------------------------------------------
-- The loops

consIf-∈ : ∀ b w ws w' → w' ∈ consIf b w ws → ((b ≡ true) × (w' ≡ w)) ⊎ (w' ∈ ws)
consIf-∈ true  w ws _  here      = inl (refl , refl)
consIf-∈ true  w ws w' (there m) = inr m
consIf-∈ false w ws w' m         = inr m

consIf-here : ∀ b w ws → b ≡ true → w ∈ consIf b w ws
consIf-here _ w ws refl = here

consIf-there : ∀ b w ws w' → w' ∈ ws → w' ∈ consIf b w ws
consIf-there true  w ws w' m = there m
consIf-there false w ws w' m = m

noiseLoop-sound : ∀ cfg l ns rest w → w ∈ noiseLoop cfg l ns rest →
  ((latent w ≡ l) × (noise w ∈ ns) × (admits cfg w ≡ true)) ⊎ (w ∈ rest)
noiseLoop-step : ∀ cfg l n ns rest w →
  ((admits cfg (l , n) ≡ true) × (w ≡ (l , n))) ⊎ (w ∈ noiseLoop cfg l ns rest) →
  ((latent w ≡ l) × (noise w ∈ (n ∷ ns)) × (admits cfg w ≡ true)) ⊎ (w ∈ rest)
noiseLoop-extend : ∀ cfg l n ns rest w →
  ((latent w ≡ l) × (noise w ∈ ns) × (admits cfg w ≡ true)) ⊎ (w ∈ rest) →
  ((latent w ≡ l) × (noise w ∈ (n ∷ ns)) × (admits cfg w ≡ true)) ⊎ (w ∈ rest)
noiseLoop-sound cfg l []       rest w m = inr m
noiseLoop-sound cfg l (n ∷ ns) rest w m =
  noiseLoop-step cfg l n ns rest w
    (consIf-∈ (admits cfg (l , n)) (l , n) (noiseLoop cfg l ns rest) w m)
noiseLoop-step cfg l n ns rest _ (inl (a , refl)) = inl (refl , here , a)
noiseLoop-step cfg l n ns rest w (inr m) =
  noiseLoop-extend cfg l n ns rest w (noiseLoop-sound cfg l ns rest w m)
noiseLoop-extend cfg l n ns rest w (inl (e , mn , a)) = inl (e , there mn , a)
noiseLoop-extend cfg l n ns rest w (inr m)            = inr m

there-first : ∀ {A : Set} {y : Int} {ys x} → (x ∈ ys) × A → (x ∈ (y ∷ ys)) × A
there-first (m , a) = there m , a

latentLoop-sound : ∀ cfg ls w → w ∈ latentLoop cfg ls →
  (latent w ∈ ls) × (noise w ∈ range) × (admits cfg w ≡ true)
latentLoop-step : ∀ cfg l ls w →
  ((latent w ≡ l) × (noise w ∈ range) × (admits cfg w ≡ true)) ⊎ (w ∈ latentLoop cfg ls) →
  (latent w ∈ (l ∷ ls)) × (noise w ∈ range) × (admits cfg w ≡ true)
latentLoop-sound cfg []       w ()
latentLoop-sound cfg (l ∷ ls) w m =
  latentLoop-step cfg l ls w (noiseLoop-sound cfg l range (latentLoop cfg ls) w m)
latentLoop-step cfg l ls w (inl (e , mn , a)) = ∈-head e , mn , a
latentLoop-step cfg l ls w (inr m)            = there-first (latentLoop-sound cfg ls w m)

-- Everything the loops produce satisfies the loop condition and lies in range.
enumerate-sound : ∀ cfg w → w ∈ enumerate cfg → InRange w × (admits cfg w ≡ true)
enumerate-sound cfg w m = (fst r , fst (snd r)) , snd (snd r)
  where r = latentLoop-sound cfg range w m

noiseLoop-here : ∀ cfg l ns rest n → n ∈ ns → admits cfg (l , n) ≡ true →
  (l , n) ∈ noiseLoop cfg l ns rest
noiseLoop-here cfg l (_ ∷ ns)  rest n here      a =
  consIf-here (admits cfg (l , n)) (l , n) (noiseLoop cfg l ns rest) a
noiseLoop-here cfg l (n' ∷ ns) rest n (there m) a =
  consIf-there (admits cfg (l , n')) (l , n') (noiseLoop cfg l ns rest) (l , n)
    (noiseLoop-here cfg l ns rest n m a)

noiseLoop-rest : ∀ cfg l ns rest w → w ∈ rest → w ∈ noiseLoop cfg l ns rest
noiseLoop-rest cfg l []       rest w m = m
noiseLoop-rest cfg l (n ∷ ns) rest w m =
  consIf-there (admits cfg (l , n)) (l , n) (noiseLoop cfg l ns rest) w
    (noiseLoop-rest cfg l ns rest w m)

latentLoop-complete : ∀ cfg ls l n → l ∈ ls → n ∈ range → admits cfg (l , n) ≡ true →
  (l , n) ∈ latentLoop cfg ls
latentLoop-complete cfg (_ ∷ ls)  l n here       mn a =
  noiseLoop-here cfg l range (latentLoop cfg ls) n mn a
latentLoop-complete cfg (l' ∷ ls) l n (there ml) mn a =
  noiseLoop-rest cfg l' range (latentLoop cfg ls) (l , n) (latentLoop-complete cfg ls l n ml mn a)

-- Everything in range that satisfies the loop condition is produced.  This
-- is where the in-range assumption of Evidence is spent.
enumerate-complete : ∀ cfg w → InRange w → admits cfg w ≡ true → w ∈ enumerate cfg
enumerate-complete cfg (l , n) (ml , mn) a = latentLoop-complete cfg range l n ml mn a

------------------------------------------------------------------------
-- Candidates are exactly the enumerated worlds

candidate-∈ : ∀ cfg (x : FiniteCandidate cfg) → fst x ∈ enumerate cfg
candidate-∈ cfg (w , obs , inRange , bnd , asm , tt) =
  enumerate-complete cfg w inRange (admits-complete cfg w obs bnd asm)

∈-candidate : ∀ cfg w → w ∈ enumerate cfg → FiniteCandidate cfg
∈-candidate cfg w m = w , fst a , fst s , fst (snd a) , snd (snd a) , tt
  where
    s = enumerate-sound cfg w m
    a = admits-sound cfg w (snd s)

------------------------------------------------------------------------
-- Presence

entailed-sound : ∀ cfg (c : FiniteCase cfg) → presence cfg ≡ entailed → Holds c Present
entailed-sound cfg c e x z =
  bool-clash
    (any-false absent (enumerate cfg) (fst x) (presenceOf-entailed (enumerate cfg) e) (candidate-∈ cfg x))
    (==ᵢ-complete (latent (fst x)) (pos 0) z)

refuted-sound : ∀ cfg (c : FiniteCase cfg) → presence cfg ≡ refuted → Holds c Absent
refuted-sound cfg c e x =
  ==ᵢ-sound (latent (fst x)) (pos 0)
    (not-false (latent (fst x) ==ᵢ pos 0)
      (any-false present (enumerate cfg) (fst x) (presenceOf-refuted (enumerate cfg) e) (candidate-∈ cfg x)))

unresolved-sound : ∀ cfg → presence cfg ≡ unresolved →
  Σ (FiniteCandidate cfg) (λ x → Present (fst x)) × Σ (FiniteCandidate cfg) (λ y → Absent (fst y))
unresolved-sound cfg e = supporting , counterexample
  where
    u = presenceOf-unresolved (enumerate cfg) e
    s = any-true present (enumerate cfg) (fst u)
    a = any-true absent (enumerate cfg) (snd u)
    supporting : Σ (FiniteCandidate cfg) (λ x → Present (fst x))
    supporting =
      ∈-candidate cfg (fst s) (fst (snd s)) ,
      ==ᵢ-refutes (latent (fst s)) (pos 0) (not-true (latent (fst s) ==ᵢ pos 0) (snd (snd s)))
    counterexample : Σ (FiniteCandidate cfg) (λ y → Absent (fst y))
    counterexample =
      ∈-candidate cfg (fst a) (fst (snd a)) ,
      ==ᵢ-sound (latent (fst a)) (pos 0) (snd (snd a))

inconsistent-sound : ∀ cfg → presence cfg ≡ inconsistent → ¬ FiniteCase cfg
inconsistent-sound cfg e c =
  ∈-nil (presenceOf-inconsistent (enumerate cfg) e) (candidate-∈ cfg (Case.witness c))

entailed-complete : ∀ cfg (c : FiniteCase cfg) → Holds c Present → presence cfg ≡ entailed
entailed-complete cfg c holds =
  presenceOf-complete (enumerate cfg)
    (fst (Case.witness c) , candidate-∈ cfg (Case.witness c))
    (none-any absent (enumerate cfg)
      (λ w m → not-so (latent w ==ᵢ pos 0)
        (λ t → holds (∈-candidate cfg w m) (==ᵢ-sound (latent w) (pos 0) t))))

------------------------------------------------------------------------
-- Identity

identified-sound : ∀ cfg (c : FiniteCase cfg) → identity cfg ≡ identified → Identified c latent
identified-sound cfg c e =
  fst v , λ x → ∈-single (snd v) (latents-covers (enumerate cfg) (fst x) (candidate-∈ cfg x))
  where v = identityOf-identified (latents (enumerate cfg)) e

unidentified-sound : ∀ cfg → identity cfg ≡ unidentified →
  Σ (FiniteCandidate cfg) (λ x → Σ (FiniteCandidate cfg) (λ y → ¬ (latent (fst x) ≡ latent (fst y))))
unidentified-sound cfg e =
  ∈-candidate cfg (fst d) (fst (snd (snd d))) ,
  ∈-candidate cfg (fst (snd d)) (fst (snd (snd (snd d)))) ,
  snd (snd (snd (snd d)))
  where
    u = identityOf-unidentified (latents (enumerate cfg)) e
    d = latents-split (enumerate cfg) (fst u) (fst (snd u)) (fst (snd (snd u))) (snd (snd (snd u)))

unidentified-refutes : ∀ cfg (c : FiniteCase cfg) → identity cfg ≡ unidentified →
  ¬ Identified c latent
unidentified-refutes cfg c e =
  different-candidates-refute-identification c latent (fst d) (fst (snd d)) (snd (snd d))
  where d = unidentified-sound cfg e

------------------------------------------------------------------------
-- Transfer to an actual world

-- A finite verdict says something about an actual world only when all
-- three assumptions of Evidence hold of it: the world is in −6..6, the
-- noise is within the bound, and the latent is zero if that was assumed.
-- The explorer hides the first inside its loop bounds; here it is a premise.
finite-actual-sound : ∀ cfg (c : FiniteCase cfg) (claim : World → Set) → Holds c claim →
  (actual : World) → observe cfg actual ≡ target cfg →
  InRange actual → Bounded cfg actual → Zero cfg actual → claim actual
finite-actual-sound cfg c claim holds actual observed inRange bounded assumed =
  actual-world-sound c holds actual observed (inRange , bounded , assumed , tt)

------------------------------------------------------------------------
-- Positive controls: rows derived by hand in
-- tests/correspondence/explorer.test.js, decided here by normalisation.

-- residual −6, bound 0, exact: only (−6, 0).
_ : report (config (negsuc 5) 0 exact false) ≡
    row (negsuc 5) 0 exact false 1 entailed identified (negsuc 5 ∷ [])
_ = refl

-- ... and assuming zero leaves nothing.
_ : report (config (negsuc 5) 0 exact true) ≡
    row (negsuc 5) 0 exact true 0 inconsistent no-candidate []
_ = refl

-- residual 2, bound 6, exact, assuming zero: only (0, 2), so presence is refuted.
_ : report (config (pos 2) 6 exact true) ≡
    row (pos 2) 6 exact true 1 refuted identified (pos 0 ∷ [])
_ = refl

-- residual 2, bound 1, exact: (1, 1), (2, 0), (3, −1); present but not identified.
_ : report (config (pos 2) 1 exact false) ≡
    row (pos 2) 1 exact false 3 entailed unidentified (pos 1 ∷ pos 2 ∷ pos 3 ∷ [])
_ = refl

-- residual −6, bound 1, sign, assuming zero: only (0, −1), whose sum is negative.
_ : report (config (negsuc 5) 1 sign true) ≡
    row (negsuc 5) 1 sign true 1 refuted identified (pos 0 ∷ [])
_ = refl

-- residual −6, bound 0, magnitude: (−6, 0) and (6, 0).
_ : report (config (negsuc 5) 0 magnitude false) ≡
    row (negsuc 5) 0 magnitude false 2 entailed unidentified (negsuc 5 ∷ pos 6 ∷ [])
_ = refl
