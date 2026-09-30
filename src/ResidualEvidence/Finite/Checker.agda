{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

-- The certified finite checker: the explorer's JavaScript model
-- (`residual-evidence-explorer.html`, model 'signed-integer-v1') written as
-- total functions over the −6..6 world, so that every verdict the page
-- shows is decided by normalisation and every row of `table` is a closed
-- term.  ResidualEvidence.Finite.Soundness proves the verdicts sound with
-- respect to the Core vocabulary (Candidate, Case, Holds, Identified), and
-- the correspondence theorem `table ≡ ExplorerTable.expected` is `refl`.
--
-- A world is a (latent, noise) pair.  The explorer observes the sum through
-- one of three views and keeps a world when the noise is within the bound,
-- the latent is zero if that is assumed, and the observed sum matches the
-- observed residual.  What the explorer never writes down is that its loops
-- only visit −6..6: here that is the first assumption of `Evidence`, so a
-- Core candidate for a configuration is exactly a world the enumeration
-- produces (Soundness: enumerate-sound / enumerate-complete), and applying a
-- verdict to an actual world demands the in-range premise explicitly.  The
-- premise is what the enumeration needs; nothing here claims it is necessary
-- for the two queries the explorer asks.
--
-- Integers are spelled with the builtin constructors: `pos n` for n ≥ 0 and
-- `negsuc n` for −(n+1).  So −6 is `negsuc 5` and 6 is `pos 6`.

module ResidualEvidence.Finite.Checker where

open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _<_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import ResidualEvidence.Prelude using (⊤; tt; ¬_; _×_; _,_; fst; snd; _≤_)
open import ResidualEvidence.Core using (Candidate; Case)
open import ResidualEvidence.Context using (Ctx; ⟦_⟧)
open import ResidualEvidence.Finite.Int using (_+ᵢ_; absᵢ; signᵢ; _==ᵢ_; _∈_; range)
open import ResidualEvidence.Finite.Row

------------------------------------------------------------------------
-- Booleans and lists (the builtins provide only the constructors)

not : Bool → Bool
not true  = false
not false = true

infixr 6 _∧_
_∧_ : Bool → Bool → Bool
true  ∧ b = b
false ∧ _ = false

infixr 5 _∨_
_∨_ : Bool → Bool → Bool
true  ∨ _ = true
false ∨ b = b

length : ∀ {A : Set} → List A → Nat
length [] = zero
length (_ ∷ xs) = suc (length xs)

map : ∀ {A B : Set} → (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

-- One iteration of a JavaScript `for` loop: visit each element in order,
-- threading the rest of the output through.
forEach : ∀ {A B : Set} → List A → (A → List B → List B) → List B → List B
forEach [] body rest = rest
forEach (x ∷ xs) body rest = body x (forEach xs body rest)

------------------------------------------------------------------------
-- Worlds, views and configurations

World : Set
World = Int × Int

latent noise : World → Int
latent = fst
noise = snd

-- |x| as a natural number; absᵢ x ≡ pos ∣ x ∣.
∣_∣ : Int → Nat
∣ pos n ∣ = n
∣ negsuc n ∣ = suc n

-- The explorer's views: exact = x ↦ x, sign = Math.sign, magnitude = Math.abs.
through : View → Int → Int
through exact x = x
through sign x = signᵢ x
through magnitude x = absᵢ x

record Config : Set where
  constructor config
  field
    residual   : Int   -- −6 .. 6
    noiseBound : Nat   -- 0 .. 6
    view       : View
    assumeZero : Bool
open Config public

-- The observation of a world and the observed residual, both through the view.
observe : Config → World → Int
observe cfg w = through (view cfg) (latent w +ᵢ noise w)

target : Config → Int
target cfg = through (view cfg) (residual cfg)

------------------------------------------------------------------------
-- The evidence a configuration assumes, as a Context

-- The explorer's loops visit exactly `range` for both coordinates.
InRange : World → Set
InRange w = (latent w ∈ range) × (noise w ∈ range)

-- |noise| ≤ noiseBound.
Bounded : Config → World → Set
Bounded cfg w = ∣ noise w ∣ ≤ noiseBound cfg

-- If assumeZero, the latent is zero; otherwise nothing is assumed.
Assumed : Bool → Int → Set
Assumed false _ = ⊤
Assumed true  l = l ≡ pos 0

Zero : Config → World → Set
Zero cfg w = Assumed (assumeZero cfg) (latent w)

Evidence : Config → Ctx World
Evidence cfg = InRange ∷ Bounded cfg ∷ Zero cfg ∷ []

-- A Core candidate / case for a configuration.
FiniteCandidate : Config → Set
FiniteCandidate cfg = Candidate (observe cfg) (target cfg) ⟦ Evidence cfg ⟧

FiniteCase : Config → Set
FiniteCase cfg = Case (observe cfg) (target cfg) ⟦ Evidence cfg ⟧

-- The two queries the explorer asks: `w.latent !== 0` and `w.latent`.
Present Absent : World → Set
Present w = ¬ (latent w ≡ pos 0)
Absent w = latent w ≡ pos 0

------------------------------------------------------------------------
-- Enumeration: the explorer's candidate loop

zeroCheck : Bool → Int → Bool
zeroCheck false _ = true
zeroCheck true  l = l ==ᵢ pos 0

-- The loop body's condition, minus the loop bounds.
admits : Config → World → Bool
admits cfg w =
  (∣ noise w ∣ < suc (noiseBound cfg)) ∧
  zeroCheck (assumeZero cfg) (latent w) ∧
  (observe cfg w ==ᵢ target cfg)

consIf : Bool → World → List World → List World
consIf true  w ws = w ∷ ws
consIf false w ws = ws

-- for (noise of ns) if (admits) candidates.push({latent, noise}); then rest.
noiseLoop : Config → Int → List Int → List World → List World
noiseLoop cfg l [] rest = rest
noiseLoop cfg l (n ∷ ns) rest = consIf (admits cfg (l , n)) (l , n) (noiseLoop cfg l ns rest)

-- for (latent of ls) for (noise of range) ...
latentLoop : Config → List Int → List World
latentLoop cfg [] = []
latentLoop cfg (l ∷ ls) = noiseLoop cfg l range (latentLoop cfg ls)

-- c.candidates, in the explorer's order: latent ascending, then noise.
enumerate : Config → List World
enumerate cfg = latentLoop cfg range

------------------------------------------------------------------------
-- Verdicts: decide(c, w => w.latent !== 0) and identify(c, w => w.latent)

present absent : World → Bool
present w = not (latent w ==ᵢ pos 0)
absent w = latent w ==ᵢ pos 0

any : (World → Bool) → List World → Bool
any p [] = false
any p (w ∷ ws) = p w ∨ any p ws

-- classify supporting? counterexample?: no counterexample is entailed,
-- otherwise no support is refuted, otherwise unresolved.
classify : Bool → Bool → Verdict
classify _     false = entailed
classify false true  = refuted
classify true  true  = unresolved

presenceOf : List World → Verdict
presenceOf [] = inconsistent
presenceOf ws@(_ ∷ _) = classify (any present ws) (any absent ws)

-- The distinct latents of the candidates.  The latent loop is the outer
-- one, so the latents arrive in ascending runs and dropping repeats of the
-- previous latent leaves them ascending and distinct, which is what
-- identify's sorted Set yields.
latentsFrom : Int → List World → List Int
latentsStep : Bool → Int → World → List World → List Int
latentsFrom x [] = []
latentsFrom x (w ∷ ws) = latentsStep (x ==ᵢ latent w) x w ws
latentsStep true  x w ws = latentsFrom x ws
latentsStep false x w ws = latent w ∷ latentsFrom (latent w) ws

latents : List World → List Int
latents [] = []
latents (w ∷ ws) = latent w ∷ latentsFrom (latent w) ws

identityOf : List Int → IdStatus
identityOf [] = no-candidate
identityOf (_ ∷ []) = identified
identityOf (_ ∷ _ ∷ _) = unidentified

presence : Config → Verdict
presence cfg = presenceOf (enumerate cfg)

identity : Config → IdStatus
identity cfg = identityOf (latents (enumerate cfg))

------------------------------------------------------------------------
-- The table

summarise : Config → List World → Row
summarise cfg ws =
  row (residual cfg) (noiseBound cfg) (view cfg) (assumeZero cfg)
      (length ws) (presenceOf ws) (identityOf (latents ws)) (latents ws)

report : Config → Row
report cfg = summarise cfg (enumerate cfg)

bounds : List Nat
bounds = 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ []

views : List View
views = exact ∷ sign ∷ magnitude ∷ []

flags : List Bool
flags = false ∷ true ∷ []

-- The 546 configurations in the explorer's order: residual −6..6 (outer),
-- noise bound 0..6, view exact | sign | magnitude, assumeZero false | true.
allConfigs : List Config
allConfigs =
  forEach range  (λ r →
  forEach bounds (λ b →
  forEach views  (λ v →
  forEach flags  (λ z →
  config r b v z ∷_)))) []

table : List Row
table = map report allConfigs

------------------------------------------------------------------------
-- The configuration count is closed and decided by normalisation:
-- 13 residuals × 7 bounds × 3 views × 2 flags.  The known-answer rows and
-- the soundness of every verdict live in ResidualEvidence.Finite.Soundness.

_ : length allConfigs ≡ 546
_ = refl
