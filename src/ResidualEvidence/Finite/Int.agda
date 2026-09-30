{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

-- Integer arithmetic and the −6..6 residual range for the certified finite
-- checker.  Every operation is total and computes by pattern matching on the
-- builtin constructors, so the correspondence with the explorer's JavaScript
-- model (`residual-evidence-explorer.html`) is decided by normalisation.
--
-- Integers are spelled with the builtin constructors: `pos n` for n ≥ 0 and
-- `negsuc n` for −(n+1).  So −6 is `negsuc 5` and 6 is `pos 6`.

module ResidualEvidence.Finite.Int where

open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _==_; _<_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import ResidualEvidence.Prelude using (⊥; ¬_; _×_; _,_)

------------------------------------------------------------------------
-- Arithmetic

-- m ⊖ n = m − n, landing in whichever constructor the sign demands.
infixl 6 _⊖_
_⊖_ : Nat → Nat → Int
m     ⊖ zero  = pos m
zero  ⊖ suc n = negsuc n
suc m ⊖ suc n = m ⊖ n

infixl 6 _+ᵢ_
_+ᵢ_ : Int → Int → Int
pos m    +ᵢ pos n    = pos (m + n)
pos m    +ᵢ negsuc n = m ⊖ suc n
negsuc m +ᵢ pos n    = n ⊖ suc m
negsuc m +ᵢ negsuc n = negsuc (suc (m + n))

negᵢ : Int → Int
negᵢ (pos zero)    = pos zero
negᵢ (pos (suc n)) = negsuc n
negᵢ (negsuc n)    = pos (suc n)

-- JS Math.abs; the result is always `pos _`.
absᵢ : Int → Int
absᵢ (pos n)    = pos n
absᵢ (negsuc n) = pos (suc n)

-- JS Math.sign: −1, 0 or 1.
signᵢ : Int → Int
signᵢ (pos zero)    = pos 0
signᵢ (pos (suc _)) = pos 1
signᵢ (negsuc _)    = negsuc 0

------------------------------------------------------------------------
-- Decidable equality and order

infix 4 _==ᵢ_
_==ᵢ_ : Int → Int → Bool
pos m    ==ᵢ pos n    = m == n
negsuc m ==ᵢ negsuc n = m == n
pos _    ==ᵢ negsuc _ = false
negsuc _ ==ᵢ pos _    = false

-- m ≤ n  ⇔  m < suc n on Nat; −(m+1) ≤ −(n+1)  ⇔  n ≤ m.
infix 4 _≤ᵇ_
_≤ᵇ_ : Int → Int → Bool
pos m    ≤ᵇ pos n    = m < suc n
negsuc m ≤ᵇ negsuc n = n < suc m
negsuc _ ≤ᵇ pos _    = true
pos _    ≤ᵇ negsuc _ = false

------------------------------------------------------------------------
-- Soundness and completeness of _==ᵢ_ with respect to _≡_

cong-suc : ∀ {m n : Nat} → m ≡ n → suc m ≡ suc n
cong-suc refl = refl

cong-pos : ∀ {m n : Nat} → m ≡ n → pos m ≡ pos n
cong-pos refl = refl

cong-negsuc : ∀ {m n : Nat} → m ≡ n → negsuc m ≡ negsuc n
cong-negsuc refl = refl

==-sound : ∀ (m n : Nat) → (m == n) ≡ true → m ≡ n
==-sound zero    zero    _ = refl
==-sound zero    (suc n) ()
==-sound (suc m) zero    ()
==-sound (suc m) (suc n) p = cong-suc (==-sound m n p)

==-refl : ∀ (n : Nat) → (n == n) ≡ true
==-refl zero    = refl
==-refl (suc n) = ==-refl n

==ᵢ-sound : ∀ a b → (a ==ᵢ b) ≡ true → a ≡ b
==ᵢ-sound (pos m)    (pos n)    p = cong-pos (==-sound m n p)
==ᵢ-sound (negsuc m) (negsuc n) p = cong-negsuc (==-sound m n p)
==ᵢ-sound (pos m)    (negsuc n) ()
==ᵢ-sound (negsuc m) (pos n)    ()

==ᵢ-complete : ∀ a b → a ≡ b → (a ==ᵢ b) ≡ true
==ᵢ-complete (pos m)    .(pos m)    refl = ==-refl m
==ᵢ-complete (negsuc m) .(negsuc m) refl = ==-refl m

-- A Bool cannot be both false and true.
bool-clash : ∀ {b : Bool} → b ≡ false → b ≡ true → ⊥
bool-clash refl ()

==ᵢ-refutes : ∀ a b → (a ==ᵢ b) ≡ false → ¬ (a ≡ b)
==ᵢ-refutes a .a p refl = bool-clash p (==ᵢ-complete a a refl)

------------------------------------------------------------------------
-- List membership and the residual range

infix 4 _∈_
data _∈_ {A : Set} (x : A) : List A → Set where
  here  : ∀ {xs} → x ∈ (x ∷ xs)
  there : ∀ {y xs} → x ∈ xs → x ∈ (y ∷ xs)

-- Ascending −6..6, thirteen elements: the explorer's residual loop order.
range : List Int
range =
    negsuc 5 ∷ negsuc 4 ∷ negsuc 3 ∷ negsuc 2 ∷ negsuc 1 ∷ negsuc 0
  ∷ pos 0 ∷ pos 1 ∷ pos 2 ∷ pos 3 ∷ pos 4 ∷ pos 5 ∷ pos 6 ∷ []

-- Every member of `range` lies within the bounds; both bounds compute.
range-sound : ∀ x → x ∈ range → ((negsuc 5 ≤ᵇ x) ≡ true) × ((x ≤ᵇ pos 6) ≡ true)
range-sound _ here = refl , refl
range-sound _ (there here) = refl , refl
range-sound _ (there (there here)) = refl , refl
range-sound _ (there (there (there here))) = refl , refl
range-sound _ (there (there (there (there here)))) = refl , refl
range-sound _ (there (there (there (there (there here))))) = refl , refl
range-sound _ (there (there (there (there (there (there here)))))) = refl , refl
range-sound _ (there (there (there (there (there (there (there here))))))) = refl , refl
range-sound _ (there (there (there (there (there (there (there (there here)))))))) = refl , refl
range-sound _ (there (there (there (there (there (there (there (there (there here))))))))) = refl , refl
range-sound _ (there (there (there (there (there (there (there (there (there (there here)))))))))) = refl , refl
range-sound _ (there (there (there (there (there (there (there (there (there (there (there here))))))))))) = refl , refl
range-sound _ (there (there (there (there (there (there (there (there (there (there (there (there here)))))))))))) = refl , refl
range-sound _ (there (there (there (there (there (there (there (there (there (there (there (there (there ())))))))))))))

-- Every integer within the bounds is a member of `range`.  Outside the
-- bounds one of the two hypotheses normalises to `false ≡ true`.
range-complete : ∀ x → (negsuc 5 ≤ᵇ x) ≡ true → (x ≤ᵇ pos 6) ≡ true → x ∈ range
range-complete (negsuc 5) _ _ = here
range-complete (negsuc 4) _ _ = there here
range-complete (negsuc 3) _ _ = there (there here)
range-complete (negsuc 2) _ _ = there (there (there here))
range-complete (negsuc 1) _ _ = there (there (there (there here)))
range-complete (negsuc 0) _ _ = there (there (there (there (there here))))
range-complete (pos 0) _ _ = there (there (there (there (there (there here)))))
range-complete (pos 1) _ _ = there (there (there (there (there (there (there here))))))
range-complete (pos 2) _ _ = there (there (there (there (there (there (there (there here)))))))
range-complete (pos 3) _ _ = there (there (there (there (there (there (there (there (there here))))))))
range-complete (pos 4) _ _ = there (there (there (there (there (there (there (there (there (there here)))))))))
range-complete (pos 5) _ _ = there (there (there (there (there (there (there (there (there (there (there here))))))))))
range-complete (pos 6) _ _ = there (there (there (there (there (there (there (there (there (there (there (there here)))))))))))
range-complete (negsuc (suc (suc (suc (suc (suc (suc _))))))) () _
range-complete (pos (suc (suc (suc (suc (suc (suc (suc _)))))))) _ ()

------------------------------------------------------------------------
-- Positive control: concrete values, decided by normalisation.
-- Kept at the end of the module so that a defect in a definition above is
-- attributed to the first lemma it breaks, not to this block.

-- _+ᵢ_ on all four sign combinations.
_ : (negsuc 1 +ᵢ pos 5) ≡ pos 3        -- −2 + 5 = 3
_ = refl
_ : (pos 2 +ᵢ pos 3) ≡ pos 5           -- 2 + 3 = 5
_ = refl
_ : (pos 2 +ᵢ negsuc 4) ≡ negsuc 2     -- 2 + (−5) = −3
_ = refl
_ : (negsuc 1 +ᵢ negsuc 2) ≡ negsuc 4  -- (−2) + (−3) = −5
_ = refl
_ : (pos 3 +ᵢ negsuc 2) ≡ pos 0        -- 3 + (−3) = 0
_ = refl
_ : (negsuc 2 +ᵢ pos 3) ≡ pos 0        -- (−3) + 3 = 0
_ = refl

-- _⊖_ and negᵢ.
_ : (3 ⊖ 5) ≡ negsuc 1
_ = refl
_ : (5 ⊖ 3) ≡ pos 2
_ = refl
_ : negᵢ (pos 3) ≡ negsuc 2
_ = refl
_ : negᵢ (negsuc 2) ≡ pos 3
_ = refl
_ : negᵢ (pos 0) ≡ pos 0
_ = refl

-- absᵢ.
_ : absᵢ (negsuc 2) ≡ pos 3
_ = refl
_ : absᵢ (pos 4) ≡ pos 4
_ = refl

-- signᵢ on all three sign classes.
_ : signᵢ (negsuc 3) ≡ negsuc 0
_ = refl
_ : signᵢ (pos 0) ≡ pos 0
_ = refl
_ : signᵢ (pos 7) ≡ pos 1
_ = refl

-- _==ᵢ_.
_ : (negsuc 0 ==ᵢ negsuc 0) ≡ true
_ = refl
_ : (negsuc 0 ==ᵢ pos 1) ≡ false
_ = refl

-- _≤ᵇ_ on every clause.  The `pos _ ≤ᵇ negsuc _` clause is reached by no
-- range lemma (their hypotheses only compare against negsuc 5 and pos 6),
-- so this block is the only check that a positive is not ≤ a negative.
_ : (negsuc 5 ≤ᵇ pos 6) ≡ true
_ = refl
_ : (pos 6 ≤ᵇ negsuc 5) ≡ false
_ = refl
_ : (negsuc 4 ≤ᵇ negsuc 2) ≡ true      -- −5 ≤ −3
_ = refl
_ : (negsuc 2 ≤ᵇ negsuc 4) ≡ false     -- −3 ≤ −5 is false
_ = refl
_ : (pos 6 ≤ᵇ pos 6) ≡ true
_ = refl
_ : (pos 7 ≤ᵇ pos 6) ≡ false
_ = refl
