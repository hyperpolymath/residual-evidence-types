{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

module ResidualEvidence.Prelude where

open import Agda.Primitive using (Level; _⊔_) public
open import Agda.Builtin.Equality using (_≡_; refl) public
open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd) public
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_) public
open import Agda.Builtin.Unit using (⊤; tt) public

data ⊥ : Set where

infix 3 ¬_
¬_ : ∀ {a} → Set a → Set a
¬ A = A → ⊥

infixr 4 _×_
_×_ : ∀ {a b} → Set a → Set b → Set (a ⊔ b)
A × B = Σ A (λ _ → B)

sym : ∀ {a} {A : Set a} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {a} {A : Set a} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl q = q

cong : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) {x y} → x ≡ y → f x ≡ f y
cong f refl = refl

infix 4 _≤_
data _≤_ : Nat → Nat → Set where
  z≤n : ∀ {n} → zero ≤ n
  s≤s : ∀ {m n} → m ≤ n → suc m ≤ suc n
