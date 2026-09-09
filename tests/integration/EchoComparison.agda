{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

module EchoComparison where

open import ResidualEvidence.Prelude
open import ResidualEvidence.Core
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
