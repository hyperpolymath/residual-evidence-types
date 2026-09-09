{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
module FalsePresence where
open import ResidualEvidence.Core
open import ResidualEvidence.Examples.Presence

-- Must fail: the bounded theorem does not apply after dropping its evidence.
invalid : Holds unrestricted Present
invalid = bounded-presence
