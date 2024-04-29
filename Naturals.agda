{-# OPTIONS --exact-split #-}

module Naturals where
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

data ℕ : Set where
    zero : ℕ
    suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

_+_ : ℕ → ℕ → ℕ
zero    + n = n
(suc n) + n′ = suc (n + n′)

-- Proves
_ : 2 + 3 ≡ 5
_ =
  begin
    2 + 3
  ≡⟨⟩
    suc (1 + 3)
  ≡⟨⟩
    suc (suc (0 + 3))
  ≡⟨⟩
    suc (suc 3)
  ≡⟨⟩
    suc (suc (suc (suc (suc zero))))
  ≡⟨⟩
    5
  ∎

_*_ : ℕ → ℕ → ℕ
zero    * n  =  zero
(suc m) * n  =  n + (m * n)

-- Proves
_ : 2 * 5 ≡ 10
_ =
  begin
    2 * 5
  ≡⟨⟩
    5 + (1 * 5)
  ≡⟨⟩
    5 + (5 + (zero * 5))
  ≡⟨⟩
    5 + (5 + 0)
  ≡⟨⟩
    10
  ∎

_^_ : ℕ → ℕ → ℕ
n ^ zero = 1
n ^ (suc m) = n * (n ^ m)

-- Proves
_ : 2 ^ 2 ≡ 4
_ =
  begin
    2 ^ 2
  ≡⟨⟩
    2 * (2 ^ 1)
  ≡⟨⟩
    2 * (2 * (2 ^ 0))
  ≡⟨⟩
    2 * (2 * 1)
  ≡⟨⟩
    2 * 2
  ≡⟨⟩
    4
  ∎

_∸_ : ℕ → ℕ → ℕ
n       ∸ zero    = n
zero    ∸ (suc m) = zero
(suc n) ∸ (suc m) = n ∸ m

-- Proves positive monus
_ : 9 ∸ 2 ≡ 7
_ =
  begin
    9 ∸ 2
  ≡⟨⟩
    8 ∸ 1
  ≡⟨⟩
    7 ∸ 0
  ≡⟨⟩
    7
  ∎

-- Proves overflow monus
_ : 2 ∸ 9 ≡ 0
_ =
  begin
    2 ∸ 9
  ≡⟨⟩
    1 ∸ 8
  ≡⟨⟩
    0 ∸ 7
  ≡⟨⟩
    0
  ∎

infixl 6  _+_  _∸_
infixl 7  _*_


