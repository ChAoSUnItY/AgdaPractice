{-# OPTIONS --exact-split #-}

module Bin where
import Relation.Binary.PropositionalEquality as Eq
import Data.Nat as Nat
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)
open Nat using (ℕ; zero; suc; _+_; _*_; _^_; _∸_)

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩
inc (b O) = b I
inc (b I) = (inc b) O

_ : inc (⟨⟩ O I) ≡ (⟨⟩ I O)
_ =
  begin
    inc (⟨⟩ O I)
  ≡⟨⟩
    (inc (⟨⟩ O)) O
  ≡⟨⟩
    (⟨⟩ I) O
  ≡⟨⟩
    ⟨⟩ I O
  ∎

-- Converts to 2 bit binary number
to : ℕ → Bin
to 0 = ⟨⟩ O O
to (suc n) = inc (to n)

-- Proves 2 concerts to `10` 2 bit binary number
_ : to 2 ≡ (⟨⟩ I O)
_ =
  begin
    to 2
  ≡⟨⟩
    inc (to 1)
  ≡⟨⟩
    inc (inc (to 0))
  ≡⟨⟩
    inc (inc (⟨⟩ O O))
  ≡⟨⟩
    inc (⟨⟩ O I)
  ≡⟨⟩
    (⟨⟩ I O)
  ∎

from : Bin → ℕ
from ⟨⟩ = 0
from (b O) = 2 * (from b) + 0
from (b I) = 2 * (from b) + 1

-- Proves `11` 2 bit binary number converts to 3
_ : from (⟨⟩ I I) ≡ 3
_ =
  begin
    from (⟨⟩ I I)
  ≡⟨⟩
    2 * (from (⟨⟩ I)) + 1
  ≡⟨⟩
    2 * (2 * (from ⟨⟩) + 1) + 1
  ≡⟨⟩
    2 * (2 * 0 + 1) + 1
  ≡⟨⟩
    2 * 1 + 1
  ≡⟨⟩
    2 + 1
  ≡⟨⟩
    3
  ∎
