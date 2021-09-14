{-# OPTIONS --allow-unsolved-metas #-} 

module Homework.LeftistHeap.Common where

open import Lib.Nat
open import Lib.One
open import Lib.Zero
open import Lib.Sum
open import Lib.Eq

-- Rank ще използваме, когато говорим за рангове, 
-- докато Priority ще наричаме стойностите, които вмъкваме в пирамидата.

Leq : Nat -> Nat -> Set
Leq zero m = One
Leq (suc n) zero = Zero
Leq (suc n) (suc m) = Leq n m

decLeq : (n m : Nat) -> Leq n m + Leq m n
decLeq zero m = inl <>
decLeq (suc n) zero = inr <>
decLeq (suc n) (suc m) = decLeq n m

<=-Leq : {n m : Nat} -> n <= m -> Leq n m
<=-Leq ozero = <>
<=-Leq (osuc p) = <=-Leq p

Leq-refl : (n : Nat) -> Leq n n
Leq-refl n = <=-Leq (<=-refl n)

Leq-trans : (n m k : Nat) -> Leq n m -> Leq m k -> Leq n k
Leq-trans zero m k p q = <>
Leq-trans (suc n) (suc m) (suc k) p q = Leq-trans n m k p q

Priority : Set
Priority = Nat

Rank : Set
Rank = Nat

data Maybe (A : Set) : Set where
  no : Maybe A
  yes : A -> Maybe A

--!
min : Nat -> Nat -> Nat
min zero m = zero
min (suc n) zero = zero
min (suc n) (suc m) = suc (min n m)
-- Leq : Nat -> Nat -> Set (По-малко или равно)
-- Leq zero m = One
-- Leq (suc n) zero = Zero
-- Leq (suc n) (suc m) = Leq n m
min-Leq-left : (n m : Nat) -> Leq (min n m) n
min-Leq-left zero m = <>
min-Leq-left (suc n) zero = <>
min-Leq-left (suc n) (suc m) = min-Leq-left n m

min-right-zero : (m : Nat) -> min m zero == zero
min-right-zero zero = refl
min-right-zero (suc m) = refl

min-symm : (n m : Nat) -> min n m == min m n
min-symm zero zero = refl
min-symm zero (suc m) = refl
min-symm (suc n) zero = refl
min-symm (suc n) (suc m) = ap suc (min-symm n m)

min-Leq-right : (n m : Nat) -> Leq (min n m) m
min-Leq-right zero m = <>
min-Leq-right (suc n) zero = <>
min-Leq-right (suc n) (suc m) = min-Leq-right n m