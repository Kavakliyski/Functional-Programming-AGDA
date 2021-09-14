{-# OPTIONS --no-unicode #-}

module Homework.LeftistHeap.Full where

open import Lib.Nat
open import Lib.One
open import Lib.Eq
open import Lib.List
open import Lib.Sum
open import Homework.LeftistHeap.Common

data Heap (lower : Priority) : Rank -> Set where
    empty : Heap lower 0
    node : {r1 r2 : Rank} -> {Leq r1 r2} ->{x y : Priority} -> (p : Priority) 
        → Leq lower p -> Leq p x -> Leq p y -> Heap x r1 
        -> Heap y r2 -> Heap lower (suc (r1 +N r2))


mkNode : {lr rr : Rank} {b : Priority} (p : Priority) -> Leq b p 
    -> Heap p lr -> Heap p rr -> Heap b ((suc (lr +N rr)))
mkNode {lr} {rr} {b} p x x1 x2 with decLeq rr lr 
... | inl n = node p x (Leq-refl {! p !}) (Leq-refl p) x1 x2
... | inr n = {!   !}
    
{-# TERMINATING #-}
merge : {lr rr : Rank} {p : Priority} -> Heap p lr -> Heap p rr -> Heap p ((lr +N rr))
merge empty empty = empty
merge h1@(node p x x1 x2 x3 x4) empty = {!  !}
merge empty h2@(node p x1 x2 x3 x4 x5) = h2
merge (node p1 x x6 x7 x8 x9) (node p x1 x2 x3 x4 x5) = {!   !}

weakenHeap : {r : Rank} (n m : Priority) -> Leq n m -> Heap m r -> Heap n r
weakenHeap {.0} n m x empty = empty
weakenHeap {.(suc (_ +N _))} n m x (node p x1 x2 x3 x4 x5) 
    = mkNode {!   !} {!   !} {!   !} {!   !}

singleton : (p x : Priority) -> Leq p x -> Heap p 1
singleton p x p<=x = mkNode x p<=x empty empty

insert : {r : Rank} {p : Priority} (x : Priority) -> Heap p r -> Heap (min p x) (suc r)
insert {r} {p} x x1 with decLeq p x
... | inl n = merge {!   !} {!   !}
... | inr n = merge {!   !} {!   !}

findMin : {p : Priority} {r : Rank} -> Heap p (suc r) -> Priority
findMin (node p x x1 x2 x3 x4) = p

delMin : {p : Priority} {r : Rank} -> Heap p (suc r) -> Heap p r
delMin {p} {.(_ +N _)} (node p1 x x1 x2 x3 x4) 
    = merge {!   !} {!   !}

minimum : List Priority -> Priority
minimum [] = zero
minimum (x ,- x1) with decLeq x (minimum x1)
... | inl n = x
... | inr n = minimum x1

fromList : (xs : List Priority) -> Heap (minimum xs) {!   !}
fromList = {!   !}