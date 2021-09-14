{-# OPTIONS --no-unicode #-}

module Homework.LeftistHeap.Ranked where

open import Homework.LeftistHeap.Common
open import Lib.Sum
open import Lib.One
open import Lib.Zero
open import Lib.Nat
open import Lib.Eq

-- type index, since we will need it to vary for the different constructors
data Heap : Rank -> Set where
  empty : Heap zero
  node : {l r : Rank} → Priority → Leq r l → Heap l → Heap r → Heap ( suc( l +N r )) 


-- mkNode :
--   {lr rr : Rank} ->
--   Priority -> Heap lr -> Heap rr -> Heap {!  !}
-- mkNode = {!!}

mkNode-lemma : (a b : Nat) → suc(a +N b) == suc(b +N a)
mkNode-lemma a b = ap suc (+N-commut a b) 

mkNode : {lr rr : Rank} -> Priority -> Heap lr -> Heap rr -> Heap (suc (lr +N rr))
mkNode {lr} {rr} x left right with decLeq (lr) (rr)
... | inl rr<=lr rewrite (mkNode-lemma lr rr) = node x rr<=lr right left
... | inr lr<=rr = node x lr<=rr left right

-- ... | inl rr<=lr rewrite (mkNode-lemma lr rr) = node x {!  !} right left

-- mkNode {x1} {x2} x heapL heapR with decLeq x1 x2
-- ... | inl rankx1<=rankx2 = node (suc (rank x2 +N rank x1)) x x2 x1
-- ... | inr rankx2<=rankx1 = node (suc (rank x1 +N rank x2)) x x1 x2

-- x != x1 of type Nat
-- when checking the clause left hand side
-- Homework.LeftistHeap.Ranked.with-32 {x1} {x2} (inl x) x heapL heapR

{-# TERMINATING #-}
merge :
  {lr rr : Rank} ->
  Heap lr -> Heap rr -> Heap (lr +N rr)
merge empty empty = empty
merge (node x x1 x2 x3) empty = node x <> (merge x2 x3) empty
merge empty h2@(node x1 x2 y y1) = h2
merge h1@(node x x3 x4 x5) h2@(node x1 x2 y y1) with decLeq x x1
...| inl x<=x1 = {!   !}
...| inr x1<=x = {!   !}

-- merge : Heap -> Heap -> Heap
-- merge empty h2 = h2
-- merge h1 empty = h1 
-- merge h1@(node rank1 x1 l1 r1) h2@(node rank2 x2 l2 r2) with decLeq x1 x2
-- ... | inl x1<=x2 = mkNode x1 l1 (merge r1 h2)
-- ... | inr x2<=x1 = mkNode x2 l2 (merge r2 h1)


-- Конкретно, имаме "smart constructor" функция (mkNode), която по произволен връх и две пирамиди, 
-- строи нова, за която е изпълнено ранг свойството:

-- mkNode : Priority -> Heap -> Heap -> Heap
-- mkNode x h1 h2 with decLeq (rank h1) (rank h2)
-- ... | inl rankh1<=rankh2
  -- = node (suc (rank h2 +N rank h1)) x h2 h1
-- ... | inr rankh2<=rankh1
  -- = node (suc (rank h1 +N rank h2)) x h1 h2
-- Нея ще използваме за "закърпване" на резултат от рекурсивното викане на сливането.


singleton : {r : Rank} -> Priority -> Heap 1
singleton x = node x <> empty empty
-- singleton : Priority -> Heap
-- singleton x = node 1 x empty empty

insert : {r : Rank} -> Priority -> Heap r -> Heap (suc r)
insert x x1 = merge (singleton x) x1
-- insert : {r : Rank} -> Priority -> Heap r -> Heap r
-- insert x x1 = merge (singleton x) x1
-- insert : Priority -> Heap -> Heap
-- insert x h = merge (singleton x) h


findMin : {r : Rank} -> Heap r -> Priority
findMin {.0} empty = zero
findMin (node x x1 x2 x3) = x

delMin : { r : Rank} -> Heap (suc r) -> Heap r
delMin (node x x1 l r) = merge l r
-- delMin : {r : Rank} -> Heap r -> Heap r
-- delMin empty = empty
-- delMin (node x x1 left right) = merge left right