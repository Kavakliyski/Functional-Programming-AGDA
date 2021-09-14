{-# OPTIONS --no-unicode #-}

module Homework.LeftistHeap.Ordered where

open import Lib.Sum
open import Lib.One
open import Homework.LeftistHeap.Common
open import Lib.Nat
-- Тук се очаква да направите Heap типа наподобяващ този от Untyped.agda,
--  но така че по конструкция да е изпълнено свойството за наредбата.

-- parametrised by the lower bound of the heap
-- Дайте пример за Heap, който изпълнява и свойството за ранга.
-- Дайте пример за Heap, който има грешен ранг.
-- Дайте пример за Heap, който не изпълнява свойството за ранга.

data Heap (lower : Priority) : Set where
  empty : Heap lower
  node : (p : Priority) → Rank → Leq lower p → Heap p → Heap p → Heap lower
  -- node : (p : Priority) → Rank → p >= lower → Heap p → Heap p → Heap lower

-- Първо, нека си направим удобна функция за изваждане на ранга на дърво.
rank : {lower : Priority} -> Heap lower -> Rank
rank empty = zero
rank (node p x x1 l r) = suc (rank l +N rank r)


mkNode :
  {lower : Priority} (x : Priority) -> Leq lower x -> Heap x -> Heap x -> Heap lower
mkNode {lower} x p left right with decLeq (rank left) (rank right)
... | inl rankleft<=rankright = node x ((suc (rank right +N rank left))) p right left
... | inr rankright<=rankleft = node x ((suc (rank left +N rank right))) p left right


-- mkNode : Priority -> Heap -> Heap -> Heap
-- mkNode x h1 h2 with decLeq (rank h1) (rank h2)
-- ... | inl rankh1<=rankh2 = node (suc (rank h2 +N rank h1)) x h2 h1
-- ... | inr rankh2<=rankh1 = node (suc (rank h1 +N rank h2)) x h1 h2

{-# TERMINATING #-}
merge : {lower : Priority} -> Heap lower -> Heap lower -> Heap lower
merge empty empty = empty
merge (node p x1 x2 h1 h2) empty = (node p x1 x2 h1 h2)
merge empty (node p x1 x2 h2 h3) = (node p x1 x2 h2 h3)
merge h1@(node p1 Rank1 leq1 l1 r1) h2@(node p Rank2 leq2 l2 r2) with decLeq p1 p
... | inl p1<=p = mkNode p leq2 {!   !} (merge {!   !} {!   !})
... | inr p<=p1 = {!   !}


-- merge : Heap -> Heap -> Heap
-- merge empty h2 = h2
-- merge h1 empty = h1
-- merge h1@(node rank1 x1 l1 r1) h2@(node rank2 x2 l2 r2) with decLeq x1 x2
-- ... | inl x1<=x2
  -- = mkNode x1 l1 (merge r1 h2)
-- ... | inr x2<=x1
  -- = mkNode x2 l2 (merge r2 h1)

-- известен още като единица, е набор с точно един елемент. Например, 
-- множеството {null} е сингъл, 
-- съдържащ елемента null. Терминът се използва и за 1-кратък.
singleton : {lower : Priority} (x : Priority) -> Leq lower x -> Heap lower
singleton {lower} x x1 = mkNode x x1 empty empty
-- singleton x x1 = node x 1 x1 empty empty

-- singleton : Priority -> Heap
-- singleton x = node 1 x empty empty

-- Идеята там вече сте я виждали - разширяваме долната граница на Heap-а ни, 
-- подобно на това което правим при Fin-ове, например. 
-- Освен weakenHeap, може да ви се наложи да доказвате и разни свойства за min и Leq.
weakenHeap : (n m : Priority) -> Leq n m -> Heap m -> Heap n
weakenHeap n m x empty = empty
weakenHeap n m x (node p x1 x2 left right) 
 = mkNode n (Leq-refl n) 
    (weakenHeap n p (Leq-trans n x1 p {!  !} {!   !}) left) 
    (weakenHeap n p (Leq-trans n x1 p {!   !} {!   !}) right)

-- weakenHeap ще ни е нужно за insert
insert : {lower : Priority} (x : Priority) -> Heap lower -> Heap x
insert {lower} x heap with decLeq lower x
... | inl x1 = merge (singleton x (Leq-refl x)) (weakenHeap x x (Leq-refl x) empty) --!
... | inr x1 = merge (singleton x ((Leq-refl x))) (weakenHeap x lower x1 heap)

-- insert : Priority -> Heap -> Heap
-- insert x h = merge (singleton x) h

findMin : {lower : Priority} -> Heap lower -> Maybe Priority
findMin empty = no
findMin (node p x x1 left right) = yes p


delMin : {lower : Priority} -> Heap lower -> Maybe (Heap lower)
delMin empty = no
delMin {lower} (node p x x1 left right) 
  = yes (merge 
      (weakenHeap lower p x1 left) 
      (weakenHeap lower p x1 right))

-- delMin : Heap -> Maybe Heap
-- delMin empty = no
-- delMin (node rank x l r) = yes (merge l r)