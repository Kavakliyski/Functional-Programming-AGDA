{-# OPTIONS --no-unicode #-}

module three,four.FourStart where

open import Lib.List
open import Lib.Eq
open import Lib.Nat
open import Lib.Sum
open import Lib.One
open import Lib.Zero
open import Lib.Sigma

-- describe modules
-- show example with open

module Listy (A : Set) where
  x : Nat
  x = zero

  id' : A -> A
  id' y = y

  bla : Nat -> Set
  bla n = A

-- z : Nat
-- z = {!id'!}

-- show bst constructions
-- write Bound
-- write LeqBound
-- write BST
-- explain "pushing down constraints"
-- examples for bst
-- show tree diagram

LeqNat : Nat -> Nat -> Set
LeqNat zero m = One
LeqNat (suc n) zero = Zero
LeqNat (suc n) (suc m) = LeqNat n m

_ : 3 <= 5
_ = osuc (osuc (osuc ozero))

_ : LeqNat 3 5
_ = <>

decLeqNat : (n m : Nat) -> LeqNat n m + LeqNat m n
decLeqNat zero m = inl <>
decLeqNat (suc n) zero = inr <>
decLeqNat (suc n) (suc m) = decLeqNat n m

<=-LeqNat : {n m : Nat} -> n <= m -> LeqNat n m
<=-LeqNat ozero = <>
<=-LeqNat (osuc p) = <=-LeqNat p


module
  Sorting
    (Key : Set)
    (Leq : Key -> Key -> Set)
    (_<=?_ : (x y : Key) -> Leq x y + Leq y x)
  where

  data Bound : Set where
    -inf : Bound
    inKey : Key -> Bound
    +inf : Bound

  LeqBound : Bound -> Bound -> Set
  LeqBound -inf y = One
  LeqBound x +inf = One
  LeqBound (inKey x) (inKey y) = Leq x y
  LeqBound _ _ = Zero

  data BST (lo hi : Bound) : Set where
    empty : LeqBound lo hi -> BST lo hi

    node :
      (k : Key) ->
      (left : BST lo (inKey k)) ->
      (right : BST (inKey k) hi) ->
      BST lo hi

  -- you can use _<=?_ to compare two values
  insert :
    {lo hi : Bound} (k : Key) ->
    LeqBound lo (inKey k) -> LeqBound (inKey k) hi ->
    BST lo hi -> BST lo hi

  insert k x1 x2 (empty x) = node k (empty x1) (empty x2)
  insert k lowk khigh (node root left right) with k <=? root  
  ... | inl x = node root       (insert k  lowk x left) right
  ... | inr x = node root       left (insert k x khigh right)

  makeTree : List Key -> BST -inf +inf
  makeTree [] = empty <>
  makeTree (x ,- x1) = insert x <> <> (makeTree x1)

  -- use the same idea as in BST to define "ordered lists"
  -- be careful about what constraints you need in your recursive case!
  data OList (lo hi : Bound) : Set where
    lempty : LeqBound lo hi → OList lo hi
    icons : (k : Key) -> LeqBound lo (inKey k) -> OList (inKey k) hi -> OList lo hi
  -- append ordered lists
  -- note that we require a key to "bridge" the two lists
  -- try to implement
  -- append : {lo mid hi : Bound} -> OList lo mid -> OList mid hi -> OList lo hi
  -- and see where you get stuck

  appendKeyed : {lo hi : Bound} -> (k : Key) -> OList lo (inKey k) -> OList (inKey k) hi -> OList lo hi
  appendKeyed k (lempty x) x1 = icons k x x1
  appendKeyed k (icons k1 x x2) x1 = icons k1 x (appendKeyed k x2 x1)

  flatten : {lo hi : Bound} -> BST lo hi -> OList lo hi
  flatten (empty x) = lempty x
  flatten (node k x x1) = appendKeyed k (flatten x) (flatten x1)

  sort : List Key -> OList -inf +inf
  sort xs = flatten (makeTree xs)

--          2
--       1  .  3
--     <=.<=.<=.<=
--       .  .  .
-- -inf<=1<=2<=3<=+inf

open Sorting Nat LeqNat decLeqNat

one : BST -inf (inKey 2)
one = node 1 (empty <>) (empty <>)

three : BST (inKey 2) +inf
three = node 3 (empty <>) (empty <>)

two : BST -inf +inf
two = node 2 one three

Dec : (A : Set) -> Set
Dec A = (A -> Zero) + A


-- used a module to introduce global vars
-- in here, you can compare values for equality with _==?_
-- in all proofs for functions defined with a `with`
-- you're most likely going to need to do another with
-- because your proof will be stuck on the result of the with in the original function def
module listy {A : Set} {_==?_ : (x y : A) -> Dec (x == y)} where
  infix 10 _In_
  data _In_ (x : A) : List A -> Set where
    here : {xs : List A} -> x In (x ,- xs)
    there : {y : A} {xs : List A} -> x In xs -> x In (y ,- xs)

  +L-monoL-In : {y : A} {ys : List A} -> (xs : List A) -> y In ys -> y In xs +L ys
  +L-monoL-In [] x = x
  +L-monoL-In (x1 ,- xs) x = there (+L-monoL-In xs x)

  +L-splits-In : {x : A} (xs ys : List A) -> x In xs +L ys -> x In xs + x In ys
  +L-splits-In [] ys x = inr x
  +L-splits-In (x1 ,- xs) ys here = inl here
  +L-splits-In (x1 ,- xs) ys (there p) with +L-splits-In (xs) (ys) (p)
  ... | inl q = inl (there q)
  ... | inr q = inr q


  notIn[] : {x : A} -> x In [] -> Zero
  notIn[] () 


  nowhere : {x y : A} {ys : List A} -> (x == y -> Zero) -> (x In ys -> Zero) -> x In y ,- ys -> Zero
  nowhere x x1 here = x refl
  nowhere x x1 (there x2) = x1 x2

  -- if there is one, return the first x in the list
  find : (x : A) (xs : List A) -> Dec (x In xs)
  find x [] = inl notIn[]
  find x (x1 ,- xs) with x ==? x1 
  ... | inr refl = inr here
  ... | inl x!=x1 with find x xs
  ... | inr x!=xs = inr (there x!=xs)  
  ... | inl x==xs = inl (nowhere x!=x1 x==xs)

  -- delete all the occurrences of x in the list
  remove : (x : A) -> (xs : List A) -> List A
  remove x [] = []
  remove x (x1 ,- xs) with x ==? x1
  ... | inr x==x1 = remove x xs
  ... | inl x!=x1 = x1 ,- remove x xs


  remove-removes : (xs : List A) -> (x : A) -> x In remove x xs -> Zero
  remove-removes (x2 ,- xs) x x1 with x ==? x2
  ... | inr x==x2 = remove-removes xs x x1
  remove-removes (x2 ,- xs) .x2 here | inl x!=x2 = x!=x2 refl
  remove-removes (x2 ,- xs) x (there x1) | inl x!=x2 = remove-removes xs x x1
  
  



  remove-keeps : (xs : List A) (y : A) -> y In xs -> (x : A) -> (x == y -> Zero) -> y In remove x xs
  remove-keeps = {!!}
  -- xs Sub ys - xs is a subsequence of ys
  -- [] Sub []
  -- 5 ,- [] Sub 5 ,- []
  -- 3 ,- 5 ,- [] Sub 3 ,- 5 ,- []
  -- 3 ,- 5 ,- [] Sub 3 ,- 5 ,- 4 ,- []
  -- 3 ,- 5 ,- [] Sub 3 ,- 4 ,- 5 ,- []
{-
  data _Sub_ : List A -> List A -> Set where
    s[] : [] Sub []
    s-cons : {x : A} {xs ys : List A} -> xs Sub ys -> (x ,- xs) Sub (x ,- ys)
    s-skip : {x : A} {xs ys : List A} -> xs Sub ys -> xs Sub (x ,- ys)
  infix 10 _Sub_
  s[]-all : (xs : List A) -> [] Sub xs
  s[]-all = {!!}
  Sub-refl : (xs : List A) -> xs Sub xs
  Sub-refl = {!!}
  -- try to make the definition "as lazy" as possible - meaning pattern matching on as few things as possible
  -- this will affect your proof for Sub-trans-assoc
  Sub-trans : {xs ys zs : List A} -> xs Sub ys -> ys Sub zs -> xs Sub zs
  Sub-trans = {!!}
  +L-monoL-Sub : (xs ys : List A) -> xs Sub (xs +L ys)
  +L-monoL-Sub = {!!}
  +L-monoR-Sub : (xs ys : List A) -> xs Sub (ys +L xs)
  +L-monoR-Sub = {!!}
  Sub-all-In : {xs ys : List A} -> xs Sub ys -> {x : A} -> x In xs -> x In ys
  Sub-all-In = {!!}
  remove-Sub : (x : A) (xs : List A) -> remove x xs Sub xs
  remove-Sub = {!!}
  -- might need to make an implicit arg explicit in one of the cases
  remove-preserves-Sub : {xs ys : List A} (x : A) -> xs Sub ys -> remove x xs Sub ys
  remove-preserves-Sub = {!!}
  ,-Sub-remove : {xs ys : List A} (x : A) -> xs Sub x ,- ys -> remove x xs Sub ys
  ,-Sub-remove = {!!}
  Sub-trans-assoc :
    {xs ys zs vs : List A} (sub1 : xs Sub ys) (sub2 : ys Sub zs) (sub3 : zs Sub vs) ->
    Sub-trans (Sub-trans sub1 sub2) sub3 == Sub-trans sub1 (Sub-trans sub2 sub3)
  Sub-trans-assoc = {!!}


decNatEq : (n m : Nat) -> Dec (n == m)
decNatEq = {!!}
open listy {Nat} {decNatEq}
_ : 3 In 3 ,- 5 ,- []
_ = here
_ : 5 In 3 ,- 5 ,- []
_ = there here
5notIn[] : 5 In [] -> Zero
5notIn[] ()
5notIn3 : 5 In 3 ,- [] -> Zero
5notIn3 (there ())
_ : [] Sub []
_ = s[]
_ : 5 ,- [] Sub 5 ,- []
_ = s-cons s[]
_ : 3 ,- 5 ,- [] Sub 3 ,- 5 ,- []
_ = s-cons (s-cons s[])
_ : 3 ,- 5 ,- [] Sub 3 ,- 5 ,- 4 ,- []
_ = s-cons (s-cons (s-skip s[]))
_ : 3 ,- 5 ,- [] Sub 3 ,- 4 ,- 5 ,- []
_ = s-cons (s-skip (s-cons s[]))
32notSub23 : 3 ,- 2 ,- [] Sub 2 ,- 3 ,- [] -> Zero
32notSub23 (s-skip (s-cons ()))
32notSub23 (s-skip (s-skip ()))
332notSub32 : 3 ,- 3 ,- 2 ,- [] Sub 3 ,- 2 ,- [] -> Zero
332notSub32 (listy.s-cons (listy.s-skip ()))
332notSub32 (listy.s-skip (listy.s-skip ()))
-}



-- plusnat : Nat → Nat → Nat
-- plusnat zero m = m
-- plusnat n zero = n
-- plusnat (suc n) m = suc (plusnat n m )

-- plusnat-commut : (n m : Nat) → plusnat n m == plusnat m n 
-- plusnat-commut zero m = {!   !}
-- plusnat-commut (suc n) m = {!   !}

-- asd : Nat → Nat
-- asd n with decLeqNat n 5
-- ... | inl x = 5
-- ... | inr x = n

-- pasd : (n : Nat) → LeqNat 5 n → asd n == n 
-- pasd n x with decLeqNat n 5 
-- ... | inl x1 = {!   !}
-- ... | inr x1 = {!   !}

-- bla : (n : Nat) → n == 10 → 0 == n
