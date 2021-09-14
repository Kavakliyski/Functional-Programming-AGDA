{-# OPTIONS --no-unicode #-}

module Homework.Bin where

import Lib.Nat as Nat
open Nat using (Nat; _+N_)
open import Lib.Eq
open import Lib.Sigma
open import Lib.Zero
open import Lib.One
open import Lib.Sum


data Bin : Set where
  end : Bin           -- 0
  _O : Bin -> Bin     -- 2n
  _I : Bin -> Bin     -- 2n+1

infixr 12 _O
infixr 12 _I

_ : Bin
_ = end I O I

-- Successor.
suc : Bin -> Bin
suc end = end I 
suc (x O) = x I
suc (x I) = (suc x) O


_ : suc end == end I
_ = refl

_ : suc (end I I) == end I O O
_ = refl


toNat : Bin -> Nat
toNat end = Nat.zero
toNat (x O) = toNat x +N toNat x
toNat (x I) = Nat.suc (toNat x +N toNat x)  

_ : toNat (end I I I) == 7
_ = refl

_ : toNat (end I I O) == 6
_ = refl

_ : toNat (end O) == 0
_ = refl

_ : toNat end == 0
_ = refl


fromNat : Nat -> Bin
fromNat Nat.zero = end
fromNat (Nat.suc x) = suc (fromNat x)

_ : fromNat 0 == end
_ = refl

_ : fromNat 1 == end I
_ = refl 

_ : fromNat 8 == end I O O O
_ = refl


toNat-suc : (b : Bin) -> toNat (suc b) == Nat.suc (toNat b)
toNat-suc end = refl
toNat-suc (b O) = refl
toNat-suc (b I) rewrite toNat-suc b | Nat.+N-right-suc (toNat b) (toNat b) = refl       --Nat.suc (Nat.suc (toNat b +N toNat b))

to-from-id : (n : Nat) -> toNat (fromNat n) == n
to-from-id Nat.zero = refl
to-from-id (Nat.suc n) rewrite toNat-suc (fromNat n) | to-from-id n  = refl


data LeadingOne : Bin -> Set where
  endI : LeadingOne (end I)
  _O : {b : Bin} -> LeadingOne b -> LeadingOne (b O)
  _I : {b : Bin} -> LeadingOne b -> LeadingOne (b I)

data Can : Bin -> Set where
  end : Can end
  leadingOne : {b : Bin} -> LeadingOne b -> Can b


suc-LeadingOne : (b : Bin) -> LeadingOne b -> LeadingOne (suc b)
suc-LeadingOne .(end I) endI = endI O
suc-LeadingOne .(_ O) (x O) = x I
suc-LeadingOne .(b I) (_I {b} x) = suc-LeadingOne b x O

suc-Can : (b : Bin) -> Can b -> Can (suc b)
suc-Can .end end = leadingOne endI
suc-Can (b O) (leadingOne (x O)) = leadingOne (x I)
suc-Can (b I) (leadingOne x) = leadingOne (suc-LeadingOne (b I) x)

fromNat-Can : (n : Nat) -> Can (fromNat n)
fromNat-Can Nat.zero = end
fromNat-Can (Nat.suc n) = suc-Can (fromNat n) (fromNat-Can n)


_+B_ : Bin -> Bin -> Bin
end +B y = y
x O +B end = x O
x O +B y O = (x +B y) O
x O +B y I = (x +B y) I
x I +B end = x I
x I +B y O = (x +B y) I
x I +B y I = suc(x +B y) O

infixr 11 _+B_

_ : end +B end I I I I == end I I I I
_ = refl

_ : end I O O +B end == end I O O
_ = refl

_ : end I I +B end I I I I == end I O O I O
_ = refl

_ : end I I I +B end I O I == end I I O O
_ = refl

--!
-- +B-right-end : (b : Bin) -> b +B end == b
-- +B-right-end end = refl
-- +B-right-end (b O) = Nat.suc (+B-right-end (b I))                   -- b O +B end == b O
-- +B-right-end (b I) = +B-right-end (b O)                   -- b I +B end == b I
-- +B-right-end (b O) = Nat.suc (+B-right-end (b O))

+B-right-end : (b : Bin) -> b +B end == b
+B-right-end end = refl
+B-right-end (b O) = refl
+B-right-end (b I) = refl


-- Можем да "изкарваме suc навън" от лявата страна на _+B_.
+B-left-suc : (b v : Bin) -> suc b +B v == suc (b +B v)
+B-left-suc end end = refl
+B-left-suc end (v O) = refl
+B-left-suc end (v I) = refl
+B-left-suc (b O) end = refl
+B-left-suc (b O) (v O) = refl
+B-left-suc (b O) (v I) = refl
+B-left-suc (b I) end = refl
+B-left-suc (b I) (v O) = ap _O (+B-left-suc b v)
+B-left-suc (b I) (v I) = ap _I (+B-left-suc b v)

-- +B-left-suc end v = refl
-- +B-left-suc (b O) v = refl
-- +B-left-suc (b I) v = ?


-- Можем да "изкарваме suc навън" от дясната страна на _+B_.
+B-right-suc : (b v : Bin) -> b +B suc v == suc (b +B v)
+B-right-suc end v = refl
+B-right-suc (b O) end = ap _I (+B-right-end b)
+B-right-suc (b O) (v O) = refl
+B-right-suc (b O) (v I) = ap _O (+B-right-suc b v)
+B-right-suc (b I) end = ap _O (ap suc (+B-right-end b))
+B-right-suc (b I) (v O) = refl
+B-right-suc (b I) (v I) = ap _I (+B-right-suc b v)


-- fromNat "комутира" в отношение с _+N_ и _+B_.
fromNat-+N-+B-commutes : (n m : Nat) -> fromNat (n +N m) == fromNat n +B fromNat m
fromNat-+N-+B-commutes Nat.zero m = refl
fromNat-+N-+B-commutes (Nat.suc n) Nat.zero 
  rewrite Nat.+N-right-zero n 
  rewrite +B-right-end  (suc (fromNat n)) 
    = refl  
fromNat-+N-+B-commutes (Nat.suc n) (Nat.suc m) 
  rewrite Nat.+N-right-suc n m 
  rewrite +B-right-suc (suc (fromNat n)) (fromNat m)
  rewrite +B-left-suc (fromNat n) (fromNat m)
    = ap suc (ap suc (fromNat-+N-+B-commutes n m))


-- Събирането на двоично число, с водеща единица, два пъти със себе си, 
-- е същото като да "изместим наляво" (bitwise shift) числото.
+B-same-shift : (b : Bin) -> LeadingOne b -> b +B b == b O
+B-same-shift (b O) (leadingOneB O) = ap _O (+B-same-shift b leadingOneB)
+B-same-shift (.end I) endI = refl
+B-same-shift (b I) (leadingOneB I) rewrite +B-same-shift b leadingOneB  = refl


-- Ако конвертираме от канонично двоично число в пеаново и обратно, 
-- получаваме оригиналното двоично число.
from-to-id-Can : (b : Bin) -> Can b -> fromNat (toNat b) == b
from-to-id-Can end end = refl
from-to-id-Can (b O) (leadingOne x) 
  rewrite fromNat-+N-+B-commutes (toNat b) (toNat b) 
  rewrite +B-same-shift (fromNat (toNat b)) {!   !}
    =  {!  !}
from-to-id-Can (b I) (leadingOne x) 
  rewrite ap suc (fromNat-+N-+B-commutes (toNat b) (toNat b))
    = {!  !}