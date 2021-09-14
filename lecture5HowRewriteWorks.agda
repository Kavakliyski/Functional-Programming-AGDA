module lecture5HowRewriteWorks where

open import Lib.Nat
open import Lib.Eq
open import Lib.Sum
open import Lib.Vec

data Vec (X : Set) : Nat → Set where
    [] : Vec X zero
    _,-_ : {n : Nat} → X → Vec X n → Vec X (suc n)


vTake : {m n : Nat} → {_ : m >= n} → {X : Set} → Vec X m → Vex X n
vTake = ?