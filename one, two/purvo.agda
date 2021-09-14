module purvo where

data Zero : Set where

-- polimorfizum
-- zero == naught
-- E == elim, naughtE {A} zero
naughtE : {A : Set} → Zero → A
naughtE ()

record One : Set where
    constructor <>

data Two : Set where
    ff tt : Two




-- |A + B| == |A| = |B|
-- ot A i B ==> B ili A
data _+_ (A B : Set) : Set where
    inl : A → A + B
    inr : B → A + B

+-swap : {A B : Set} → A + B → B + A
+-swap (inl x) = inr x
+-swap (inr x) = inl x


-- |A * B| == |A| * |B|
-- A*B == naredena dwojka
record _*_ (A B : Set) : Set where
    constructor _,_
    field
        fst : A
        snd : B

_ : One * Two
_ = <> , tt

-- *-swap : {A B : Set} → A * B → B * A
-- *-swap (fst , snd) = snd, fst 



data Nat : Set where
    zero : Nat
    suc : Nat → Nat --wzima estestweno chislo i vrushta estestweno

_ : Nat
_ = zero

_ : Nat
_ = suc (suc (suc zero))

{-# BUILTIN NATURAL Nat #-}

_+N_ : Nat → Nat → Nat
zero +N m = m
suc n +N m = suc (n +N m)




-- kakwi wodowe piene
data DrinkType : Set where
    milk : DrinkType
    beer : DrinkType

data Drink : DrinkType → Set where
    vereq : Drink milk
    ariana : Drink beer
    duvel : Drink beer

Alcohol : DrinkType → Set
Alcohol beer = Nat  -- kolko alkohola sushtestwuwat
Alcohol milk = One --nqmame izbor kakwo da e alkoholnoto sudurjanie

-- alkohol dt ,,,,, drink : Drink dt
-- drink ~ ariana 
-- ariana : Drink beer
-- dt ~ beer
-- Alcohol beer ~ Nat
-- alcohol : {dt : DrinkType} → Drink dt → Alcohol dt
-- alcohol ariana = 0
-- alcohol duvel = 10
-- alcohol vereq = <>

TwoEq : Two → Two → Set
TwoEq ff ff = One 
TwoEq ff tt = Zero
TwoEq tt ff = Zero
TwoEq tt tt = One

NatEq : Nat → Nat → Set
NatEq zero zero = One
NatEq zero (suc m) = Zero
NatEq (suc n) zero = Zero
NatEq (suc n) (suc m) = NatEq n m



data _==_ {A : Set} : A → A → Set where
    refl : (x : A) → x == x

infix 10 _==_

_ : zero == zero
_ = refl zero


-- _ : 2 +N  2 == 4
-- _ = {!   !}

zeroIsNotOne : zero == suc zero -> Zero
zeroIsNotOne ()

bla : {n : Nat} -> n == 2 -> n +N 2 == 4
bla (refl _) = refl 4

+N-left-zero : (n : Nat) -> zero +N n == n
+N-left-zero n = refl n

-- stuckness explanation
-- ap time

-- n ~ m
-- suc n ~ suc m
-- функционалност
ap : {A B : Set} {x y : A} -> (f : A -> B) -> x == y -> f x == f y
ap f (refl x) = refl (f x)


+N-right-zero : (n : Nat) → n +N 0 == n 
+N-right-zero zero = refl zero
+N-right-zero (suc n') = ap suc (+N-right-zero n')

















