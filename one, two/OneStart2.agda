{-# OPTIONS --no-unicode #-}

module OneStart2 where

data Zero : Set where

naughtE : {A : Set} → Zero → A
naughtE ()


record One : Set where
    constructor <>


data Two : Set where
    ff tt : Two


data _+_ (A B : Set) : Set where
    inl : A → A + B 
    inr : B → A + B 
-- |A + B| == |A| + |B|
-- data Either a b = Left a | Right b



infixr 8 _+_

-- swap :: Either a b -> Either b a
-- A || B -> B || A
+-swap : {A B : Set} → A + B → B + A 
+-swap (inl x) = inr x 
+-swap (inr x) = inl x  


-- (a , b)
-- a * b
-- count of members is product of both
-- cartesian product
-- |A * B| == |A| * |B|
record _*_ (A B : Set) : Set where
    constructor _,_ 
    field
        fst : A 
        snd : B 


infixr 9 _*_ 

open _*_ public

*-swap : {A B : Set} → A * B → B * A
*-swap (fst , snd) = snd , fst

data Nat : Set where
    zero : Nat
    suc : Nat → Nat

_ : Nat
_ = zero
_ : Nat
_ = suc (suc(suc zero))


{-# BUILTIN NATURAL Nat #-}


_ : Nat
_ = 4 -- suc (suc (suc (suc zero)))
-- _ = suc (suc (suc (suc zero)))

_+N_ : Nat → Nat → Nat
zero +N m = m 
suc n +N m = suc (n +N m) 
-- (1 + n) + m ==
-- 1 + (n + m)


infixr 15 _+N_ 
-- drinktypes example for type indices
-- and alcohol content dep ret type
-- data _+_ (A B : Set) : Set where
--   inl : A -> A + B
--   inr : B -> A + B
data DrinkType : Set where
    milk : DrinkType
    beer : DrinkType

data Drink : DrinkType -> Set where
    верея : Drink milk
    ariana : Drink beer
    duvel : Drink beer


Alcohol : DrinkType -> Set
Alcohol beer = Nat -- колко алкохол има, като число
Alcohol milk = One -- само една възможност, която означава "няма алкохол"


alcohol : {dt : DrinkType} -> Drink dt -> Alcohol dt
alcohol ariana = 0
alcohol duvel = 10
alcohol верея = <>



data _==_ {A : Set} : A -> A -> Set where
  refl : (x : A) -> x == x

infix 10 _==_

_ : zero == zero
_ = refl zero

zeroIsNotOne : zero == suc zero -> Zero
zeroIsNotOne ()


ble : {n : Nat} → n == 2 → n +N 2 == 4
ble (refl _ ) = refl 4


+N-left-zero : (n : Nat) → zero +N n == n
+N-left-zero n = refl n 


-- функционалност
ap : {A B : Set} {x y : A} -> (f : A -> B) -> x == y -> f x == f y
ap f (refl x) = refl (f x)



+-assoc : {A B C : Set} -> (A + B) + C → A + (B + C)
+-assoc (inl (inl a)) = inl a
+-assoc (inl (inr b)) = inr (inl b)
+-assoc (inr c)       = inr (inr c)

+-assoc' : {A B C : Set} -> A + (B + C) -> (A + B) + C
+-assoc' (inl a)       = inl (inl a)
+-assoc' (inr (inl b)) = inl (inr b)
+-assoc' (inr (inr c)) = inr c

*-assoc : {A B C : Set} → A * (B * C) → (A * B) * C 
*-assoc (a , (b , c)) = (a , b) , c



-- *-swap : {A B : Set} -> A * B -> B * A
-- *-swap (fst , snd) = snd , fst
*-distrib-+ : {A B C : Set} ->  A * (B + C)     ->   A * B + A * C
*-distrib-+ (fst , inl x) = inl (fst , x)
*-distrib-+ (fst , inr x) = inr (fst , x)


==-symm : {X : Set} {x y : X} -> x == y -> y == x
==-symm (refl _) = refl _


-- data _==_ {A : Set} : A -> A -> Set where
--   refl : (x : A) -> x == x
==-trans : {X : Set} {x y z : X} -> x == y -> y == z -> x == z
==-trans (refl x) (refl _) = refl x


+N-right-suc : (n m : Nat) -> suc (n +N m) == n +N suc m
+N-right-suc zero m = refl (suc m)
+N-right-suc (suc n) m = ap suc (+N-right-suc n m)


+N-right-zero : (n : Nat) → n +N 0 == n 
+N-right-zero zero = refl zero
+N-right-zero (suc n') = ap suc (+N-right-zero n')


-- you'll need ==-symm, ==-trans, +N-right-zero and +N-right-suc here

-- _+N_ : Nat → Nat → Nat
-- zero +N m = m 
-- suc n +N m = suc (n +N m) 

+N-commut : (n m : Nat) -> n +N m == m +N n
+N-commut zero m = ==-symm (+N-right-zero m)
+N-commut (suc n) m = ==-trans (ap suc (+N-commut n m)) (+N-right-suc m n)


data List (a : Set) : Set where
    [] : List a 
    _,-_ : a → List a → List a 

infixr 11 _,-_

-- concatenate tow list
_+L_ : {A : Set} -> List A -> List A -> List A
[] +L ys = ys
(x ,- xs) +L ys = x ,- (xs +L ys)
 
_ : (3 ,- 5 ,- []) +L  (4 ,- 2 ,- []) == 3 ,- 5 ,- 4 ,- 2 ,- []
_ = refl _
_ : (<> ,- []) +L  (<> ,- []) == <> ,- <> ,- []
_ = refl _

infixr 12 _+L_

+L-assoc : {A : Set} (xs ys zs : List A) -> (xs +L ys) +L zs == xs +L ys +L zs
+L-assoc [] ys zs = refl (ys +L zs)
+L-assoc (x ,- xs) ys zs = ap (x ,-_) (+L-assoc xs ys zs)

+L-right-id : {A : Set} (xs : List A) -> xs +L [] == xs
+L-right-id [] = refl []
+L-right-id (x ,- xs) = ap (x ,-_) (+L-right-id xs)


-- calculate the length of a list
length : {A : Set} -> List A -> Nat
length [] = zero
length (_ ,- xs) = suc (length xs)
_ : length (<> ,- []) == 1
_ = refl _
_ : length (0 ,- 5 ,- 8 ,- 6 ,- [] ) == 4
_ = refl _


-- create a list of only the given element, with length the given Nat
replicate : {A : Set} -> Nat -> A -> List A
replicate zero _ = []
replicate (suc n) x = x ,- replicate n x
_ : replicate 2 <> == <> ,- <> ,- []
_ = refl _
_ : replicate 3 5 == 5 ,- 5 ,- 5 ,- []
_ = refl _
_ : replicate 9 5 == 5 ,- 5 ,- 5 ,- 5 ,- 5 ,- 5 ,- 5 ,- 5 ,- 5 ,- []
_ = refl _


-- prove that the length of the replicated list is the original input number to replicate
length-replicate : {A : Set} {x : A} (n : Nat) -> length (replicate n x) == n
length-replicate zero = refl zero
length-replicate (suc n) = ap suc (length-replicate n)


-- define All to calculate the type which  is inhabited when
-- P is true for all the elements of the given list
-- All : {X : Set} (P : X -> Set) -> List X -> Set
-- All P [] = {!   !}
-- All P (x ,- x1) = {!   !}
-- prove that 




-- ThreeStart 

data _<=_ : Nat -> Nat -> Set where
  ozero : {n : Nat} -> 0 <= n
  osuc : {n m : Nat} -> n <= m -> suc n <= suc m

infix 9 _<=_
-- -- maybe send link on actual rewrite
-- +N-right-zero' : (n : Nat) -> n +N 0 == n
-- +N-right-zero' zero = refl zero
-- +N-right-zero' (suc n) rewrite +N-right-zero' n = refl _

<=-refl : (n : Nat) -> n <= n
<=-refl zero = ozero
<=-refl (suc n) = osuc (<=-refl n)


<=-antisym : {n m : Nat} -> n <= m -> m <= n -> n == m
<=-antisym ozero ozero = refl zero
<=-antisym (osuc x) (osuc xs) = ap suc (<=-antisym x xs)


<=-mono-left-+ : {n m : Nat} (k : Nat) -> n <= m -> k +N n <= k +N m
<=-mono-left-+ zero x = x
<=-mono-left-+ (suc k) x = osuc (<=-mono-left-+ k x)


-- you might need a lemma here
{-# BUILTIN EQUALITY _==_ #-}
-- +N-right-suc : (n m : Nat) -> suc (n +N m) == n +N suc m
-- +N-right-suc zero m = refl (suc m)
-- +N-right-suc (suc n) m = ap suc (+N-right-suc n m)
<=-lemma : (k m : Nat) → k <= m +N k
<=-lemma zero m = ozero
<=-lemma (suc k) m rewrite ==-symm (+N-right-suc m k) = osuc (<=-lemma k m)

<=-mono-right-+ : {n m : Nat} (k : Nat) -> n <= m -> n +N k <= m +N k
<=-mono-right-+ {n} {m} k ozero = <=-lemma k m
<=-mono-right-+ k (osuc x) = osuc (<=-mono-right-+ k x)


-- multiplication using repeated addition
_*N_ : Nat -> Nat -> Nat
zero *N m = zero
suc n *N m = m +N n *N m
infixr 40 _*N_

-- EXERCISE: multiplication right identity
*N-right-id : (n : Nat) -> n *N 1 == n
*N-right-id zero = refl zero
*N-right-id (suc n) = ap suc (*N-right-id n)


_=[]_ : {A : Set} {y : A} -> (x : A) -> x == y -> x == y
x =[] (refl _) = refl _
infixr 1 _=[]_

_QED : {A : Set} -> (x : A) -> x == x
x QED = refl x
infix 3 _QED
-- END OF UTILS


-- multiplication distributes over addition
-- *N-distrib-+N : (n m k : Nat) -> (n +N m) *N k == n *N k +N m *N k
-- *N-distrib-+N zero m zero = refl (m *N zero)
-- *N-distrib-+N (suc n) m zero = *N-distrib-+N n m zero
-- *N-distrib-+N n m (suc k) = {!   !}

-- use *N-distrib-+N
-- *N-assoc : (n m k : Nat) -> (n *N m) *N k == n *N (m *N k)
-- *N-assoc = {!  !}




