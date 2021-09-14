-- TODO discuss
{-# OPTIONS --type-in-type #-}
{-# OPTIONS --no-unicode #-}

module SevenStart where

open import Lib.Eq
open import Lib.List
open import Lib.Vec
open import Lib.Nat
open import Lib.One
open import Lib.Two
open import Lib.Zero
open import Lib.Sigma

record Category : Set where
  field
    -- data
    Obj : Set
    _~>_ : Obj -> Obj -> Set

    -- operations
    id~> : (x : Obj) -> x ~> x
        -- (f ∘ g  ∘ h) x == f(g(h(x)))
        -- (h >~> g >~> f) x == f(g(h(x)))
    _>~>_ : {S T R : Obj} -> S ~> T -> T ~> R -> S ~> R

    -- laws
    left-id :
      {S T : Obj} (f : S ~> T) ->
      id~> S >~> f == f
    right-id :
      {S T : Obj} (f : S ~> T) ->
      f >~> id~> T == f
    assoc :
      {S T R Q : Obj}
      (f : S ~> T) (g : T ~> R) (h : R ~> Q) ->
      (f >~> g) >~> h == f >~> (g >~> h)

open Category public

AGDA : Category
AGDA = 
    record
    { Obj = Set
    ; _~>_ = \ S T -> S → T
    ; id~> = λ S x → x
    ; _>~>_ = \ f g x -> g (f x)
    ; left-id = \ f -> refl
    ; right-id = \ f -> refl
    ; assoc = \ f g h -> refl
    }


-- * --> *
--  \    |
--   \   |
--    \  |
--     \ |
--      \|
--       v
--       *
module Three where
  -- One + One + One
  data Three : Set where
    -- zero : Three
    -- one : Three
    -- two : Three
    zero one two : Three

  data Arrow : Three -> Three -> Set where
    idArr : (x : Three) -> Arrow x x
    zero-one : Arrow zero one
    one-two : Arrow one two
    zero-two : Arrow zero two

  THREE : Category
  THREE = 
        record
        { Obj = Set
        ; _~>_ = {!   !}
        ; id~> = {!   !}
        ; _>~>_ = {!   !}
        ; left-id = {!   !}
        ; right-id = {!   !}
        ; assoc = {!   !}
        }


-- TODO: use a record here!
-- SET : Category
-- SET = {!!}
-- all of the info is in the objects
record Preorder : Set where
  field
    cat : Category
    one-arrow : {S T : Obj cat} (f g : _~>_ cat S T) -> f == g
-- TODO: show copatterns here
-- https://agda.readthedocs.io/en/v2.6.1.3/language/copatterns.html

<=-unique : {n m : Nat} (p q : n <= m) -> p == q
<=-unique ozero ozero = refl
<=-unique (osuc p) (osuc q) = ap osuc (<=-unique p q)

<=-Cat : Category
Obj <=-Cat = Nat
_~>_ <=-Cat = _<=_                  -- Nat -> Nat -> Set
id~> <=-Cat = <=-refl               -- (x : Nat) -> x <= x
_>~>_ <=-Cat = <=-trans              -- {S T R : Nat} -> S <= T -> T <= R -> S <= R
left-id <=-Cat {n} {m} p = <=-unique (<=-trans (<=-refl n) p) p
right-id <=-Cat {S} {T} f = <=-unique (<=-trans f (<=-refl T)) f
assoc <=-Cat f g h =
  <=-unique
    (<=-trans (<=-trans f g) h)
    (<=-trans f (<=-trans g h))


<=-Preorder : Preorder
Preorder.cat <=-Preorder = <=-Cat
Preorder.one-arrow <=-Preorder = <=-unique
-- all of the info is in the arrows


record Monoid : Set where
  field
    cat : Category
    Obj-is-One : Obj cat == One


Nat+N-Cat : Category
Obj Nat+N-Cat = One
_~>_ Nat+N-Cat _ _ = Nat
id~> Nat+N-Cat _ = zero            --(x : One) -> Nat
_>~>_ Nat+N-Cat = _+N_
left-id Nat+N-Cat f = refl
right-id Nat+N-Cat = +N-right-zero      --f +N zero == f
assoc Nat+N-Cat = +N-assoc               -- (f g h : Nat) -> (f +N g) +N h == f +N g +N h

{-
Nat+N-Monoid : Monoid
Nat+N-Monoid = {!!}
-- a category with one object
-- *
ONE : Category
Obj ONE = One
_~>_ ONE _ _ = One
id~> ONE = {!!}
_>~>_ ONE = {!!}
left-id ONE = {!!}
right-id ONE = {!!}
assoc ONE = {!!}
-- a category with two objects
-- * --> *
module TwoCat where
  data ArrTwo : Two -> Two -> Set where
  TWO : Category
  Obj TWO = Two
  _~>_ TWO = ArrTwo
  id~> TWO = {!!}
  _>~>_ TWO = {!!}
  left-id TWO = {!!}
  right-id TWO = {!!}
  assoc TWO = {!!}
-- we'll be making this a monoid, so the objects will be One for sure
-- with our arrows being List A s
List-+L-Cat : Set -> Category
List-+L-Cat = {!!}
List-+L-Monoid : Set -> Monoid
List-+L-Monoid = {!!}
-- a Discrete category is one in which the only arrows are the identity arrows
-- an example of such a category is the one formed with an arbitrary type, and _==_ as arrows
Discrete== : Set -> Category
Obj (Discrete== X) = X
_~>_ (Discrete== X) = _==_
id~> (Discrete== X) = {!!}
_>~>_ (Discrete== X) = {!!}
left-id (Discrete== X) = {!!}
right-id (Discrete== X) = {!!}
assoc (Discrete== X) = {!!}
-- we can make a category with whatever arrows we like
-- if we have no objects
EMPTY : Set -> Category
Obj (EMPTY X) = Zero
_~>_ (EMPTY X) _ _ = X
id~> (EMPTY X) = {!!}
_>~>_ (EMPTY X) = {!!}
left-id (EMPTY X) = {!!}
right-id (EMPTY X) = {!!}
assoc (EMPTY X) = {!!}
-- we can always "flip" the arrows in a category, to get a "dual" notion of something
-- very powerful concept
Op : Category -> Category
Obj (Op X) = Obj X
_~>_ (Op X) x y = _~>_ X y x
id~> (Op X) = {!!}
_>~>_ (Op X) = {!!}
left-id (Op X) = {!!}
right-id (Op X) = {!!}
assoc (Op X) f g h = {!!}
-- a product of two other categories - we want to "carry" our operations pointwise
Product : Category -> Category -> Category
Obj (Product X Y) = Obj X * Obj Y
_~>_ (Product X Y) = {!!}
id~> (Product X Y) = {!!}
_>~>_ (Product X Y) = {!!}
left-id (Product X Y) = {!!}
right-id (Product X Y) = {!!}
assoc (Product X Y) = {!!}
-- like homomorphisms
record _=>_ (C D : Category) : Set where
  field
    F-Obj : Obj C -> Obj D
    F-map : {S T : Obj C} -> (_~>_ C S T) -> _~>_ D (F-Obj S) (F-Obj T)
    F-map-id : {S : Obj C} -> F-map (id~> C S) == id~> D (F-Obj S)
    F-map->~> :
      {S T R : Obj C}
      (f : _~>_ C S T) (g : _~>_ C T R) ->
      F-map (_>~>_ C f g) == _>~>_ D (F-map f) (F-map g)
open _=>_ public
postulate
  ext :
    {A B : Set} {f g : A -> B} ->
    ((x : A) -> f x == g x) -> f == g
id : {A : Set} -> A -> A
id x = x
-- the identity functor
-- does nothing
ID : (C : Category) -> C => C
ID = {!!}
map : {A B : Set} -> (A -> B) -> List A -> List B
map = {!!}
map-id : {A : Set} (xs : List A) -> map id xs == xs
map-id = {!!}
_>>_ : {S R T : Set} -> (S -> R) -> (R -> T) -> S -> T
_>>_ f g x = g (f x)
map-compose :
  {A B C : Set} (f : A -> B) (g : B -> C) (xs : List A) ->
  map (f >> g) xs == map g (map f xs)
map-compose = {!!}
-- lists are a functor
LIST : SET => SET
F-Obj LIST = List
F-map LIST = map
F-map-id LIST = ext {!!}
F-map->~> LIST f g = ext {!!}
-- addition with some constant is a functor over our previous Nat preorder category
ADD : Nat -> <=-Cat => <=-Cat
ADD k = {!!}
-- every function generates a functor over the list monoid,
-- showing that applying it for each element respects the list structure
LIST+L : {X Y : Set} (f : X -> Y) -> List-+L-Cat X => List-+L-Cat Y
LIST+L = {!!}
vTake : {A : Set} {n m : Nat} -> n <= m -> Vec A m -> Vec A n
vTake = {!!}
-- vTake forms a functor, sending a perorder into a type (Vec X n)
-- we need to use the opposite category of <=-Cat here, to make the "directions" match up
VTAKE : Set -> Op <=-Cat => SET
VTAKE = {!!}
-}