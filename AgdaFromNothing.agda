module AgdaFromNothing where

data Boolean : Set where
    -- true : Boolean
    -- false : Boolean
    true false : Boolean

data One : Set where
    tt : One

data Empty : Set where

mybool : Boolean
mybool = true

-- myfunction : Boolean → Boolean
-- myfunction true = true
-- myfunction false = false

-- identity : Boolean → Boolean
-- identity true = true
-- identity false = false


not : Boolean -> Boolean
-- not true = false
-- not false = true
not false = true
not true = false


-- and : Boolean → (Boolean → Boolean)
-- and true true = true
-- and true false = false
-- and false true = false
-- and false false = false

infixl 7 _and_
infixl 6 _or_   
_and_ : Boolean → (Boolean → Boolean)
-- false and false = false
-- false and true = false
-- true and false = false
-- true and true = true

-- true and true = true
-- _ and _ = false

-- true and y = {!   !}
-- false and y = {!   !} 

false and _ = false 
true and y = y

 

_or_ : Boolean → Boolean → Boolean
-- true or true = {!   !}
-- true or false = {!   !}
-- false or true = {!   !}
-- false or false = {!   !} 
true or y = y
false or y = true


-- if_then_else_ : Boolean → Boolean → Boolean → Boolean
-- if false then _ else y = y
-- if true then x else _ = x 

-- not' : Boolean → Boolean
-- not' x = if x then false else true 




-- open import Agda.Primitive
-- if_then_else_ : {level : Level} → {X : Set level} → Boolean → X → X → X 
-- if false then _ else y = y
-- if true then x else _ = x 

-- not' : Boolean → Boolean
-- not' x = if x then false else true 


-- data Equal : Boolean → Boolean → Set where
--     equal : (x : Boolean) → Equal x x

-- proof : Equal (true and true) true                           --not false is equal to true
-- proof = equal                                                   -- c+c c+r r=refine

-- not-eq-not' : (x : Boolean) → Equal (not x) (not' x)
-- not-eq-not' false = equal  
-- not-eq-not' true = equal




open import Agda.Primitive
if_then_else_ : {ℓ : Level} → {X : Set ℓ} → Boolean → X → X → X
if false then _ else y = y
if true then x else _ = x 

not' : Boolean → Boolean
not' x = if x then false else true

data Equal : Boolean → Boolean → Set where
    equal : {x : Boolean} → Equal x x 

proof : Equal (true and true) true                           
proof = equal  

not-eq-not' : (x : Boolean) → Equal (not x) (not' x)
not-eq-not' false = equal
not-eq-not' true = equal

false-and : (x : Boolean) → Equal (false and x) false
false-and x = equal

and-false : (x : Boolean) → Equal (x and false) false
and-false false = equal
and-false true = equal





data Natural : Set where
    zero : Natural
    suc : Natural → Natural

_+_ : Natural → Natural → Natural
zero + y = y
suc x + y = suc(x + y)                          -- (1 + x) + y = 1 + (x + y)














