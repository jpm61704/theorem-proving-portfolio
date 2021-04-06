module Library where

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

data Bool : Set where
  true : Bool
  false : Bool

infixr 6 _∧_
infixr 5 _∨_ _xor_

not : Bool → Bool
not true  = false
not false = true

_∧_ : Bool → Bool → Bool
true  ∧ b = b
false ∧ b = false

_∨_ : Bool → Bool → Bool
true  ∨ b = true
false ∨ b = b

_xor_ : Bool → Bool → Bool
true  xor b = not b
false xor b = b

toNat : Bool → Nat
toNat true = suc zero
toNat false = zero


infix  4 _==_ _<_
infixl 6 _+_ _-_
infixl 7 _*_

_+_ : Nat → Nat → Nat
zero  + m = m
suc n + m = suc (n + m)

_-_ : Nat → Nat → Nat
n     - zero = n
zero  - suc m = zero
suc n - suc m = n - m

_*_ : Nat → Nat → Nat
zero  * m = zero
suc n * m = m + n * m


_==_ : Nat → Nat → Bool
zero  == zero  = true
suc n == suc m = n == m
{-# CATCHALL #-}
_     == _     = false


_<_ : Nat → Nat → Bool
_     < zero  = false
zero  < suc _ = true
suc n < suc m = n < m

add2 : Nat → Nat
add2 n = suc (suc n)



