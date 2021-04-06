{-# OPTIONS --type-in-type #-}

module TypingUniverse where

open import Data.Nat using (ℕ ; suc ; zero ; _<_ ; z≤n ; s≤s  ; _≟_ ; _≤_ ; _≤?_)
open import Data.Nat.Base using (_∸_)
open import Data.Nat.Properties using (n∸m≤n)
open import Data.Bool using (Bool ; true ; false)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Product using (Σ-syntax)

open import Relation.Nullary using (Dec ; yes ; no)
open import Relation.Unary using (Pred)
open import Relation.Binary using ( IsEquivalence ; Reflexive ; Symmetric ; Transitive
                                  ; IsDecEquivalence ; Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong₂ ; subst)

open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)


import ProgramSearch as P

-- Calculation shortcut for n<m
#- : ∀ {m} → (n : ℕ) → n < m
#- {zero} n = ⊥-elim impossible
  where postulate impossible : ⊥
#- {suc m} zero =  s≤s z≤n
#- {suc m} (suc n) =  s≤s ( #- n)



data TypeCode : ℕ → Set

infixr 5 _⇒_
infixl 6 _××_

data TypeCode where
  U : ∀ {n} → TypeCode n
  _⇒_ : ∀ {n} → TypeCode n → TypeCode n → TypeCode n
  _××_ : ∀ {n} → TypeCode n → TypeCode n → TypeCode n
  #_ : ∀ {n m} → n < m → TypeCode m


data Module : ℕ → Set

-- Type Interpretation(in module m)
⟦_⟧_ : ∀ {n} → TypeCode n → Module n → Set

-- Relative Reference Lookup in a module
⟪_⟫_ : ∀ {n m} → n < m → Module m → Set

-- Absolute Reference Lookup in module
⟨a⟨_⟫_ : ∀ {n m} → n < m → Module m → Set

infixl 10 _∷_,_

data Module where
  [] : Module 0
  _∷_,_ : ∀ {n}
        → (Γ : Module n)
        → (t : TypeCode n)
        → (⟦ t ⟧ Γ)
        → Module (suc n)


-- Type Interpretation
⟦ U ⟧ Γ      = Set
⟦ A ⇒ B ⟧ Γ =  ⟦ A ⟧ Γ → ⟦ B ⟧ Γ
⟦  A ×× B  ⟧ Γ =  ⟦ A ⟧ Γ × ⟦ B ⟧ Γ
⟦ # n<m ⟧ Γ  = ⟨a⟨ n<m ⟫ Γ

-- Relative(DeBruijin) reference Lookup
⟪ s≤s z≤n ⟫ (Γ ∷ U , term) =  term
{-# CATCHALL #-}
⟪ s≤s z≤n ⟫ (Γ ∷ type , term) =  ⊥-elim impossible
  where postulate impossible : ⊥
-- ⟪ s≤s (s≤s n<m) ⟫ (Γ ∷ _ , _) =  ⟪  s≤s n<m  ⟫ Γ
⟪ s≤s (s≤s n<m) ⟫ (Γ ∷ _ , _) =  ⟪ s≤s n<m  ⟫ Γ


⟨a⟨_⟫_ {n} {m} n<m Γ =  ⟪ k<m ⟫ Γ
  where k<m : m ∸ n < m
        k<m =  #- (m ∸ n) -- This is a poor way of doing this


--------------------------------------------------------------------------------
---------------------------- TypeCode Equality ---------------------------------
--------------------------------------------------------------------------------

infixl 2 _~_

data _~_ {n} {m} : TypeCode n → TypeCode m → Set where
  U~U : U ~ U

  ⇒~⇒ : ∀ {A A' B B'}
        → A ~ A'
        → B ~ B'
        ----------------------
        → A ⇒ B ~ A' ⇒ B'

  #~# : ∀ {k} {k<n : k < n} {k<m : k < m}
      ----------------------------------------
      → (# k<n ) ~ (# k<m)
  ×~× : ∀ {A A' B B'}
        → A ~ A'
        → B ~ B'
        ----------------------
        →  A ×× B ~  A' ×× B'



~-refl : ∀ {n} → Reflexive (_~_ {n})
~-refl {n} {U} =  U~U
~-refl {n} {A ⇒ B} =  ⇒~⇒ ~-refl ~-refl
~-refl {n} { A ×× B } =  ×~× ~-refl ~-refl
~-refl {n} {# x} = #~#

~-sym : ∀ {n} → Symmetric (_~_ {n})
~-sym U~U =  U~U
~-sym (⇒~⇒ A~B A'~B') =  ⇒~⇒ ( ~-sym A~B) (~-sym A'~B')
~-sym (×~× A~B A'~B') =  ×~× ( ~-sym A~B) (~-sym A'~B')
~-sym #~# = #~#

~-trans : ∀ {n} → Transitive (_~_ {n})
~-trans U~U U~U                                  = U~U
~-trans (⇒~⇒ A~A' B~B') (⇒~⇒ A''~A' B''~B') =  ⇒~⇒ ( ~-trans A~A' A''~A') ( ~-trans B~B' B''~B')
~-trans (×~× A~A' B~B') (×~× A''~A' B''~B') =  ×~× ( ~-trans A~A' A''~A') ( ~-trans B~B' B''~B')
~-trans #~# #~#                                  = #~#

~-IsEquiv : ∀ {n} → IsEquivalence (_~_ {n})
~-IsEquiv = record { refl  =  ~-refl
                   ; sym   =  ~-sym
                   ; trans =  ~-trans
                   }

_≈?_ : ∀ {n m} → Decidable (_~_ {n} {m})
U ≈? U         =  yes U~U
U ≈? (A ⇒ B)  =  no λ ()
U ≈? ( A ×× B )  =  no λ ()
U ≈? (# x)     =  no λ ()
(A ⇒ B) ≈? U  =  no λ ()
(A ⇒ B) ≈? (A' ⇒ B') with A ≈? A' | B ≈? B'
...| yes ~₁ | yes ~₂ =  yes ( ⇒~⇒ ~₁ ~₂)
{-# CATCHALL #-}
...|  _   |  _    =  no (⊥-elim impossible)
  where postulate impossible : ⊥
(A ⇒ B) ≈? (# x) =  no λ ()
(A ⇒ B) ≈? (A' ×× B') =  no λ ()
(# x) ≈? U =  no λ ()
(# x) ≈? (A ⇒ B) =  no λ ()
(# x) ≈? (A ×× B) =  no λ ()
(#_ {x} x<k) ≈? (#_ {y} y<k) with x ≟ y
...| yes refl =  yes #~#
...| no x≠y   =  no ( ⊥-elim impossible)
  where postulate impossible : ⊥

(A ×× B) ≈? U  =  no λ ()
(A ×× B) ≈? (A' ⇒ B')  =  no λ ()
(A ×× B) ≈? (A' ×× B') with A ≈? A' | B ≈? B'
...| yes ~₁ | yes ~₂ =  yes ( ×~× ~₁ ~₂)
{-# CATCHALL #-}
...|  _   |  _    =  no (⊥-elim impossible)
  where postulate impossible : ⊥
(A ×× B) ≈? (# x) =  no λ ()



~-isDecEquiv : ∀ {n} → IsDecEquivalence (_~_ {n})
~-isDecEquiv =  record { isEquivalence = ~-IsEquiv
                       ; _≟_ = _≈?_}




--------------------------------------------------------------------------------
-------------------------------- Search ----------------------------------------
--------------------------------------------------------------------------------

open import Data.List using (List) renaming ([] to empty ; _∷_ to cons)


TermList : Set
TermList = Σ[ t ∈ Set ] (List t)


HomogeneousList : Set
HomogeneousList = List (Σ[ t ∈ Set ] t)


{-
  This is the ultimate goal

  This may require some notion of type equality that is implied from a typecode
  being equal to another typecode.

  It also requires some sort of weakening lemma for typecodes
-}
search' : ∀ {n m} → n ≤ m → (tc : TypeCode n) → (Γ : Module m) → HomogeneousList
search' z≤n tc [] =  empty
search' z≤n tc (Γ ∷ tc' , term) with tc ≈? tc'
...| yes tc≈tc' = cons (⟦ tc' ⟧ Γ , term) (search' z≤n tc Γ)
...| no  tc≉tc' = search' z≤n tc Γ
search' (s≤s {n} {m} n≤m) tc (Γ ∷ tc' , term) with tc ≈? tc' | suc n ≤? m
...| yes tc≈tc' | yes sn≤m =  cons ( ( ⟦ tc' ⟧ Γ) ,  term) ( search'  sn≤m tc Γ)
...| yes tc≈tc' | no  sn≰m =  cons ( ( ⟦ tc' ⟧ Γ) ,  term) empty
...| no tc≉tc'  | yes sn≤m =  search'  sn≤m tc Γ
...| no tc≉tc'  | no  sn≰m =  empty

search : ∀ {n m} → TypeCode n → Module m → HomogeneousList
search {n} {m} with n ≤? m
...| yes n≤m = search' n≤m
...| no n≰m  = ⊥-elim impossible
  where postulate impossible : ⊥



feelingLucky : ∀ {n m} → TypeCode n → Module m → Σ[ t ∈ Set ] t
feelingLucky tc m with search tc m
feelingLucky tc m | empty = ⊥-elim NoResultError
  where postulate NoResultError : ⊥
feelingLucky tc m | cons x res = x



unpackTerm : (R : Σ[ t ∈ Set ] t) → proj₁ R
unpackTerm ( type , term ) =  term

fill : ∀ {n m} → (tc : TypeCode n) → (Γ : Module m) → proj₁ (feelingLucky tc Γ)
fill tc Γ = unpackTerm (feelingLucky tc Γ)

--------------------------------------------------------------------------------
-------------------------------- Examples --------------------------------------
--------------------------------------------------------------------------------


-- Unsafe reference creation
⟨_⟩ : ∀ {m} → ℕ → TypeCode m
⟨ n ⟩ = # (#- n)




module Example where

  toNum : Bool → ℕ
  toNum false =  0
  toNum true  =  1

  C : Bool → Set
  C true = ℕ
  C false = Bool

  mult : ℕ × ℕ → ℕ
  mult (n , m) =  n Data.Nat.* m


  ex : Module _
  ex = [] ∷  U                      , ℕ
          ∷  ⟨ 1 ⟩                   , 5
          ∷  ⟨ 1 ⟩                   , 2
          ∷  U                      , Bool
          ∷  ⟨ 4 ⟩                   , true
          ∷  ⟨ 4 ⟩ ⇒ ⟨ 1 ⟩          , toNum
          ∷  ⟨ 4 ⟩                   , false
          ∷  ⟨ 4 ⟩ ⇒ U              ,  C
          ∷ (⟨ 1 ⟩ ×× ⟨ 1 ⟩) ⇒ ⟨ 1 ⟩ , mult


  -- Bool → ℕ
  tc₁ : TypeCode 4
  tc₁ = ⟨ 4 ⟩ ⇒ ⟨ 1 ⟩

  search₁ : HomogeneousList
  search₁ = search tc₁ ex


  hole : ℕ
  hole = unpackTerm (feelingLucky tc ex)
    where tc : TypeCode 1
          tc = ⟨ 1 ⟩
