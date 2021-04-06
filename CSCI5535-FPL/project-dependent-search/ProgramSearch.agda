module ProgramSearch where


open import Level renaming (suc to lsuc ; zero to lzero)
open import Data.Nat using (ℕ)
open import Relation.Binary using (IsDecEquivalence ; Rel)

open import Data.List using (List)
open import Data.Product using (Σ-syntax)



record Module (n : ℕ) : Set (lsuc lzero) where
  field
    Carrier : ℕ → Set



record TypeSystem : Set (lsuc lzero) where
  field
    Type : ℕ → Set
    ⟦_⟧_ : ∀ {n} → Type n → Module n → Set



record DecTypeSystem : Set (lsuc lzero) where
  field
    Type : ℕ → Set
    ⟦_⟧_ : ∀ {n} → Type n → Module n → Set
    _~_ : ∀ {n m} → Type n → Type m → Set
    ~-isDecEquiv : ∀ {n} → IsDecEquivalence (_~_ {n})


  isTypeSystem : TypeSystem
  isTypeSystem = record { Type =  Type
                        ; ⟦_⟧_ =  ⟦_⟧_ }


