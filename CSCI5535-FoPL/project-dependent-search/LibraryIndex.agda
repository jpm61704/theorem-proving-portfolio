{-# OPTIONS --type-in-type #-}
module LibraryIndex where

open import Data.Product using (proj₁)
open import Library
open import TypingUniverse

searchModule : Module _
searchModule = [] ∷ U , Nat
        ∷ ⟨ 1 ⟩ , zero
        ∷ ⟨ 1 ⟩ ⇒ ⟨ 1 ⟩ , suc
        ∷ U , Bool
        ∷ ⟨ 1 ⟩ , suc (suc zero)
        ∷ ⟨ 4 ⟩ , true
        ∷ ⟨ 4 ⟩ , false
        ∷ ⟨ 4 ⟩ ⇒ ⟨ 4 ⟩ , not
        ∷ ⟨ 4 ⟩ ⇒ ⟨ 4 ⟩ ⇒ ⟨ 4 ⟩ , _∧_
        ∷ ⟨ 4 ⟩ ⇒ ⟨ 4 ⟩ ⇒ ⟨ 4 ⟩ , _∨_
        ∷ ⟨ 4 ⟩ ⇒ ⟨ 4 ⟩ ⇒ ⟨ 4 ⟩ , _xor_
        ∷ ⟨ 4 ⟩ ⇒ ⟨ 1 ⟩ , toNat
        ∷ ⟨ 1 ⟩ ⇒ ⟨ 1 ⟩ ⇒ ⟨ 1 ⟩ , _+_
        ∷ ⟨ 1 ⟩ ⇒ ⟨ 1 ⟩ ⇒ ⟨ 1 ⟩ , _-_
        ∷ ⟨ 1 ⟩ ⇒ ⟨ 1 ⟩ ⇒ ⟨ 1 ⟩ , _*_
        ∷ ⟨ 1 ⟩ ⇒ ⟨ 1 ⟩ ⇒ ⟨ 4 ⟩ , _==_
        ∷ ⟨ 1 ⟩ ⇒ ⟨ 1 ⟩ ⇒ ⟨ 4 ⟩ , _<_
        ∷ ⟨ 1 ⟩ ⇒ ⟨ 1 ⟩ , add2


fill' : ∀ {n} → (tc : TypeCode n) → proj₁ (feelingLucky tc searchModule)
fill' tc = fill tc searchModule

five : Nat
five = suc (suc (suc (suc (suc zero))))

-- Nat -> Nat -> Nat
tc1 : ∀ {x} → TypeCode x
tc1 = ⟨ 1 ⟩ ⇒ ⟨ 1 ⟩ ⇒ ⟨ 1 ⟩

interpretTC1 : Set
interpretTC1 = ⟦ tc1 ⟧ searchModule

tc2 : TypeCode 1
tc2 = ⟨ 1 ⟩


testSearch : HomogeneousList
testSearch = search (tc1 {1}) searchModule

testSearchNat : HomogeneousList
testSearchNat = search tc2 searchModule


missingNumber : Nat
missingNumber = five +  fill' tc2


partialProgram : Nat
partialProgram = (fill' (tc1 {1})) (fill' tc2) (fill' tc2)
-- partialProgram = (fill' tc1) (fill' tc2) (fill' tc2)
