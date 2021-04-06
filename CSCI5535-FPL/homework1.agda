module homework1 where

open import Relation.Nullary
open import Data.Product
open import Relation.Binary.PropositionalEquality

data Card : Set where
  ♡ ♠ ♣ ♢ : Card

data Deck : Set where
  nil : Deck
  cons : Card → Deck → Deck


data Unshuffle : Deck → Deck → Deck → Set where
  unshuffle-nil  : Unshuffle nil nil nil
  unshuffle-left : ∀ {s₁ s₂ s₃ : Deck} (c : Card)
                   → (Unshuffle s₁ s₂ s₃)
                   ----------------------------------
                   → Unshuffle (cons c s₁) (cons c s₂) s₃
  unshuffle-right : ∀ {s₁ s₂ s₃ : Deck} (c : Card)
                   → (Unshuffle s₁ s₂ s₃)
                   ----------------------------------
                   → Unshuffle (cons c s₁) s₂ (cons c s₃)


{-
Problem 2.
-}


proof2Aₗ : ∀ (s₁ : Deck) → Unshuffle s₁ s₁ nil
proof2Aₗ nil =  unshuffle-nil
proof2Aₗ (cons x s₁) =  unshuffle-left x (proof2Aₗ s₁)

proof2Aᵣ : ∀ (s₁ : Deck) → Unshuffle s₁ nil s₁
proof2Aᵣ nil =  unshuffle-nil
proof2Aᵣ (cons x s₁) =  unshuffle-right x (proof2Aᵣ s₁)

proof2A : ∀ (s₁ : Deck) → ∃  λ s₂ →  ∃  λ s₃ →  Unshuffle s₁ s₂ s₃
proof2A d =  d , nil ,  proof2Aₗ d


{-
Problem 2. Part B
-}

data Even : Deck → Set
data Odd : Deck → Set

data Odd where
  even⇒odd : ∀ {s : Deck} (c : Card) → (Even s)
                  ------------------------------------
                  → Odd (cons c s)

data Even where
  nil-even : Even nil
  odd⇒even : ∀ {s : Deck} (c : Card) → (Odd s)
                  ------------------------------------
                  → Even (cons c s)

{-
Subpart 2.B.i
-}
ind-even : ∀ {P : ∀ {s} → Even s → Set}
          → (P nil-even)
          → (∀ {s} {x y : Card} {deckₑ : Even s} → ((P deckₑ) → (P ( odd⇒even x (even⇒odd y deckₑ)))))
          → ∀ {s} (even : Even s) → P even
ind-even base _ nil-even = base
ind-even {P} base ind (odd⇒even c₁ (even⇒odd c₂ even)) =  ind (ind-even {P} base ind even)


ind-odd : ∀ {P : ∀ {s} → Odd s → Set}
        → (∀ {c} → P (even⇒odd c nil-even))
        → (∀ {s} {x y : Card} {deckₒ : Odd s} → ((P deckₒ) → P (even⇒odd x (odd⇒even y deckₒ))) )
        → ∀ {s} (odd : Odd s) → P odd
ind-odd {P} base ind (even⇒odd c nil-even) = base
ind-odd {P} base ind (even⇒odd c (odd⇒even c₁ x)) =  ind ( ind-odd {P} base ind x)


{-
Subpart 2.B.ii
-}
indii : ∀ {P : Deck → Set}
        → (P nil)
        → (∀ {c₁ c₂ : Card} {s : Deck} → P s → P (cons c₁ (cons c₂ s)))
        → ∀ {s : Deck} → (Even s → P s)
indii {P} base ind =  ind-even { λ {s} even → P s} base ind
{-
or

indii {P} base ind nil-even = base
indii {P} base ind (odd⇒even c₁ (even⇒odd c₂ s)) with indii {P} base ind s
...| H = ind H
-}


{-
Subpart 2.B.iii
-}

data Cut : Deck → Deck → Deck → Set where
  cut-nil : ∀ (s : Deck)
          ----------------------------
          → Cut s s nil

  cut-cons : ∀ {s₁ s₂ s₃ : Deck} (c : Card)
           → (Cut s₁ s₂ s₃)
           -------------------------------------------------
           → Cut (cons c s₁) s₂ (cons c s₃)


inversion-nil : ∀ {s₁ s₂} → Cut s₁ s₂ nil
              → s₁ ≡ s₂
inversion-nil (cut-nil s) = refl

inversion-cons : ∀ {s₁ s₂ s₃} {c} → Cut s₁ s₂ (cons c s₃)
               → Σ[ s₁' ∈ Deck ] (s₁ ≡ cons c s₁' × Cut s₁' s₂ s₃)
inversion-cons (cut-cons {s₁'} c2 cut) =  s₁' ,  refl ,  cut


prf : ∀ {s₁ s₂ s₃ : Deck}
    → Even s₂
    → Even s₃
    → Cut s₁ s₂ s₃
    → Even s₁
prf e2 nil-even c with inversion-nil c
...| refl = e2
prf e2 (odd⇒even c₁ (even⇒odd c₂ x)) (cut-cons .c₁ (cut-cons .c₂ c)) with inversion-cons (cut-cons c₂ c)
...| d , refl , ct with prf e2 x c
...| ev1 = odd⇒even c₁ (even⇒odd c₂ ev1)

{-

-}
