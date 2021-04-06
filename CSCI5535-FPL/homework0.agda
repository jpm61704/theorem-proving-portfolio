module homework0 where

open import Relation.Nullary

-- unicode suits ♡ ♠ ♣ ♢


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

-- ** Part A
{-
Prove the following judgement. There are at least two ways to do so.

-}

proof6A : Unshuffle (cons ♡ (cons ♠ (cons ♠ (cons ♢ nil))))
                    (cons ♠ (cons ♢ nil)) (cons ♡ (cons ♠ nil))
proof6A = unshuffle-right ♡ (unshuffle-left ♠ (unshuffle-right ♠ (unshuffle-left ♢ unshuffle-nil)))


proof6A' : Unshuffle (cons ♡ (cons ♠ (cons ♠ (cons ♢ nil))))
                     (cons ♠ (cons ♢ nil)) (cons ♡ (cons ♠ nil))
proof6A' = unshuffle-right ♡ (unshuffle-right ♠ (unshuffle-left ♠ (unshuffle-left ♢ unshuffle-nil)))

-- ** Part B

data Separate : Deck → Deck → Deck → Set where
  separate-nil : Separate nil nil nil
  separate-diamond : ∀ {deck reds blacks : Deck}
                   → Separate deck reds blacks
                   → Separate (cons ♢ deck) (cons ♢ reds) blacks

  separate-heart   : ∀ {deck reds blacks : Deck}
                   → Separate deck reds blacks
                   → Separate (cons ♡ deck) (cons ♡ reds) blacks

  separate-spade   : ∀ {deck reds blacks : Deck}
                   → Separate deck reds blacks
                   → Separate (cons ♠ deck) reds (cons ♠ blacks)


  separate-club    : ∀ {deck reds blacks : Deck}
                   → Separate deck reds blacks
                   → Separate (cons ♣ deck) reds (cons ♣ blacks)


proof6B1 : Separate (cons ♡ (cons ♢ (cons ♠ nil))) (cons ♡ (cons ♢ nil)) (cons ♠ nil)
proof6B1 = separate-heart (separate-diamond (separate-spade separate-nil))

proof6B2 : Separate (cons ♠ (cons ♢ (cons ♣ (cons ♡ nil)))) (cons ♢ (cons ♡ nil)) (cons ♠ (cons ♣ nil))
proof6B2 = separate-spade (separate-diamond (separate-club (separate-heart separate-nil)))

proof6B3 : Separate (cons ♣ (cons ♡ (cons ♣ (cons ♠ nil)))) (cons ♡ nil) (cons ♣ (cons ♣ (cons ♠ nil)))
proof6B3 = separate-club (separate-heart (separate-club (separate-spade separate-nil)))


impossibleProof6B4 : ¬ (Separate (cons ♡ (cons ♠ nil)) (cons ♡ (cons ♠ nil)) nil)
impossibleProof6B4 (separate-heart ())

impossibleProof6B5 : ¬ (Separate (cons ♡ (cons ♢ nil)) (cons ♢ (cons ♡ nil)) nil)
impossibleProof6B5 ()

