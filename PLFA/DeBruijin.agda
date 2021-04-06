

module DeBruijin where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Nullary using (¬_)

infix  4 _⊢_
infix  4 _∋_
infixl 5 _,_

infixr 7 _⇒_

infix  5 ƛ_
infix  5 μ_
infixl 7 _·_
infix  8 `suc_
infix  9 `_
infix  9 S_
infix  9 #_


data Type : Set where
  _⇒_ : Type → Type → Type
  Num : Type

data Context : Set where
  ∅ : Context
  _,_ : Context → Type → Context


data _∋_ : Context → Type → Set where
  Z : ∀ {Γ A}
    -----------------
    → Γ , A ∋ A

  S_ : ∀ {Γ A B}
     → Γ ∋ A
     → Γ , B ∋ A


data _⊢_ : Context → Type → Set where
  `_ : ∀ {Γ A}
     → Γ ∋ A
     -----------
     → Γ ⊢ A

  ƛ_ : ∀ {Γ A B}
     → Γ , A ⊢ B
     ----------------
     → Γ ⊢ A ⇒ B

  _∙_ : ∀ {Γ A B}
      → Γ ⊢ A ⇒ B
      → Γ ⊢ A
      ---------------
      → Γ ⊢ B

  `zero : ∀ {Γ}
        --------------
        → Γ ⊢ Num

  `suc_ : ∀ {Γ}
        → Γ ⊢ Num
        -------------
        → Γ ⊢ Num

  case : ∀ {Γ A}
       → Γ ⊢ Num
       → Γ ⊢ A
       → Γ , Num ⊢ A
       -----------------
       → Γ ⊢ A

  μ_ : ∀ {Γ A}
     → Γ , A ⊢ A
     ---------------
     → Γ ⊢ A


lookup : Context → ℕ → Type
lookup (Γ , A) zero = A
lookup (Γ , A) (suc n) = lookup Γ n
lookup ∅ _ = ⊥-elim impossible
  where postulate impossible : ⊥

count : ∀ {Γ} → (n : ℕ) → Γ ∋ lookup Γ n
count {Γ , _} zero     =  Z
count {Γ , _} (suc n)  =  S (count n)
count {∅}     _        =  ⊥-elim impossible
  where postulate impossible : ⊥

#_ : ∀ {Γ} → (n : ℕ) → Γ ⊢ lookup Γ n
# n  =  ` count n

ext : ∀ {Γ Δ}
    → (∀ {A} →       Γ ∋ A →     Δ ∋ A)
    ---------------------------------
    → (∀ {A B} → Γ , B ∋ A → Δ , B ∋ A)
ext ρ Z      =  Z
ext ρ (S x)  =  S (ρ x)

rename : ∀ {Γ Δ}
       → (∀ {A} → Γ ∋ A → Δ ∋ A)
       -----------------------
       → (∀ {A} → Γ ⊢ A → Δ ⊢ A)
rename ρ (` x) =  ` ρ x
rename ρ (ƛ N) =  ƛ  rename (ext ρ) N
rename ρ (N ∙ M) =  (rename ρ N) ∙ rename ρ M
rename ρ `zero =  `zero
rename ρ (`suc N) =  `suc (rename ρ N)
rename ρ (case N M K) =  case (rename ρ N) (rename ρ M) (rename (ext ρ) K)
rename ρ (μ N) =  μ (rename (ext ρ) N)

exts : ∀ {Γ Δ}
     → (∀ {A} →       Γ ∋ A →     Δ ⊢ A)
     ---------------------------------
     → (∀ {A B} → Γ , B ∋ A → Δ , B ⊢ A)
exts σ Z      =  ` Z
exts σ (S x)  =  rename S_ (σ x)


subst : ∀ {Γ Δ}
      → (∀ {A} → Γ ∋ A → Δ ⊢ A)
      -----------------------
      → (∀ {A} → Γ ⊢ A → Δ ⊢ A)
subst σ (` x) = σ x
subst σ (ƛ M) =  ƛ subst ( exts σ) M
subst σ (M ∙ N) =  (subst σ M) ∙ (subst σ N)
subst σ `zero =  `zero
subst σ (`suc M) =  `suc (subst σ M)
subst σ (case M N K) =  case (subst σ M) (subst σ N) (subst (exts σ) K)
subst σ (μ M) =  μ (subst (exts σ) M)

_[_] : ∀ {Γ A B}
     → Γ , B ⊢ A
     → Γ ⊢ B
     ---------
     → Γ ⊢ A
_[_] {Γ} {A} {B} N M =  subst {Γ , B} {Γ} σ {A} N
  where
    σ : ∀ {A} → Γ , B ∋ A → Γ ⊢ A
    σ Z      =  M
    σ (S x)  =  ` x


data Value : ∀ {Γ A} → Γ ⊢ A → Set where

  V-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B}
      ---------------------------
      → Value (ƛ N)

  V-zero : ∀ {Γ}
         -----------------
         → Value (`zero {Γ})

  V-suc : ∀ {Γ} {V : Γ ⊢ Num}
        → Value V
        --------------
        → Value (`suc V)


