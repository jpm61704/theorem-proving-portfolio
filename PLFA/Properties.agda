module Properties where

open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; cong₂)
open import Data.String using (String; _≟_ )
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product
  using (_×_; proj₁; proj₂; ∃; ∃-syntax)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Function using (_∘_)
-- open import plfa.Isomorphism
open import LambdaCalculus


-- Some Definitions
{-
- Recall -
  A ⟶ B  Denotes reductions from A to B

Progress: If ∅ ⊢ M ∶ A then either M is a value or there is an N such
          that M ⟶ N.

Preservation: If ∅ ⊢ M ∶ A and M ⟶ N then ∅ ⊢ N ∶ A


These two properties taken together, and applied to the lambda calculus, allow
us to say that every closed, well-typed term will evaluate to a value
-}


-- Values do not reduce

V¬⟶ : ∀ {M N} → Value M → ¬ (M ⟶ N)
V¬⟶ V-ƛ        ()
V¬⟶ V-zero     ()
V¬⟶ (V-suc VM) (ξ-suc M⟶N) =  V¬⟶ VM M⟶N

-- Corollary: terms that reduce are not values

⟶¬V : ∀ {M N} → M ⟶ N → ¬ Value M
⟶¬V M⟶N VM =  V¬⟶ VM M⟶N


-- Canonical Forms
{-
Canonical Forms are closed and well-typed
-}

infix 4 Canonical_∶_

data Canonical_∶_ : Term → Type → Set where

  C-ƛ : ∀ {x A N B}
      → ∅ , x ∶ A ⊢ N ∶ B
      ------------------------
      → Canonical (ƛ x ⇒ N) ∶ (A ⇒ B)

  C-zero :
      ---------------------
      Canonical `zero ∶ `ℕ

  C-suc : ∀ {V}
        → Canonical V ∶ `ℕ
        ---------------------------
        → Canonical `suc V ∶ `ℕ


canonical : ∀ {V A} → ∅ ⊢ V ∶ A → Value V
          ----------------
          → Canonical V ∶ A
canonical (⊢ƛ e) v =  C-ƛ  e
canonical ⊢zero v =  C-zero
canonical (⊢suc e) (V-suc v) = C-suc (canonical e v )


value : ∀ {M A}
      → Canonical M ∶ A
      → Value M
value (C-ƛ x) =  V-ƛ
value C-zero =  V-zero
value (C-suc c) =  V-suc (value c)


typed : ∀ {M A} → Canonical M ∶ A
      → ∅ ⊢ M ∶ A
typed (C-ƛ ⊢N) =  ⊢ƛ ⊢N
typed C-zero =  ⊢zero
typed (C-suc CM) =  ⊢suc (typed CM)


-- Progress
{-
We wish to show that every term is either a value or may take a reduction step.

This is not true for non-canonical forms
-}


data Progress (M : Term) : Set where

  step : ∀ {N}
       → M ⟶ N
       ------------
       → Progress M

  done : Value M → Progress M

{-
The above may be read that M makes progress if it can take a reduction step or
if it is a value.
-}


progress : ∀ {M A}
         → ∅ ⊢ M ∶ A
         -----------------
         → Progress M
progress (⊢ƛ WT) =  done V-ƛ
progress (⊢L · ⊢M) with progress ⊢L
... | step L⟶L' =  step ( ξ-·₁  L⟶L')
... | done VL with progress ⊢M
...   | step M⟶M' =  step ( ξ-·₂ VL M⟶M')
...   | done VM with canonical ⊢L VL
...     | C-ƛ _ = step ( β-ƛ  VM)
progress ⊢zero =  done  V-zero
progress (⊢suc ⊢M) with progress ⊢M
... | step M⟶N =  step ( ξ-suc  M⟶N)
... | done VM =  done ( V-suc VM)
progress (⊢case ⊢L ⊢M ⊢N) with progress ⊢L
... | step L⟶L' =  step ( ξ-case L⟶L')
... | done V-zero =  step  β-zero
... | done (V-suc VL) =  step ( β-suc VL)
progress (⊢μ ⊢M) =  step β-μ



-- Preservation

-- Renaming

-- Extension Lemma
ext : ∀ {Γ Δ}
    → (∀ {x A} →  Γ ∋ x ∶ A → Δ ∋ x ∶ A)
    ----------------------------------------
    → (∀ {x y A B} → Γ , y ∶ B ∋ x ∶ A → Δ , y ∶ B ∋ x ∶ A)
ext ρ Z =  Z
ext ρ (S x≠y ∋x) =  S  x≠y ( ρ ∋x)


rename : ∀ {Γ Δ}
       → (∀ {x A} → Γ ∋ x ∶ A → Δ ∋ x ∶ A)
       ---------------------------------------
       → (∀ {M A} → Γ ⊢ M ∶ A → Δ ⊢ M ∶ A)
rename ρ (⊢` w) =  ⊢` (ρ  w)
rename ρ (⊢ƛ ⊢N) =  ⊢ƛ ( rename ( ext ρ)  ⊢N)
rename ρ (⊢M · ⊢L) =   rename  ρ  ⊢M ·  rename  ρ ⊢L
rename ρ ⊢zero =  ⊢zero
rename ρ (⊢suc ⊢x) =  ⊢suc ( rename ρ ⊢x)
rename ρ (⊢case ⊢N ⊢M ⊢L) =  ⊢case ( rename ρ ⊢N) ( rename ρ ⊢M) ( rename (ext ρ) ⊢L)
rename ρ (⊢μ ⊢M) =  ⊢μ ( rename (ext ρ) ⊢M)


-- Corolarries

-- 1.) Weakening

weaken : ∀ {Γ M A}
      → ∅ ⊢ M ∶ A
      ---------------
      → Γ ⊢ M ∶ A
weaken {Γ} ⊢M =  rename  ρ ⊢M
  where
    ρ : ∀ {z C}
        → ∅ ∋ z ∶ C
        -------------
        → Γ ∋ z ∶ C
    ρ ()

-- 2.) Drop
-- Drops a variable if the last two variables in the context are the same. Deletes the shaddowed one

drop : ∀ {Γ x M A B C}
     → Γ , x ∶ A , x ∶ B ⊢ M ∶ C
     ------------------------------
     → Γ , x ∶ B ⊢ M ∶ C
drop {Γ} {x} {M} {A} {B} {C} ⊢M =  rename ρ ⊢M
  where
  ρ : ∀ {z C}
    → Γ , x ∶ A , x ∶ B ∋ z ∶ C
    -----------------------------
    → Γ , x ∶ B ∋ z ∶ C
  ρ Z =  Z
  ρ (S x≠x Z) =  ⊥-elim (x≠x refl)
  ρ (S z≠x (S _ ∋z)) =  S z≠x ∋z

swap : ∀ {Γ x y M A B C}
     → x ≢ y
     → Γ , y ∶ B , x ∶ A ⊢ M ∶ C
     -------------------------------
     → Γ , x ∶ A , y ∶ B ⊢ M ∶ C
swap {Γ} {x} {y} {M} {A} {B} {C} x≢y ⊢M =  rename ρ ⊢M
  where
  ρ : ∀ {z C}
    → Γ , y ∶ B , x ∶ A ∋ z ∶ C
    -------------------------------
    → Γ , x ∶ A , y ∶ B ∋ z ∶ C
  ρ Z =  S  x≢y  Z
  ρ (S x≢y Z) =  Z
  ρ (S z≢x (S z≢y ∋z)) =  S z≢y ( S z≢x ∋z)

-- Substitution

subst : ∀ {Γ x N V A B}
      → ∅ ⊢ V ∶ A
      → Γ , x ∶ A ⊢  N ∶ B
      --------------------------
      → Γ ⊢ N [ x := V ] ∶ B
subst {x = y} ⊢V (⊢` {x = x} Z) with x ≟ y
... | yes refl        =  weaken ⊢V
... | no  x≢y         =  ⊥-elim (x≢y refl)
subst {x = y} ⊢V (⊢` {x = x} (S x≢y ∋x)) with x ≟ y
... | yes refl        =  ⊥-elim (x≢y refl)
... | no  _           =  ⊢` ∋x
subst {x = y} ⊢V (⊢ƛ {x = x} ⊢N) with x ≟ y
... | yes refl        =  ⊢ƛ (drop ⊢N)
... | no  x≢y         =  ⊢ƛ (subst ⊢V (swap x≢y ⊢N))
subst ⊢V (⊢L · ⊢M)    =  (subst ⊢V ⊢L) · (subst ⊢V ⊢M)
subst ⊢V ⊢zero        =  ⊢zero
subst ⊢V (⊢suc ⊢M)    =  ⊢suc (subst ⊢V ⊢M)
subst {x = y} ⊢V (⊢case {x = x} ⊢L ⊢M ⊢N) with x ≟ y
... | yes refl        =  ⊢case (subst ⊢V ⊢L) (subst ⊢V ⊢M) (drop ⊢N)
... | no  x≢y         =  ⊢case (subst ⊢V ⊢L) (subst ⊢V ⊢M) (subst ⊢V (swap x≢y ⊢N))
subst {x = y} ⊢V (⊢μ {x = x} ⊢M) with x ≟ y
... | yes refl        =  ⊢μ (drop ⊢M)
... | no  x≢y         =  ⊢μ (subst ⊢V (swap x≢y ⊢M))


-- Preservation

preserve : ∀ {M N A}
         → ∅ ⊢ M ∶ A
         → M ⟶ N
         ---------------
         → ∅ ⊢ N ∶ A
preserve (⊢L · ⊢M) (ξ-·₁ L⟶L') =  preserve ⊢L L⟶L' · ⊢M
preserve (⊢L · ⊢M) (ξ-·₂ VL M⟶M') =  ⊢L · (preserve ⊢M M⟶M')
preserve (⊢ƛ ⊢N · ⊢V) (β-ƛ VV) =  subst ⊢V  ⊢N
preserve (⊢suc ⊢M) (ξ-suc M⟶M') =  ⊢suc (preserve ⊢M M⟶M')
preserve (⊢case ⊢L ⊢M ⊢N) (ξ-case L⟶L') =  ⊢case (preserve ⊢L L⟶L') ⊢M ⊢N
preserve (⊢case ⊢zero ⊢M ⊢N) β-zero =  ⊢M
preserve (⊢case (⊢suc ⊢V) ⊢M ⊢N) (β-suc x) =  subst ⊢V ⊢N
preserve (⊢μ ⊢M) β-μ =  subst (⊢μ ⊢M) ⊢M


-- Evaluation --
