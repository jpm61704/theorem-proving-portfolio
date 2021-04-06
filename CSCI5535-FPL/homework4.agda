module homework4 where

-- open import lang

open import Data.String using (String ; length ; _++_ ) renaming (_≟_ to _≟string_ )
open import Data.Nat    using (ℕ ; suc ; zero) renaming (_+_ to plus ; _*_ to mult)
-- open import Data.List using (List ; _∷_ ; [])
open import Data.Product using (Σ-syntax ; _,_) renaming (_×_ to Prod ; proj₁ to fst ; proj₂ to snd)
open import Data.Maybe using (Maybe ; just ; nothing ; _>>=_)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding (subst; [_])
open import Data.List using (List; _∷_; [])

open ≡-Reasoning renaming (_∎ to qed)
open import Data.Empty using (⊥ ; ⊥-elim)

Name : Set
Name = String

data Type : Set where
  num  : Type
  _⇒_ : Type → Type → Type


data Expr : Set where
  [_]  : Name → Expr
  zero : Expr
  suc  : Expr → Expr
  ifz_[z↪_|s_↪_] : Expr → Expr → Name → Expr → Expr

  ƛ_∶_⇒_ : Name → Type → Expr → Expr
  _·_ : Expr → Expr → Expr
  fix_∶_is_ : Name → Type → Expr → Expr


data Frame : (Expr → Expr) → Set where
  F-suc : Frame (λ e → suc e)
  F-ifz : (eₒ : Expr) → (e₁ : Expr) → (x : Name) → Frame (λ e → ifz e [z↪ eₒ |s x ↪ e₁ ] )
  F-app : (e₂ : Expr )  → Frame (λ e₁ → e₁ · e₂)


-- Stack : Set
-- Stack = List (Σ[ e ∈ (Expr → Expr) ] Frame e)

data Stack : Set where
  []  : Stack
  _∷_ : ∀ {e} → Frame e → Stack → Stack

infix 7 _◃_
infix 7 _▹_

data State : Set where
  -- return states
  _◃_ : Stack → Expr → State
  -- evaluation state
  _▹_ : Stack → Expr → State


[_/_]_ : Expr → Name → Expr → Expr
[ e' / x ] [ x₁ ] with x ≟string x₁
...| yes _ =  e'
...| no _ =  [ x₁ ]
[ e' / x ] zero = zero
[ e' / x ] (suc e) = suc ([ e' / x ] e)
([ e' / x ] (ƛ y ∶ τ ⇒ e)) with x ≟string y
...| yes x≡y =  ƛ y ∶ τ ⇒ e
...| no x≠y  =  ƛ y ∶ τ ⇒ ([ e' / x ] e)
([ e' / x ] (e₁ · e₂)) =  ([ e' / x ] e₁) · ([ e' / x ] e₂)
[ e' / x ] (fix y ∶ τ is e) with (y ≟string x)
...| yes y≡x =  fix y ∶ τ is e
...| no  y≠x =  fix y ∶ τ is ([ e' / x ] e)
[ eᵣ / x ] ifz e [z↪ e₁ |s y ↪ e₂ ] with y ≟string x | [ eᵣ / x ] e | [ eᵣ / x ] e₁ | [ eᵣ / x ] e₂
...| yes p | e' | e₁' | _   =  ifz e' [z↪ e₁' |s y ↪ e₂  ]
...| no ¬p | e' | e₁' | e₂' =  ifz e' [z↪ e₁' |s y ↪ e₂' ]


infix 4 _↦_

data _↦_ : State → State → Set where
  ε-zero : ∀ {k}
         ---------------------------
         → k ▹ zero ↦ k ◃ zero

  ε-suc : ∀ {e k}
         ----------------------------------
         → k ▹ suc e ↦ ( F-suc ∷ k) ▹ e

  ρ-suc : ∀ {e k}
        ----------------------------------
        → (F-suc ∷ k) ◃ e ↦ k ◃ suc e

  ε-ifz : ∀ {k e e₀ e₁ x}
        --------------------------------------------------------------
        → k ▹ ifz e [z↪ e₀ |s x ↪ e₁ ] ↦ (F-ifz e₀ e₁ x ∷ k) ▹ e

  ρ-ifz₁ : ∀ {k e₀ e₁ x}
         -------------------------------------------
         → ( F-ifz e₀ e₁ x ∷ k) ◃ zero ↦ k ▹ e₀

  ρ-ifz₂ : ∀ {k e₀ e₁ x e}
         -------------------------------------------
         → ( F-ifz e₀ e₁ x ∷ k) ◃ suc e ↦ k ▹ [ e / x ] e₁

  ε-lam : ∀ {k x τ e}
        ---------------------------------------------
        → k ▹ ƛ x ∶ τ ⇒ e ↦ k ◃ ƛ x ∶ τ ⇒ e

  ε-ap : ∀ {k e₁ e₂}
       ------------------------------------------------
       → k ▹ e₁ · e₂ ↦ ( F-app e₂ ∷ k) ▹ e₁

  ρ-ap : ∀ {k e₂ τ x e}
       --------------------------------------------------------
       → ( F-app e₂ ∷ k ) ◃ ƛ x ∶ τ ⇒ e ↦ k ▹ [ e₂ / x ] e

  ε-fix : ∀ {k τ x e}
        --------------------------------------------------------
        → k ▹ fix x ∶ τ is e ↦ k ▹ [ fix x ∶ τ is e / x ] e


data Value : Expr → Set where
  V-zero : Value zero
  V-suc : ∀ {e} → Value e
        → Value (suc e)
  V-lam  : ∀ {x τ e}
         → Value (ƛ x ∶ τ ⇒ e)



data Initial : State → Set where
  init : ∀ {e} → Initial ([] ▹ e)

data Final : State → Set where
  fin : ∀ {e} → Value e
      → Final ([] ◃ e)


Context : Set
Context = List (Prod Name Type)

data _∶_∈_ : Name → Type → Context → Set where
  here : ∀ {x τ Γ}
       --------------------------------
       → x ∶ τ ∈ ((x , τ) ∷ Γ)

  there : ∀ {x y τ τ₂ Γ}
        → x ≢ y
        → x ∶ τ ∈ Γ
        -----------------------------
        → x ∶ τ ∈ ((y , τ₂) ∷ Γ)




data _⊢_∶_ : Context → Expr → Type → Set where
  T-var : ∀ {Γ x τ}
        → x ∶ τ ∈ Γ
        -------------------
        → Γ ⊢ [ x ] ∶ τ

  T-zero : ∀ {Γ}
        ----------------------
         → Γ ⊢ zero ∶ num

  T-suc : ∀ {Γ n}
        → Γ ⊢ n ∶ num
        --------------------
        → Γ ⊢ suc n ∶ num


  T-lam : ∀ {Γ x τ₁ τ₂ e}
        → ((x , τ₁) ∷ Γ) ⊢ e ∶ τ₂
        -------------------------------------
        → Γ ⊢ (ƛ x ∶ τ₁ ⇒ e) ∶ (τ₁ ⇒ τ₂)

  T-app : ∀ {Γ e₁ e₂ τ₁ τ₂}
        → Γ ⊢ e₁ ∶ (τ₁ ⇒ τ₂)
        → Γ ⊢ e₂ ∶ τ₁
        ---------------------------
        → Γ ⊢ e₁ · e₂ ∶ τ₂

  T-fix : ∀{Γ x τ e}
        → ((x , τ) ∷ Γ) ⊢ e ∶ τ
        -----------------------------
        → Γ ⊢ (fix x ∶ τ is e) ∶ τ

  T-ifz : ∀ {Γ e e₁ e₂ x τ}
        → Γ ⊢ e ∶ num
        → Γ ⊢ e₁ ∶ τ
        → ((x , num) ∷ Γ) ⊢ e₂ ∶ τ
        ------------------------------------------
        → Γ ⊢ (ifz e [z↪ e₁ |s x ↪ e₂ ]) ∶ τ



{-
The auxiliary judgement for type-expectation. It states that a frame f
transforms the value of type t into the type t'
-}
data _∶_↠_ : ∀ {e} → (Frame e) → Type → Type → Set where
  t-suc : F-suc ∶ num ↠ num

  t-ifz : ∀ {e₀ e₁ x τ}
        → [] ⊢ e₀ ∶ τ
        → ((x , num) ∷ []) ⊢ e₁ ∶ τ
        --------------------------------
        → F-ifz e₀ e₁ x ∶ num ↠ τ

  t-ap : ∀ {e₂ τ₂ τ}
       → [] ⊢ e₂ ∶ τ₂
       ---------------------------------
       → F-app e₂ ∶ τ₂ ⇒ τ ↠ τ

{-
Type Expectation

the stack k is expecting the type τ
-}
data _◃∶_ : Stack → Type → Set where
  TE-init : ∀ {τ}
          -----------
          → [] ◃∶ τ

  TE-frame : ∀ {k τ τ' e} {f : Frame e}
           → k ◃∶ τ'
           → (f ∶ τ ↠ τ')
           ------------------
           → (f ∷ k) ◃∶ τ

data Ok : State → Set where
  eval-ok : ∀ {k τ e}
          → k ◃∶ τ
          → [] ⊢ e ∶ τ
          -----------------
          → Ok (k ▹ e)

  return-ok : ∀ {k τ e}
            → k ◃∶ τ
            → [] ⊢ e ∶ τ
            → Value e
            ----------------
            → Ok (k ◃ e)


------------------------------------------------------------
------------------------ Progress --------------------------
------------------------------------------------------------

data Progress (s : State) : Set where
  step : ∀ {s'}
       → s ↦ s'
       → Progress s

  done : Final s
       → Progress s

progress : ∀ {s} → Ok s → Progress s
progress (eval-ok ◃τ T-zero)          =  step ε-zero
progress (eval-ok ◃τ (T-suc ⊢e))     =  step ε-suc
progress (eval-ok ◃τ (T-lam ⊢e))     =  step ε-lam
progress (eval-ok ◃τ (T-app ⊢e ⊢e₁)) =  step ε-ap
progress (eval-ok ◃τ (T-fix ⊢e))     =  step ε-fix
progress (eval-ok x (T-ifz x₁ x₂ x₃)) =  step ε-ifz
progress (return-ok {k = []} ◃τ ⊢e V-e) =  done (fin V-e)
progress (return-ok {k = F-suc ∷ k} ◃τ ⊢e V-e) =  step ρ-suc
progress (return-ok {k = F-ifz eₒ e₁ x ∷ k} (TE-frame ◃τ (t-ifz ⊢e₀ ⊢e₁)) ⊢e V-zero) =  step ρ-ifz₁
progress (return-ok {k = F-ifz eₒ e₁ x ∷ k} (TE-frame ◃τ (t-ifz x₁ x₂)) ⊢e (V-suc V-e)) =  step ρ-ifz₂
progress (return-ok {k = F-app e₂ ∷ k} (TE-frame ◃τ (t-ap x)) ⊢e V-lam) = step ρ-ap


------------------------------------------------------------
---------------------- Preservation ------------------------
------------------------------------------------------------

ext : ∀ {Γ Δ}
    → (∀ {x τ} → x ∶ τ ∈ Γ → x ∶ τ ∈ Δ)
    → (∀ {x y τ₁ τ₂} → x ∶ τ₁ ∈ ((y , τ₂) ∷ Γ) → x ∶ τ₁ ∈ ((y , τ₂) ∷ Δ))
ext p here =  here
ext p (there x≠x' ∈Γ) = there x≠x' (p ∈Γ)

rename : ∀ {Γ Δ}
       → (∀ {x τ} → (x ∶ τ ∈ Γ) → (x ∶ τ ∈ Δ))
       → (∀ {e τ} → Γ ⊢ e ∶ τ → Δ ⊢ e ∶ τ)
rename H (T-var ∈Γ) =  T-var (H ∈Γ)
rename H (T-lam ⊢e) =  T-lam ( rename (ext H) ⊢e)
rename H (T-app ⊢e₁ ⊢e₂) =  T-app (rename H ⊢e₁) (rename H ⊢e₂)
rename H (T-fix ⊢e) =  T-fix ( rename ( ext H) ⊢e)
rename H T-zero           =  T-zero
rename H (T-suc x₁)       =  T-suc ( rename H x₁)
rename H (T-ifz x₁ x₂ x₃) =  T-ifz (rename H x₁) ( rename H x₂) ( rename (ext H) x₃)

weaken : ∀ {Γ e τ}
       → [] ⊢ e ∶ τ
       → Γ ⊢ e ∶ τ
weaken {Γ} ⊢e =  rename ( λ ()) ⊢e

drop : ∀ {Γ x e τ₁ τ₂ τ₃}
     → ((x , τ₂) ∷ (x , τ₁) ∷ Γ) ⊢ e ∶ τ₃
     → ((x , τ₂) ∷ Γ) ⊢ e ∶ τ₃
drop {Γ} {x} {e} {τ₁} {τ₂} {τ₃} ⊢e =  rename  dropMemberLemma ⊢e
  where dropMemberLemma : ∀ {y τ₃}
                        → y ∶ τ₃ ∈ ((x , τ₂) ∷ (x , τ₁) ∷ Γ)
                        → y ∶ τ₃ ∈ ((x , τ₂) ∷ Γ)
        dropMemberLemma here =  here
        dropMemberLemma (there x≠x' here) =  ⊥-elim (x≠x' refl)
        dropMemberLemma (there x≠x' (there x ∈Γ)) =  there x≠x' ∈Γ


swap : ∀ {Γ x y e τ₁ τ₂ τ₃}
     → x ≢ y
     → ((x , τ₁) ∷ (y , τ₂) ∷ Γ ) ⊢ e ∶ τ₃
     → ((y , τ₂) ∷ (x , τ₁) ∷ Γ ) ⊢ e ∶ τ₃
swap {Γ} {x} {y} {e} {τ₁} {τ₂} {τ₃} x≠y ⊢e =  rename  swapMemberLemma ⊢e
  where swapMemberLemma : {x = x₁ : String} {τ : Type}
                        →  x₁ ∶ τ ∈ ((x , τ₁) ∷ (y , τ₂) ∷ Γ)
                        → x₁ ∶ τ ∈ ((y , τ₂) ∷ (x , τ₁) ∷ Γ)
        swapMemberLemma here = there x≠y here
        swapMemberLemma (there x here) = here
        swapMemberLemma (there x₂≠x₃ (there x₂≠y c))
                               = there x₂≠y ( there x₂≠x₃ c)




subst : ∀ {Γ x e₁ e₂ τ₁ τ₂}
      → [] ⊢ e₁ ∶ τ₁
      → ((x , τ₁) ∷ Γ) ⊢ e₂ ∶ τ₂
      → Γ ⊢ [ e₁ / x ] e₂ ∶ τ₂
subst {x = x} ⊢e₁ (T-var here) with x ≟string x
subst {x = x} ⊢e₁ (T-var here) | yes p =  weaken ⊢e₁
subst {x = x} ⊢e₁ (T-var here) | no ¬p =  ⊥-elim ( ¬p refl)
subst {x = y} ⊢e₁ (T-var (there {x₁} x x∈Γ)) with y ≟string x₁
subst {x = y} ⊢e₁ (T-var (there {_} x₁≠y x∈Γ)) | yes p =  ⊥-elim ( x₁≠y ( sym p) )
subst {x = y} ⊢e₁ (T-var (there {_} x x∈Γ)) | no y≠x₁ =  T-var x∈Γ
subst {x = y} ⊢e' (T-lam {x = x} ⊢e) with y ≟string x
...| yes refl =  T-lam ( drop ⊢e)
...| no y≠x  =  T-lam ( subst  ⊢e' ( swap ( ≢-sym y≠x) ⊢e))
subst ⊢e' (T-app ⊢e₁ ⊢e₂) =  T-app (subst ⊢e' ⊢e₁) (subst ⊢e' ⊢e₂)
subst {x = y} ⊢e' (T-fix {x = x} ⊢e) with x ≟string y
subst {x = y} ⊢e' (T-fix {x = x} ⊢e) | yes refl =  T-fix ( drop ⊢e)
subst {x = y} ⊢e' (T-fix {x = x} ⊢e) | no x≠y =  T-fix ( subst  ⊢e' ( swap x≠y ⊢e))
subst ⊢e' T-zero = T-zero
subst ⊢e' (T-suc x₁) =  T-suc ( subst ⊢e' x₁)
subst {x = y} ⊢e' (T-ifz {x = x} ⊢e ⊢e₃ ⊢e₂) with x ≟string y
...| yes refl =  T-ifz ( subst ⊢e' ⊢e) ( subst ⊢e' ⊢e₃) ( drop ⊢e₂ )
...| no ¬p =  T-ifz ( subst ⊢e' ⊢e) ( subst ⊢e' ⊢e₃) ( subst  ⊢e' ( swap ¬p ⊢e₂))



preserve : ∀ {s s'}
         → Ok s
         → s ↦ s'
         → Ok s'
preserve (eval-ok ◃τ ⊢e) ε-zero        = return-ok ◃τ ⊢e V-zero
preserve (eval-ok ◃τ (T-suc ⊢e)) ε-suc = eval-ok ( TE-frame ◃τ t-suc) ⊢e
preserve (eval-ok ◃τ ⊢e) ε-lam         =  return-ok ◃τ ⊢e V-lam
preserve (eval-ok ◃τ (T-app ⊢e₁ ⊢e₂)) ε-ap = eval-ok ( TE-frame ◃τ (t-ap ⊢e₂)) ⊢e₁
preserve (eval-ok ◃τ (T-fix ⊢e)) ε-fix =  eval-ok ◃τ ( subst ( T-fix ⊢e )  ⊢e )
preserve (eval-ok ◃τ (T-ifz ⊢e ⊢e₁ ⊢e₂)) ε-ifz = eval-ok ( TE-frame ◃τ ( t-ifz ⊢e₁ ⊢e₂) ) ⊢e
preserve (return-ok (TE-frame ◃τ t-suc) ⊢e V-e) ρ-suc =  return-ok ◃τ (T-suc ⊢e) (V-suc V-e)
preserve (return-ok (TE-frame ◃τ (t-ifz ⊢e₀ ⊢e₁)) ⊢e V-e) ρ-ifz₁ =  eval-ok ◃τ  ⊢e₀
preserve (return-ok (TE-frame ◃τ (t-ifz ⊢e₀ ⊢e₁)) (T-suc ⊢e) V-e) ρ-ifz₂ = eval-ok ◃τ (subst  ⊢e ⊢e₁)
preserve (return-ok (TE-frame ◃τ (t-ap ⊢e₂)) (T-lam ⊢e) V-e) ρ-ap =  eval-ok ◃τ ( subst  ⊢e₂  ⊢e)



--------------------------------------------------------------------------------
-------------------------------- Evaluation-------------------------------------
--------------------------------------------------------------------------------



infix 2 _⟶_
infix 2 _⟶⟨_⟩_
infix 3 _∎

data _⟶_ : State → State → Set where
  _∎ : ∀ M → M ⟶ M
  _⟶⟨_⟩_ : ∀ L { M N }
         → L ↦ M
         → M ⟶ N
         → L ⟶ N




data Gas : Set where
  gas : ℕ → Gas

data Finished (e : State) : Set where
  done : Final e
       → Finished e

  out-of-gas : Finished e

data Steps (e : State) : Set where
  steps : ∀ {e'}
        → e ⟶ e'
        → Finished e'
        → Steps e


eval : ∀ {e}
     → Gas
     → Ok e
     → Steps e
eval {e} (gas zero) e-ok =  steps ( e ∎) out-of-gas
eval {e} (gas (suc x)) ⊢e with progress ⊢e
...| done V-e   =  steps (e ∎) (done V-e)
...| step e↦e' with eval (gas x) (preserve ⊢e e↦e')
...  | steps e⟶f d =  steps ( (  e ⟶⟨  e↦e' ⟩  e⟶f) )  d

