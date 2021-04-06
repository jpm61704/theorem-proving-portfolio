module properties where

open import lang

open import Data.String using (String ; length ; _++_ ) renaming (_≟_ to _≟string_ )
open import Data.Nat    using (ℕ ; suc ; zero) renaming (_+_ to plus ; _*_ to mult)
open import Data.List using (List ; _∷_ ; [])
open import Data.Product using (Σ-syntax ; _,_) renaming (_×_ to Prod ; proj₁ to fst ; proj₂ to snd)
open import Data.Maybe using (Maybe ; just ; nothing ; _>>=_)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding (subst)

open ≡-Reasoning renaming (_∎ to qed)
open import Data.Empty using (⊥ ; ⊥-elim)


                  --------------------------------------
                  -------------- Progress --------------
                  --------------------------------------

data Progress (e : Expr) : Set where
  step : ∀ {e'}
       → e ⟶ e'
       → Progress e

  done : Value e
       → Progress e



progress : ∀ {e τ}
         → [] ⊢ e ∶ τ
         → Progress e
progress T-num =  done V-num
progress T-str =  done V-str
progress T-unit = done V-unit
progress (T-prod ⊢e₁ ⊢e₂) with progress ⊢e₁
...| step e₁⟶e₁' =  step (ξ₁-prod e₁⟶e₁')
...| done V-e₁ with progress ⊢e₂
...  | step e₂⟶e₂' =  step (ξ₂-prod V-e₁ e₂⟶e₂')
...  | done V-e₂ =  done (V-prod V-e₁ V-e₂)
progress (T-plus ⊢e₁ ⊢e₂) with progress ⊢e₁
...| step e₁⟶e₁' =  step( ξ₁-plus e₁⟶e₁')
...| done V-num with progress ⊢e₂
...  | step e₂⟶e₂' =  step ( ξ₂-plus V-num e₂⟶e₂')
...  | done V-num =  step β-plus
progress (T-times ⊢e₁ ⊢e₂) with progress ⊢e₁
...| step e₁⟶e₁' =  step( ξ₁-times e₁⟶e₁')
...| done V-num with progress ⊢e₂
...  | step e₂⟶e₂' =  step ( ξ₂-times V-num e₂⟶e₂')
...  | done V-num =  step β-times
progress (T-length ⊢e) with progress ⊢e
...| step e⟶e' = step (ξ-length e⟶e')
...| done V-str = step (β-length)
progress (T-concat ⊢e₁ ⊢e₂) with progress ⊢e₁
...| step e₁⟶e₁' =  step ( ξ₁-concat e₁⟶e₁')
...| done V-str with progress ⊢e₂
...  | step e₂⟶e₂' = step (ξ₂-concat V-str e₂⟶e₂')
...  | done V-str   = step β-concat
progress (T-prj₁ ⊢e) with progress ⊢e
...| step e⟶e' =  step ( ξ-prj₁  e⟶e')
...| done (V-prod V-e₁ V-e₂) =  step β-prj₁
progress (T-prj₂ ⊢e) with progress ⊢e
...| step e⟶e' =  step ( ξ-prj₂  e⟶e')
...| done (V-prod V-e₁ V-e₂) =  step β-prj₂
progress (T-inj₁ ⊢e) with progress ⊢e
...| step e⟶e' =  step ( ξ-inj₁ e⟶e')
...| done V-e   =  done (V-inj₁ V-e)
progress (T-inj₂ ⊢e) with progress ⊢e
...| step e⟶e' =  step ( ξ-inj₂ e⟶e')
...| done V-e   =  done (V-inj₂ V-e)
progress (T-let ⊢e₁ ⊢e₂) with progress ⊢e₁
...| step e₁⟶e₁' =  step (ξ-let e₁⟶e₁')
...| done V-e₁    =  step ( β-let V-e₁)
progress (T-case ⊢e ⊢e₁ ⊢e₂) with progress ⊢e
progress (T-case ⊢e ⊢e₁ ⊢e₂) | step e⟶e' =  step ( ξ-case e⟶e')
progress (T-case ⊢e ⊢e₁ ⊢e₂) | done (V-inj₁ V-e) =  step (β-case₁ V-e)
progress (T-case ⊢e ⊢e₁ ⊢e₂) | done (V-inj₂ V-e) =  step (β-case₂ V-e)
progress (T-lam ⊢e)      =  done V-lam
progress (T-app ⊢e₁ ⊢e₂) with progress ⊢e₁
...| step e₁⟶e₁' =  step (ξ₁-app  e₁⟶e₁')
...| done V-e₁ with progress ⊢e₂
...  | step e₂⟶e₂' = step (ξ₂-app V-e₁ e₂⟶e₂')
progress (T-app ⊢e₁ ⊢e₂) | done V-lam | done V-e₂ =  step ( β-lam V-e₂)


                  --------------------------------------
                  ------------ Preservation ------------
                  --------------------------------------

ext : ∀ {Γ Δ}
    → (∀ {x τ} → x ∶ τ ∈ Γ → x ∶ τ ∈ Δ)
    → (∀ {x y τ₁ τ₂} → x ∶ τ₁ ∈ ((y , τ₂) ∷ Γ) → x ∶ τ₁ ∈ ((y , τ₂) ∷ Δ))
ext p here =  here
ext p (there x≠x' ∈Γ) = there x≠x' (p ∈Γ)

rename : ∀ {Γ Δ}
       → (∀ {x τ} → (x ∶ τ ∈ Γ) → (x ∶ τ ∈ Δ))
       → (∀ {e τ} → Γ ⊢ e ∶ τ → Δ ⊢ e ∶ τ)
rename H (T-var ∈Γ) =  T-var (H ∈Γ)
rename H (T-let ⊢e₁ ⊢e₂) =  T-let ( rename H ⊢e₁) ( rename ( ext  H) ⊢e₂)
rename H T-num =  T-num
rename H T-str =  T-str
rename H (T-plus ⊢e₁ ⊢e₂) =  T-plus ( rename H ⊢e₁) ( rename H ⊢e₂)
rename H (T-times ⊢e₁ ⊢e₂) =  T-times (rename H ⊢e₁) (rename H ⊢e₂)
rename H (T-length ⊢e) =  T-length (rename H ⊢e)
rename H (T-concat ⊢e₁ ⊢e₂) =  T-concat (rename H ⊢e₁) (rename H ⊢e₂)
rename H T-unit =  T-unit
rename H (T-prod ⊢e₁ ⊢e₂) =  T-prod (rename H ⊢e₁) (rename H ⊢e₂)
rename H (T-prj₁ ⊢e) =  T-prj₁ (rename H ⊢e)
rename H (T-prj₂ ⊢e) =  T-prj₂ (rename H ⊢e)
rename H (T-inj₁ ⊢e) =  T-inj₁ (rename H ⊢e)
rename H (T-inj₂ ⊢e) =  T-inj₂ (rename H ⊢e)
rename H (T-case ⊢e ⊢e₁ ⊢e₂) =  T-case ( rename H ⊢e) (rename ( ext H) ⊢e₁) (rename (ext H) ⊢e₂)
rename H (T-lam ⊢e) =  T-lam ( rename (ext H) ⊢e)
rename H (T-app ⊢e₁ ⊢e₂) =  T-app (rename H ⊢e₁) (rename H ⊢e₂)

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


-- ≠-sym

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
subst {x = y} ⊢e₁ (T-let {x = x} ⊢e₂ ⊢e₃) with x ≟string y
subst {x = y} ⊢e₁ (T-let {x = x} ⊢e₂ ⊢e₃) | yes refl =  T-let ( subst ⊢e₁ ⊢e₂) ( drop ⊢e₃)
subst {x = y} ⊢e₁ (T-let {x = x} ⊢e₂ ⊢e₃) | no  x≠y  =  T-let ( subst ⊢e₁ ⊢e₂) ( subst  ⊢e₁ (swap  x≠y ⊢e₃))
subst ⊢e₁ T-num =  T-num
subst ⊢e₁ T-str =  T-str
subst ⊢e₁ (T-plus ⊢e₂ ⊢e₃) =  T-plus (subst ⊢e₁ ⊢e₂) (subst ⊢e₁ ⊢e₃)
subst ⊢e₁ (T-times ⊢e₂ ⊢e₃) =  T-times (subst ⊢e₁ ⊢e₂) (subst ⊢e₁ ⊢e₃)
subst ⊢e₁ (T-length ⊢e₂) =  T-length (subst ⊢e₁ ⊢e₂)
subst ⊢e₁ (T-concat ⊢e₂ ⊢e₃) =  T-concat (subst ⊢e₁ ⊢e₂) (subst ⊢e₁ ⊢e₃)
subst ⊢e₁ T-unit =  T-unit
subst ⊢e₁ (T-prod ⊢e₂ ⊢e₃) =  T-prod (subst ⊢e₁ ⊢e₂) (subst ⊢e₁ ⊢e₃)
subst ⊢e₁ (T-prj₁ ⊢e₂) =  T-prj₁ (subst ⊢e₁ ⊢e₂)
subst ⊢e₁ (T-prj₂ ⊢e₂) =  T-prj₂ (subst ⊢e₁ ⊢e₂)
subst ⊢e₁ (T-inj₁ ⊢e₂) =  T-inj₁ (subst ⊢e₁ ⊢e₂)
subst ⊢e₁ (T-inj₂ ⊢e₂) =  T-inj₂ (subst ⊢e₁ ⊢e₂)
subst {x = z} ⊢e' (T-case {x = x} {y = y} ⊢e ⊢e₁ ⊢e₂) with (z ≟string x) , (z ≟string y)
subst {x = z} ⊢e' (T-case {x = x} {y} ⊢e ⊢e₁ ⊢e₂) | yes refl , yes refl =  T-case ( subst ⊢e' ⊢e) ( drop ⊢e₁) ( drop ⊢e₂)
subst {x = z} ⊢e' (T-case {x = x} {y} ⊢e ⊢e₁ ⊢e₂) | yes refl , no z≠y
  =  T-case (subst ⊢e' ⊢e) (drop ⊢e₁) ( subst ⊢e' ( swap ( ≢-sym  z≠y ) ⊢e₂))
subst {x = z} ⊢e' (T-case {x = x} {y} ⊢e ⊢e₁ ⊢e₂) | no z≠x  , yes refl
  =  T-case (subst ⊢e' ⊢e) (subst ⊢e' (swap ( (≢-sym z≠x))  ⊢e₁)) (drop ⊢e₂)
subst {x = z} ⊢e' (T-case {x = x} {y} ⊢e ⊢e₁ ⊢e₂) | no z≠x , no z≠y
  =  T-case (subst ⊢e' ⊢e) (subst ⊢e' (swap ( (≢-sym z≠x))  ⊢e₁))  ( subst ⊢e' ( swap ( ≢-sym  z≠y ) ⊢e₂))
subst {x = y} ⊢e' (T-lam {x = x} ⊢e) with y ≟string x
...| yes refl =  T-lam ( drop ⊢e)
...| no y≠x  =  T-lam ( subst  ⊢e' ( swap ( ≢-sym y≠x) ⊢e))
subst ⊢e' (T-app ⊢e₁ ⊢e₂) =  T-app (subst ⊢e' ⊢e₁) (subst ⊢e' ⊢e₂)

preserve : ∀ {e e' τ}
         → [] ⊢ e ∶ τ
         → e ⟶ e'
         → [] ⊢ e' ∶ τ
preserve (T-plus ⊢e₁ ⊢e₂) (ξ₁-plus e₁⟶e₁') with preserve ⊢e₁ e₁⟶e₁'
...| ⊢e₁' =  T-plus ⊢e₁' ⊢e₂
preserve (T-plus ⊢e₁ ⊢e₂) (ξ₂-plus V-e₁ e₂⟶e₂') with preserve ⊢e₂ e₂⟶e₂'
...| ⊢e₂' =  T-plus ⊢e₁ ⊢e₂'
preserve (T-plus ⊢e₁ ⊢e₂) β-plus = T-num
preserve (T-times ⊢e₁ ⊢e₂) (ξ₁-times e₁⟶e₁') with preserve ⊢e₁ e₁⟶e₁'
...| ⊢e₁' =  T-times ⊢e₁' ⊢e₂
preserve (T-times ⊢e₁ ⊢e₂) (ξ₂-times V-e₁ e₂⟶e₂') with preserve ⊢e₂ e₂⟶e₂'
...| ⊢e₂' =  T-times ⊢e₁ ⊢e₂'
preserve (T-times ⊢e₁ ⊢e₂) β-times = T-num
preserve (T-length ⊢e) (ξ-length e⟶e') with preserve ⊢e e⟶e'
...| ⊢e' =  T-length ⊢e'
preserve (T-length ⊢e) β-length = T-num
preserve (T-concat ⊢e₁ ⊢e₂) (ξ₁-concat e₁⟶e₁') with preserve ⊢e₁ e₁⟶e₁'
...| ⊢e₁' =  T-concat ⊢e₁' ⊢e₂
preserve (T-concat ⊢e₁ ⊢e₂) (ξ₂-concat V-e₁ e₂⟶e₂') with preserve ⊢e₂ e₂⟶e₂'
...| ⊢e₂' =  T-concat ⊢e₁ ⊢e₂'
preserve (T-concat ⊢e₁ ⊢e₂) β-concat = T-str
preserve (T-prod ⊢e₁ ⊢e₂) (ξ₁-prod e₁⟶e₁' ) = T-prod (preserve ⊢e₁ e₁⟶e₁') ⊢e₂
preserve (T-prod ⊢e₁ ⊢e₂) (ξ₂-prod V-e₁ e₂⟶e₂' ) = T-prod ⊢e₁ (preserve ⊢e₂ e₂⟶e₂')
preserve (T-prj₁ ⊢e) (ξ-prj₁ e⟶e') = T-prj₁ (preserve ⊢e  e⟶e')
preserve (T-prj₁ (T-prod ⊢e₁ ⊢e₂)) β-prj₁ = ⊢e₁
preserve (T-prj₂ ⊢e) (ξ-prj₂ e⟶e') = T-prj₂ (preserve ⊢e  e⟶e')
preserve (T-prj₂ (T-prod ⊢e₁ ⊢e₂)) β-prj₂ = ⊢e₂
preserve (T-inj₁ ⊢e) (ξ-inj₁ e⟶e') = T-inj₁ (preserve ⊢e e⟶e' )
preserve (T-inj₂ ⊢e) (ξ-inj₂ e⟶e') =  T-inj₂ (preserve ⊢e e⟶e')
preserve (T-let ⊢e₁ ⊢e₂) (ξ-let e₁⟶e₁') = T-let (preserve ⊢e₁ e₁⟶e₁') ⊢e₂
preserve (T-let ⊢e₁ ⊢e₂) (β-let V-e₁) = subst ⊢e₁ ⊢e₂
preserve (T-case ⊢e ⊢e₁ ⊢e₂) (ξ-case e⟶e') = T-case ( preserve ⊢e e⟶e') ⊢e₁ ⊢e₂
preserve (T-case (T-inj₁ ⊢e) ⊢e₁ ⊢e₂) (β-case₁ V-e) = subst  ⊢e  ⊢e₁
preserve (T-case (T-inj₂ ⊢e) ⊢e₁ ⊢e₂) (β-case₂ V-e) = subst  ⊢e  ⊢e₂
preserve (T-app ⊢e₁ ⊢e₂) (ξ₁-app e₁⟶e₁') =  T-app ( preserve  ⊢e₁  e₁⟶e₁')  ⊢e₂
preserve (T-app ⊢e₁ ⊢e₂) (ξ₂-app V-e₁ e₂⟶e₂') =  T-app  ⊢e₁ ( preserve  ⊢e₂  e₂⟶e₂')
preserve (T-app (T-lam ⊢e₁) ⊢e₂) (β-lam V-e₂) = subst ⊢e₂ ⊢e₁


--------------------------------------------------------------------------------
-------------------------------- Evaluation-------------------------------------
--------------------------------------------------------------------------------


data Gas : Set where
  gas : ℕ → Gas


data Finished (e : Expr) : Set where
  done : Value e
       → Finished e

  out-of-gas : Finished e

data Steps (e : Expr) : Set where
  steps : ∀ {e'}
        → e ↠ e'
        → Finished e'
        → Steps e


eval : ∀ {e τ}
     → Gas
     → [] ⊢ e ∶ τ
     → Steps e
eval {e} (gas zero) ⊢e =  steps ( e ∎) out-of-gas
eval {e} (gas (suc x)) ⊢e with progress ⊢e
...| done V-e   =  steps (e ∎) (done V-e)
...| step e⟶e' with eval (gas x) (preserve ⊢e e⟶e')
...  | steps e↠f fin =  steps (e ⟶⟨ e⟶e' ⟩ e↠f) fin


--------------------------------------------------------------------------------
------------------------------------ Tests -------------------------------------
--------------------------------------------------------------------------------

--------------------------------------
--------- Arithmetic Tests -----------
--------------------------------------


ex1 : Expr
ex1 = num[ 5 ] + num[ 6 ] + num[ 9 ]

t1 : Maybe ([] ⊢ ex1 ∶ num)
t1 = typecheck [] ex1 num

eval1 : Maybe (Steps ex1)
eval1 = t1 >>= λ ⊢ex1 → just (eval (gas 15) ⊢ex1)

--------------------------------------
----------- String Length ------------
--------------------------------------

ex2 : Expr
ex2 = ∣ str[ "hello world" ] ∣

eval2 : Maybe (Steps ex2)
eval2 = typecheck [] ex2 num >>= λ ⊢ex2 → just (eval (gas 15) ⊢ex2)

--------------------------------------
------------ String Concat -----------
--------------------------------------

ex3 : Expr
ex3 = str[ "012345" ] ^ str["56789"]

eval3 : Maybe (Steps ex3)
eval3 = typecheck [] ex3 str >>= λ ⊢ex3 → just (eval (gas 15) ⊢ex3)


--------------------------------------
-------------- Products --------------
--------------------------------------

ex4 : Expr
ex4 = (prj₁ ⟨ num[ 123 ] , str[ "012345" ] ^ str["56789"] ⟩) + num[ 123 ]

eval4 : Maybe (Steps ex4)
eval4 = typeinfer [] ex4 >>= λ ⊢ex4 → just (eval (gas 15) ( snd ⊢ex4))


--------------------------------------
---------------- Sums ----------------
--------------------------------------
