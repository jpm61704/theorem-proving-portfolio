module lang where

module homework2 where

open import Data.String using (String ; length ; _++_ ) renaming (_≟_ to _≟string_ )
open import Data.Nat    using (ℕ ; suc ; zero) renaming (_+_ to plus ; _*_ to mult)
open import Data.List using (List ; _∷_ ; [])
open import Data.Product using (Σ-syntax ; _,_) renaming (_×_ to Prod ; proj₁ to fst ; proj₂ to snd)
open import Data.Maybe using (Maybe ; just ; nothing ; _>>=_)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding (subst)

open ≡-Reasoning renaming (_∎ to qed)
open import Data.Empty using (⊥ ; ⊥-elim)


--------------------------------------------------------------------------------
--------------------------------- Statics --------------------------------------
--------------------------------------------------------------------------------




                   --------------------------------------
                   -------------- Syntax ----------------
                   --------------------------------------

Name : Set
Name = String

infixl 7 _⊗_
infixl 6 _⊕_

data Type : Set where
  num  : Type
  str  : Type
  _⇒_ : Type → Type → Type
  unit : Type
  _⊗_  : Type → Type → Type
  -- void : Type
  _⊕_ : Type → Type → Type

infixl 6 _+_
infixl 7 _×_
infixl 7 _^_
infix 10 let[_:=_]_

data Expr : Set where

  -- System E

    -- Variables
  [_]    : Name → Expr

    -- Primitives
  num[_] : ℕ → Expr
  str[_] : String → Expr

    -- Arithmetic Operatoenotation Semantics of IMPrs
  _+_    : Expr → Expr → Expr
  _×_    : Expr → Expr → Expr

    -- String Operators
  _^_    : Expr → Expr → Expr
  ∣_∣     : Expr → Expr

    -- Let Binding
  let[_:=_]_ : Name → Expr → Expr → Expr

  -- System T

    -- Lambda Abstraction
  ƛ_∶_↦_ : Name → Type → Expr → Expr

    -- Application
  _∙_     : Expr → Expr → Expr

  -- System P

  ⟨⟩ : Expr
  ⟨_,_⟩ : Expr → Expr → Expr
  prj₁ : Expr → Expr
  prj₂ : Expr → Expr

  -- System S

  -- abort : Expr → Expr
  inj₁⟦_,_⟧ : Type → Type → Expr → Expr
  inj₂⟦_,_⟧ : Type → Type → Expr → Expr
  case_[left_↦_,right_↦_] : Expr → Name → Expr → Name → Expr → Expr


                    --------------------------------------
                    ----------- Type Checking ------------
                    --------------------------------------

postulate impossible : ⊥

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

_∈?_ : (x : Name) → (Γ : Context) → Dec (Σ[ τ ∈ Type ] x ∶ τ ∈ Γ)
x ∈? [] =  no λ ()
x ∈? ( (x' , τ) ∷ Γ) with x ≟string x'
...| yes refl =  yes (  τ ,  here )
...| no x≠x' with x ∈? Γ
...  | yes (τ' , prf ) =  yes (  τ' , there x≠x' prf)
...  | no ¬p =  no  λ x → impossible

data _⊢_∶_ : Context → Expr → Type → Set where
  T-var : ∀ {Γ x τ}
        → x ∶ τ ∈ Γ
        -------------------
        → Γ ⊢ [ x ] ∶ τ

  T-let : ∀ {Γ e₁ e₂ x τ₁ τ₂}
        → Γ ⊢ e₁ ∶ τ₁
        → ((x , τ₁) ∷ Γ) ⊢ e₂ ∶ τ₂
        ------------------------------------
        → Γ ⊢ (let[ x := e₁ ] e₂) ∶ τ₂

  T-num : ∀ {Γ n} →
        -------------------
        Γ ⊢ num[ n ] ∶ num

  T-str : ∀ {Γ n} →
        -------------------
        Γ ⊢ str[ n ] ∶ str

  T-plus : ∀ {Γ e₁ e₂}
         → Γ ⊢ e₁ ∶ num
         → Γ ⊢ e₂ ∶ num
         --------------------
         → Γ ⊢ e₁ + e₂ ∶ num

  T-times : ∀ {Γ e₁ e₂}
          → Γ ⊢ e₁ ∶ num
          → Γ ⊢ e₂ ∶ num
          --------------------
          → Γ ⊢ e₁ × e₂ ∶ num

  T-length : ∀ {Γ e}
           → Γ ⊢ e ∶ str
           ---------------------
           → Γ ⊢ ∣ e ∣ ∶ num


  T-concat : ∀ {Γ e₁ e₂}
           → Γ ⊢ e₁ ∶ str
           → Γ ⊢ e₂ ∶ str
           --------------------
           → Γ ⊢ e₁ ^ e₂ ∶ str

  T-unit : ∀ {Γ}
         ----------------------
         → Γ ⊢ ⟨⟩ ∶ unit

  T-prod : ∀ {Γ e₁ e₂} {τ₁ τ₂}
         → Γ ⊢ e₁ ∶ τ₁
         → Γ ⊢ e₂ ∶ τ₂
         ----------------------
         → Γ ⊢ ⟨ e₁ , e₂ ⟩ ∶ (τ₁ ⊗ τ₂)

  T-prj₁ : ∀ {Γ e τ₁ τ₂}
        → Γ ⊢ e ∶ (τ₁ ⊗ τ₂)
        -------------------------------
        → Γ ⊢ prj₁ e ∶ τ₁

  T-prj₂ : ∀ {Γ e τ₁ τ₂}
         → Γ ⊢ e ∶ (τ₁ ⊗ τ₂)
         -------------------------------
         → Γ ⊢ prj₂ e ∶ τ₂

  T-inj₁ : ∀ {Γ e τ₁ τ₂}
         → Γ ⊢ e ∶ τ₁
         --------------------------
         → Γ ⊢ inj₁⟦ τ₁ , τ₂ ⟧ e ∶ (τ₁ ⊕ τ₂)

  T-inj₂ : ∀ {Γ e τ₁ τ₂}
         → Γ ⊢ e ∶ τ₂
         --------------------------
         → Γ ⊢ inj₂⟦ τ₁ , τ₂ ⟧ e ∶ (τ₁ ⊕ τ₂)

  T-case : ∀ {Γ τ τ₁ τ₂ e e₁ e₂ x y}
         → Γ ⊢ e ∶ (τ₁ ⊕ τ₂)
         → ((x , τ₁) ∷ Γ) ⊢ e₁ ∶ τ
         → ((y , τ₂) ∷ Γ) ⊢ e₂ ∶ τ
         --------------------------------------------------
         → Γ ⊢ case e [left x ↦ e₁ ,right y ↦ e₂ ] ∶ τ

  T-lam : ∀ {Γ x τ₁ τ₂ e}
           → ((x , τ₁) ∷ Γ) ⊢ e ∶ τ₂
           -------------------------------------
           → Γ ⊢ (ƛ x ∶ τ₁ ↦ e) ∶ (τ₁ ⇒ τ₂)

  T-app : ∀ {Γ e₁ e₂ τ₁ τ₂}
        → Γ ⊢ e₁ ∶ (τ₁ ⇒ τ₂)
        → Γ ⊢ e₂ ∶ τ₁
        ---------------------------
        → Γ ⊢ e₁ ∙ e₂ ∶ τ₂


_≟_ : ∀ (τ₁ τ₂ : Type) → Dec (τ₁ ≡ τ₂)
num ≟ num = yes refl
str ≟ str = yes refl
unit ≟ unit =  yes refl
(t1 ⊗ t3) ≟ (t2 ⊗ t4) with t1 ≟ t2 , t3 ≟ t4
...| yes refl , yes refl =  yes refl
{-# CATCHALL #-}
...| p , ¬p =  no λ x → impossible
(t1 ⊕ t2) ≟ (t3 ⊕ t4) with t1 ≟ t3 , t2 ≟ t4
...| yes refl , yes refl =  yes refl
{-# CATCHALL #-}
...| p , ¬p =  no λ x → impossible
{-# CATCHALL #-}
_ ≟ _ =  no  λ x → impossible



typecheck : (Γ : Context) → (e : Expr) → (τ : Type) → Maybe (Γ ⊢ e ∶ τ)
typeinfer : (Γ : Context) → (e : Expr) → Maybe (Σ[ τ ∈ Type ] Γ ⊢ e ∶ τ)

typeinfer Γ [ x ] with x ∈? Γ
typeinfer Γ [ x ] | yes (τ , ∈Γ) =  just (  τ ,  T-var ∈Γ)
...| no ¬p =  nothing
typeinfer Γ num[ x ] = just (num , T-num)
typeinfer Γ str[ x ] =  just (str , T-str)

typeinfer Γ (let[ x := e₁ ] e₂) with typeinfer Γ e₁
typeinfer Γ (let[ x := e₁ ] e₂) | nothing =  nothing
typeinfer Γ (let[ x := e₁ ] e₂) | just (τ₁ , ⊢e₁) with typeinfer ((x , τ₁) ∷ Γ) e₂
typeinfer Γ (let[ x := e₁ ] e₂) | just (τ₁ , ⊢e₁) | nothing =  nothing
typeinfer Γ (let[ x := e₁ ] e₂) | just (τ₁ , ⊢e₁) | just (τ₂ , ⊢e₂) =  just (  τ₂ ,  T-let  ⊢e₁  ⊢e₂)

typeinfer Γ (e₁ + e₂) = typecheck Γ e₁ num >>=
             λ ⊢e₁ → typecheck Γ e₂ num >>=
             λ ⊢e₂ → just (num , T-plus ⊢e₁ ⊢e₂)
typeinfer Γ (e₁ × e₂) = typecheck Γ e₁ num >>=
             λ ⊢e₁ → typecheck Γ e₂ num >>=
             λ ⊢e₂ → just (num , T-times ⊢e₁ ⊢e₂)
typeinfer Γ (e₁ ^ e₂) = typecheck Γ e₁ str >>=
             λ ⊢e₁ → typecheck Γ e₂ str >>=
             λ ⊢e₂ → just ( str , T-concat ⊢e₁ ⊢e₂)
typeinfer Γ ∣ e ∣ = typecheck Γ e str >>=
         λ ⊢e → just ( num , T-length ⊢e )
typeinfer Γ ⟨⟩ = just (unit , T-unit)
typeinfer Γ ⟨ e₁ , e₂ ⟩ =  typeinfer Γ e₁ >>=
                λ ti1 → typeinfer Γ e₂ >>=
                λ ti2 → just ((fst ti1 ⊗ fst ti2) ,  T-prod (snd ti1) (snd ti2))
typeinfer Γ (prj₁ e) with typeinfer Γ e
...| just (τ₁ ⊗ τ₂ , ⊢⊗) = just ( τ₁ ,  T-prj₁ ⊢⊗)
{-# CATCHALL #-}
...| _       =  nothing
typeinfer Γ (prj₂ e) with typeinfer Γ e
...| just (τ₁ ⊗ τ₂ , ⊢⊗) = just ( τ₂ ,  T-prj₂ ⊢⊗)
{-# CATCHALL #-}
...| _       =  nothing
typeinfer Γ (inj₁⟦ τ₁ , τ₂ ⟧ e) with typeinfer Γ e
...| nothing =  nothing
...| just (t , ⊢e) with τ₁ ≟ t
...  | yes refl =  just ( τ₁ ⊕ τ₂ ,  T-inj₁  ⊢e)
...  | no _ = nothing
typeinfer Γ (inj₂⟦ τ₁ , τ₂ ⟧ e) with typeinfer Γ e
...| nothing =  nothing
...| just (t , ⊢e) with τ₂ ≟ t
...  | yes refl =  just ( τ₁ ⊕ τ₂ ,  T-inj₂ ⊢e)
...  | no _ = nothing

typeinfer Γ case e [left x ↦ e₁ ,right y ↦ e₂ ] with typeinfer Γ e
typeinfer Γ case e [left x ↦ e₁ ,right y ↦ e₂ ] | nothing =  nothing
typeinfer Γ case e [left x ↦ e₁ ,right y ↦ e₂ ] | just (num , ⊢e) =  nothing
typeinfer Γ case e [left x ↦ e₁ ,right y ↦ e₂ ] | just (str , ⊢e) =  nothing
typeinfer Γ case e [left x ↦ e₁ ,right y ↦ e₂ ] | just (unit , ⊢e) =  nothing
typeinfer Γ case e [left x ↦ e₁ ,right y ↦ e₂ ] | just (τ ⊗ τ₁ , ⊢e) =  nothing
typeinfer Γ case e [left x ↦ e₁ ,right y ↦ e₂ ] | just (τ ⇒ τ₁ , ⊢e) =  nothing
typeinfer Γ case e [left x ↦ e₁ ,right y ↦ e₂ ] | just (τ₁ ⊕ τ₂ , ⊢e) with typeinfer ((x , τ₁) ∷ Γ) e₁
typeinfer Γ case e [left x ↦ e₁ ,right y ↦ e₂ ] | just (τ₁ ⊕ τ₂ , ⊢e) | nothing = nothing
typeinfer Γ case e [left x ↦ e₁ ,right y ↦ e₂ ] | just (τ₁ ⊕ τ₂ , ⊢e) | just (τₒ₁ , ⊢e₁) with typeinfer ((y , τ₂) ∷ Γ) e₂
typeinfer Γ case e [left x ↦ e₁ ,right y ↦ e₂ ] | just (τ₁ ⊕ τ₂ , ⊢e) | just (τₒ₁ , ⊢e₁) | nothing =  nothing
typeinfer Γ case e [left x ↦ e₁ ,right y ↦ e₂ ] | just (τ₁ ⊕ τ₂ , ⊢e) | just (τₒ₁ , ⊢e₁) | just (τₒ₂ , ⊢e₂) with τₒ₁ ≟ τₒ₂
typeinfer Γ case e [left x ↦ e₁ ,right y ↦ e₂ ] | just (τ₁ ⊕ τ₂ , ⊢e) | just (τₒ₁ , ⊢e₁) | just (τₒ₂ , ⊢e₂) | no ¬p = nothing
typeinfer Γ case e [left x ↦ e₁ ,right y ↦ e₂ ] | just (τ₁ ⊕ τ₂ , ⊢e) | just (τₒ₁ , ⊢e₁) | just (τₒ₂ , ⊢e₂) | yes refl
  =  just (τₒ₁ ,  T-case ⊢e  ⊢e₁  ⊢e₂)

typeinfer Γ (ƛ x ∶ τ₁ ↦ e) with typeinfer ((x , τ₁) ∷ Γ) e
typeinfer Γ (ƛ x ∶ τ₁ ↦ e) | nothing = nothing
typeinfer Γ (ƛ x ∶ τ₁ ↦ e) | just (τ₂ , ⊢e) =  just ( ( τ₁ ⇒ τ₂) ,  T-lam  ⊢e)

typeinfer Γ (e₁ ∙ e₂) with typeinfer Γ e₁
typeinfer Γ (e₁ ∙ e₂) | nothing =  nothing
typeinfer Γ (e₁ ∙ e₂) | just (τ₁' ⇒ τ₂ , ⊢e₁) with typeinfer Γ e₂
typeinfer Γ (e₁ ∙ e₂) | just (τ₁' ⇒ τ₂ , ⊢e₁) | nothing =  nothing
typeinfer Γ (e₁ ∙ e₂) | just (τ₁' ⇒ τ₂ , ⊢e₁) | just (τ₁ , ⊢e₂) with τ₁ ≟ τ₁'
...| yes refl =  just (  τ₂ , T-app  ⊢e₁  ⊢e₂)
...| no x = nothing
{-# CATCHALL #-}
typeinfer Γ (e₁ ∙ e₂) | just (τ₁ , ⊢e₁) = nothing


typecheck Γ e τ with typeinfer Γ e
typecheck Γ e τ | nothing = nothing
typecheck Γ e τ | just (τ' , ⊢e) with τ ≟ τ'
...| yes refl = just ⊢e
...| no x =  nothing

--------------------------------------------------------------------------------
--------------------------------- Dynamics -------------------------------------
--------------------------------------------------------------------------------


                     --------------------------------------
                     --------------- Values ---------------
                     --------------------------------------

data Value : Expr → Set where
  V-num : ∀ {n} → Value num[ n ]
  V-str : ∀ {s} → Value str[ s ]
  V-unit : Value ⟨⟩
  V-prod : ∀ {v₁ v₂}
         → Value v₁ → Value v₂
         ------------------------
         → Value ⟨ v₁ , v₂ ⟩
  V-inj₁ : ∀ {v τ₁ τ₂}
         → Value v
         → Value (inj₁⟦ τ₁ , τ₂ ⟧ v)
  V-inj₂ : ∀ {v τ₁ τ₂}
         → Value v
         → Value (inj₂⟦ τ₁ , τ₂ ⟧ v)
  V-lam : ∀ {x τ e}
        → Value (ƛ x ∶ τ ↦ e)

                     --------------------------------------
                     ------------ Substitution ------------
                     --------------------------------------

[_/_]_ : Expr → Name → Expr → Expr
[ e' / x ] [ x₁ ] with x ≟string x₁
...| yes _ =  e'
...| no _ =  [ x₁ ]
[ e' / x ] num[ n ] =  num[ n ]
[ e' / x ] str[ s ] =  str[ s ]
[ e' / x ] (e₁ + e₂) =  [ e' / x ] e₁ + [ e' / x ] e₂
[ e' / x ] (e₁ × e₂) =  [ e' / x ] e₁ × [ e' / x ] e₂
[ e' / x ] (∣ e ∣) = ∣ [ e' / x ] e ∣
[ e' / x ] (e₁ ^ e₂) =  [ e' / x ] e₁ ^ [ e' / x ] e₂
[ e' / x ] ⟨⟩ = ⟨⟩
[ e' / x ] ⟨ e₁ , e₂ ⟩ = ⟨ [ e' / x ] e₁ , [ e' / x ] e₂ ⟩
[ e' / x ] (prj₁ e) = prj₁ ([ e' / x ] e)
[ e' / x ] (prj₂ e) = prj₂ ([ e' / x ] e)
[ e' / x ] (inj₁⟦ τ₁ , τ₂ ⟧ e) =  inj₁⟦ τ₁ , τ₂ ⟧ ( [ e' / x ]  e)
[ e' / x ] (inj₂⟦ τ₁ , τ₂ ⟧ e) =  inj₂⟦ τ₁ , τ₂ ⟧ ( [ e' / x ]  e)
[ e' / x ] (let[ x' := e₁ ] e₂) with x' ≟string x
...| yes x≡x' =  let[ x' := ([ e' / x ] e₁) ] e₂
...| no x≠x'  =  let[ x' := ([ e' / x ] e₁) ] ([ e' / x ] e₂)
[ e' / x ] (case e [left l ↦ e₁ ,right r ↦ e₂ ]) with (x ≟string l) , (x ≟string r)
([ e' / x ] case e [left l ↦ e₁ ,right r ↦ e₂ ]) | yes x≡l , yes x≡r
  = case ([ e' / x ] e) [left l ↦ e₁ ,right r ↦ e₂ ]
([ e' / x ] case e [left l ↦ e₁ ,right r ↦ e₂ ]) | yes x≡l , no x≠r
  =  case ([ e' / x ] e) [left l ↦ e₁ ,right r ↦ ( [ e' / x ] e₂) ]
([ e' / x ] case e [left l ↦ e₁ ,right r ↦ e₂ ]) | no x≠l  , yes x≡r
  =  case ([ e' / x ] e) [left l ↦ ([ e' / x ] e₁) ,right r ↦ e₂ ]
([ e' / x ] case e [left l ↦ e₁ ,right r ↦ e₂ ]) | no x≠l  , no x≠r
  =  case ([ e' / x ] e) [left l ↦ ([ e' / x ] e₁) ,right r ↦ ([ e' / x ] e₂) ]
([ e' / x ] (ƛ y ∶ τ ↦ e)) with x ≟string y
...| yes x≡y =  ƛ y ∶ τ ↦ e
...| no x≠y  =  ƛ y ∶ τ ↦ ([ e' / x ] e)
([ e' / x ] (e₁ ∙ e₂)) =  ([ e' / x ] e₁) ∙ ([ e' / x ] e₂)




                     --------------------------------------
                     --------- Big-Step Semantics ---------
                     --------------------------------------

infix 2 _⇓_

data _⇓_ : Expr → Expr → Set where
  ⇓-num : ∀{n}
        ------------------------
        → num[ n ] ⇓ num[ n ]

  ⇓-str : ∀{s}
        ------------------------
        → str[ s ] ⇓ str[ s ]

  ⇓-plus : ∀{e₁ e₂ n m}
         → e₁ ⇓ num[ n ]
         → e₂ ⇓ num[ m ]
         -----------------------
         → e₁ + e₂ ⇓ num[ plus n m ]

  ⇓-mult : ∀{e₁ e₂ n m}
         → e₁ ⇓ num[ n ]
         → e₂ ⇓ num[ m ]
         -----------------------
         → e₁ × e₂ ⇓ num[ mult n m ]

  ⇓-length : ∀{e s}
           → e ⇓ str[ s ]
           ---------------------------
           → ∣ e ∣ ⇓ num[ length s ]

  ⇓-concat : ∀{e₁ e₂ s r}
           → e₁ ⇓ str[ s ]
           → e₂ ⇓ str[ r ]
           -----------------------
           → e₁ ^ e₂ ⇓ str[ s ++ r ]

  ⇓-unit :
         -----------------------
         ⟨⟩ ⇓ ⟨⟩

  ⇓-prod : ∀ {e₁ e₂ v₁ v₂}
         → e₁ ⇓ v₁
         → e₂ ⇓ v₂
         --------------------------
         → ⟨ e₁ , e₂ ⟩ ⇓ ⟨ v₁ , v₂ ⟩

  ⇓-prj₁ : ∀ {e e₁ e₂}
         → e ⇓ ⟨ e₁ , e₂ ⟩
         --------------------------
         → prj₁ e ⇓ e₁

  ⇓-prj₂ : ∀ {e e₁ e₂}
         → e ⇓ ⟨ e₁ , e₂ ⟩
         --------------------------
         → prj₂ e ⇓ e₂



data Canonical : Expr → Type → Set where
  C-num : ∀{n} → Canonical num[ n ] num
  C-str : ∀{s} → Canonical str[ s ] str
  C-unit : Canonical ⟨⟩ unit
  C-prod : ∀ {v₁ v₂ τ₁ τ₂} → Canonical v₁ τ₁ → Canonical v₂ τ₂
         -----------------------------------------
         → Canonical ⟨ v₁ , v₂ ⟩ (τ₁ ⊗ τ₂)
  C-inj₁ : ∀ {τ₁ τ₂ v}
         → Canonical v τ₁
         --------------------------------------------
         → Canonical (inj₁⟦ τ₁ , τ₂ ⟧ v) (τ₁ ⊕ τ₂)
  C-inj₂ : ∀ {τ₁ τ₂ v}
         → Canonical v τ₂
         --------------------------------------------
         → Canonical (inj₂⟦ τ₁ , τ₂ ⟧ v) (τ₁ ⊕ τ₂)
  C-arr : ∀ {x τ₁ τ₂ e}
        → ((x , τ₁) ∷ []) ⊢ e ∶ τ₂
        → Canonical (ƛ x ∶ τ₁ ↦ e) (τ₁ ⇒ τ₂)

canonical : ∀ {e τ}
          → [] ⊢ e ∶ τ
          → Value e
          → Canonical e τ
canonical T-num V-num = C-num
canonical T-str V-str = C-str
canonical T-unit V-unit = C-unit
canonical (T-prod ⊢e₁ ⊢e₂) (V-prod V-e₁ V-e₂) =
  C-prod (canonical ⊢e₁ V-e₁) ( canonical ⊢e₂ V-e₂)
canonical (T-inj₁ ⊢e) (V-inj₁ V-e) with canonical ⊢e V-e
...| C-e =  C-inj₁ C-e
canonical (T-inj₂ ⊢e) (V-inj₂ V-e) with canonical ⊢e V-e
...| C-e =  C-inj₂ C-e
canonical (T-lam ⊢e) V-lam = C-arr ⊢e

value : ∀ {e τ} → Canonical e τ
      → Value e
value C-num = V-num
value C-str = V-str
value C-unit = V-unit
value (C-prod C-e₁ C-e₂) = V-prod (value C-e₁) (value C-e₂)
value (C-inj₁ C-e) = V-inj₁ (value C-e)
value (C-inj₂ C-e) = V-inj₂ (value C-e)
value (C-arr ⊢e) =  V-lam

typed : ∀ {e τ} → Canonical e τ
      → [] ⊢ e ∶ τ
typed C-num = T-num
typed C-str = T-str
typed C-unit = T-unit
typed (C-prod C-e₁ C-e₂) = T-prod (typed C-e₁) (typed C-e₂)
typed (C-inj₁ C-e) = T-inj₁ (typed C-e)
typed (C-inj₂ C-e) = T-inj₂ (typed C-e)
typed (C-arr ⊢e) = T-lam ⊢e



                     --------------------------------------
                     -------- Small-Step Semantics --------
                     --------------------------------------

infix 2 _⟶_

data _⟶_ : Expr → Expr → Set where

  ξ₁-plus : ∀ {e₁ e₁' e₂}
          → e₁ ⟶ e₁'
          --------------------------
          → e₁ + e₂ ⟶ e₁' + e₂

  ξ₂-plus : ∀ {v e₂ e₂'}
          → Value v
          → e₂ ⟶ e₂'
          -------------------------
          → v + e₂ ⟶ v + e₂'

  β-plus : ∀ {n m}
         ------------------------------------------
         → num[ n ] + num[ m ] ⟶ num[ plus n m ]

  ξ₁-times : ∀ {e₁ e₁' e₂}
         → e₁ ⟶ e₁'
         --------------------------
         → e₁ × e₂ ⟶ e₁' × e₂

  ξ₂-times : ∀ {v e₂ e₂'}
           → Value v
           → e₂ ⟶ e₂'
           -------------------------
           → v × e₂ ⟶ v × e₂'

  β-times : ∀ {n m}
          ------------------------------------------
          → num[ n ] × num[ m ] ⟶ num[ mult n m ]

  ξ-length : ∀ {e e'}
           → e ⟶ e'
           ---------------------
           → ∣ e ∣ ⟶ ∣ e' ∣

  β-length : ∀ {s}
           → ∣ str[ s ] ∣ ⟶ num[ length s ]


  ξ₁-concat : ∀ {e₁ e₁' e₂}
           → e₁ ⟶ e₁'
           --------------------------
           → e₁ ^ e₂ ⟶ e₁' ^ e₂

  ξ₂-concat : ∀ {v e₂ e₂'}
           → Value v
           → e₂ ⟶ e₂'
           -------------------------
           → v ^ e₂ ⟶ v ^ e₂'

  β-concat : ∀ {n m}
          ------------------------------------------
          → str[ n ] ^ str[ m ] ⟶ str[ n ++ m ]

  ξ₁-prod : ∀ {e₁ e₁' e₂}
          → e₁ ⟶ e₁'
          --------------------------
          → ⟨ e₁ , e₂ ⟩ ⟶ ⟨ e₁' , e₂ ⟩


  ξ₂-prod : ∀ {v e₂ e₂'}
          → Value v
          → e₂ ⟶ e₂'
          -------------------------
          → ⟨ v , e₂ ⟩ ⟶ ⟨ v , e₂' ⟩

  ξ-prj₁ : ∀ {e e'}
          → e ⟶ e'
          ---------------------------
          → prj₁ e ⟶ prj₁ e'

  β-prj₁ : ∀ {e₁ e₂}
          ---------------------------
          → prj₁ ⟨ e₁ , e₂ ⟩ ⟶ e₁

  ξ-prj₂ : ∀ {e e'}
          → e ⟶ e'
          ---------------------------
          → prj₂ e ⟶ prj₂ e'

  β-prj₂ : ∀ {e₁ e₂}
          ---------------------------
          → prj₂ ⟨ e₁ , e₂ ⟩ ⟶ e₂

  ξ-inj₁ : ∀ {e e' τ₁ τ₂}
         → e ⟶ e'
         -----------------------------
         → inj₁⟦ τ₁ , τ₂ ⟧ e ⟶ inj₁⟦ τ₁ , τ₂ ⟧ e'

  ξ-inj₂ : ∀ {e e' τ₁ τ₂}
         → e ⟶ e'
         -----------------------------
         → inj₂⟦ τ₁ , τ₂ ⟧ e ⟶ inj₂⟦ τ₁ , τ₂ ⟧ e'

  ξ-let : ∀ {x e₁ e₁' e₂}
        → e₁ ⟶ e₁'
        ----------------------------------------------
        → (let[ x := e₁ ] e₂) ⟶ (let[ x := e₁' ] e₂)

  β-let : ∀ {x v e₂}
         → Value v
         ----------------------------------------------
         → (let[ x := v ] e₂) ⟶ ([ v / x ] e₂)

  ξ-case : ∀ {e e' e₁ e₂ x y}
         → e ⟶ e'
         -------------------------------------------------------------------------------------
         → case e [left  x ↦ e₁
                   ,right y ↦ e₂ ] ⟶ case e' [left x ↦ e₁ ,right y ↦ e₂ ]

  β-case₁ : ∀ {e₁ e₂ v τ₁ τ₂ x y}
          → Value v
          --------------------------------------------------------------------------------
          → case (inj₁⟦ τ₁ , τ₂ ⟧ v) [left x ↦ e₁ ,right y ↦ e₂ ] ⟶ ( [ v / x ] e₁)


  β-case₂ : ∀ {e₁ e₂ v τ₁ τ₂ x y}
          → Value v
          --------------------------------------------------------------------------------
          → case (inj₂⟦ τ₁ , τ₂ ⟧ v) [left x ↦ e₁ ,right y ↦ e₂ ] ⟶ ( [ v / y ] e₂)

  ξ₁-app : ∀ {e₁ e₁' e₂}
         → e₁ ⟶ e₁'
         --------------------------
         → e₁ ∙ e₂ ⟶ e₁' ∙ e₂

  ξ₂-app : ∀ {v e₂ e₂'}
         → Value v
         → e₂ ⟶ e₂'
         --------------------------
         → v ∙ e₂ ⟶ v ∙ e₂'

  β-lam : ∀ {x τ e v}
        → Value v
        ---------------------------------------
        → (ƛ x ∶ τ ↦ e) ∙ v ⟶ [ v / x ] e


infix 2 _↠_
infix 2 _⟶⟨_⟩_
infix 3 _∎

data _↠_ : Expr → Expr → Set where
  _∎ : ∀ M → M ↠ M
  _⟶⟨_⟩_ : ∀ L { M N }
           → L ⟶ M
           → M ↠ N
           → L ↠ N


