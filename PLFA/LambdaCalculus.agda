module LambdaCalculus where

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Data.String using (String; _≟_ )
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Negation using (¬?)


{-
⇒  U+21D2  RIGHTWARDS DOUBLE ARROW (\=>)
ƛ  U+019B  LATIN SMALL LETTER LAMBDA WITH STROKE (\Gl-)
·  U+00B7  MIDDLE DOT (\cdot)
—  U+2014  EM DASH (\em)
↠  U+21A0  RIGHTWARDS TWO HEADED ARROW (\rr-)
ξ  U+03BE  GREEK SMALL LETTER XI (\Gx or \xi)
β  U+03B2  GREEK SMALL LETTER BETA (\Gb or \beta)
∋  U+220B  CONTAINS AS MEMBER (\ni)
∅  U+2205  EMPTY SET (\0)
⊢  U+22A2  RIGHT TACK (\vdash or \|-)
⦂  U+2982  Z NOTATION TYPE COLON (\:)
-}

Id : Set
Id = String


infix  5  ƛ_⇒_
infix  5  μ_⇒_
infixl 7  _·_
infix  8  `suc_
infix  9  `_

data Term : Set where
  `_    : Id → Term
  ƛ_⇒_ : Id → Term → Term
  _·_   : Term → Term → Term
  `zero : Term
  `suc_ : Term → Term
  case_[zero⇒_|suc_⇒_] : Term → Term → Id → Term → Term
  μ_⇒_                  : Id → Term → Term

-- Example Terms

two : Term
two = `suc `suc `zero

plus : Term
plus = μ "+" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
         case ` "m"
         [zero⇒ ` "n"
         |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")]

2+2 : Term
2+2 = plus · two · two

-- Church Numerals 

twoᶜ : Term
twoᶜ =  ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · ` "z")

plusᶜ : Term
plusᶜ =  ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒
        ` "m" · ` "s" · (` "n" · ` "s" · ` "z")

sucᶜ : Term
sucᶜ = ƛ "n" ⇒ `suc (` "n")

fourᶜ : Term
fourᶜ = plusᶜ · twoᶜ · twoᶜ

-- Exercise : mul

mul : Term
mul = μ "×" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
        case ` "m" [zero⇒ `zero
                   |suc "m" ⇒  case ` "m" [zero⇒ ` "n"
                                           |suc "m" ⇒ ` "+" · ` "n" · ` "mul" · ` "m" · ` "n" ] ]



-- Values

data Value : Term → Set where
  V-ƛ    : ∀ {x N} → Value (ƛ x ⇒ N)
  V-zero : Value `zero
  V-suc  : ∀ {V} → Value V → Value (`suc V)


-- Substitution by Closed Terms

infix 9 _[_:=_]

_[_:=_] : Term → Id → Term → Term
(` x) [ y := V ] with x ≟ y
... | yes _ = V
... | no  _ = ` x
(ƛ x ⇒ N) [ y := V ] with x ≟ y
... | yes _ =  ƛ x ⇒ N
... | no  _ =  ƛ x ⇒ N [ y := V ]
(L · M) [ y := V ] = L [ y := V ] · M [ y := V ]
`zero [ y := V ] =  `zero
(`suc M) [ y := V ] =  `suc M [ y := V ]
case L [zero⇒ M |suc x ⇒ N ] [ y := V ] with x ≟ y
... | yes _ =  case L [ y := V ] [zero⇒ M [ y := V ] |suc x ⇒ N ]
... | no  _ = case L [ y := V ] [zero⇒ M [ y := V ] |suc x ⇒ N [ y := V ] ]
(μ x ⇒ N) [ y := V ] with x ≟ y
... | yes _ =  μ x ⇒ N
... | no  _ =  μ x ⇒ N [ y := V ]

-- Exercise: subprime


-- Some Examples of Substitution

_ : (sucᶜ · (sucᶜ · ` "z")) [ "z" := `zero ] ≡  sucᶜ · (sucᶜ · `zero)
_ = refl

_ : (ƛ "z" ⇒ ` "s" · (` "s" · ` "z")) [ "s" := sucᶜ ] ≡  ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")
_ = refl

_ : (ƛ "x" ⇒ ` "y") [ "y" := `zero ] ≡ ƛ "x" ⇒ `zero
_ = refl

_ : (ƛ "x" ⇒ ` "x") [ "x" := `zero ] ≡ ƛ "x" ⇒ ` "x"
_ = refl

_ : (ƛ "y" ⇒ ` "y") [ "x" := `zero ] ≡ ƛ "y" ⇒ ` "y"
_ = refl


-- Reductions

infix 4 _⟶_

data _⟶_ : Term → Term → Set where

  ξ-·₁ : ∀ {L L' M}
       → L ⟶ L'
       ---------------------
       → L · M ⟶ L' · M


  ξ-·₂ : ∀ {V M M'}
       → Value V
       → M ⟶ M'
       ---------------------
       → V · M ⟶ V · M'

  β-ƛ : ∀ {x N V}
      → Value V
      ----------------------
      → (ƛ x ⇒ N) · V ⟶ N [ x := V ]

  ξ-suc : ∀ {M M'}
        → M ⟶ M'
        ----------------------
        → `suc M ⟶ `suc M'

  ξ-case : ∀ {x L L′ M N}
         → L ⟶ L′
         -----------------------------------------------------------------
         → case L [zero⇒ M |suc x ⇒ N ] ⟶ case L′ [zero⇒ M |suc x ⇒ N ]

  β-zero : ∀ {x M N}
         ----------------------------------------
         → case `zero [zero⇒ M |suc x ⇒ N ] ⟶ M

  β-suc : ∀ {x V M N}
        → Value V
        ---------------------------------------------------
        → case `suc V [zero⇒ M |suc x ⇒ N ] ⟶ N [ x := V ]

  β-μ : ∀ {x M}
      ------------------------------
      → μ x ⇒ M ⟶ M [ x := μ x ⇒ M ]


-- Reflexive and transitive closure

infix 2 _↠_
infix 1 begin_
infixr 2 _⟶⟨_⟩_
infix 3 _∎

data _↠_ : Term → Term → Set where
  _∎ : ∀ M
     -----------
     → M ↠ M

  _⟶⟨_⟩_ : ∀ L {M N}
         → L ⟶ M
         → M ↠ N
         -------------
         → L ↠ N

begin_ : ∀ {M N}
       → M ↠ N
       -------------
       → M ↠ N
begin M↠N = M↠N



-- Examples



_ : twoᶜ · sucᶜ · `zero ↠ `suc `suc `zero
_ =
  begin
    twoᶜ · sucᶜ · `zero
  ⟶⟨  ξ-·₁ ( β-ƛ  V-ƛ) ⟩
    (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · `zero
  ⟶⟨  β-ƛ  V-zero  ⟩
    sucᶜ · (sucᶜ · `zero)
  ⟶⟨ ξ-·₂ V-ƛ ( β-ƛ  V-zero) ⟩
    sucᶜ · ( `suc `zero)
  ⟶⟨  β-ƛ ( V-suc V-zero) ⟩
    `suc `suc `zero ∎

one : Term
one = `suc `zero

_ : plus · (`suc `zero) · (`suc `zero) ↠ two
_ =
  begin
    plus · (`suc `zero) · (`suc `zero)
  ⟶⟨  ξ-·₁ (ξ-·₁ β-μ)  ⟩
    (ƛ "m" ⇒ (ƛ "n" ⇒
      case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (plus · ` "m" · ` "n")]))
    · one · one
  ⟶⟨  ξ-·₁ ( β-ƛ (V-suc V-zero) ) ⟩
    (ƛ "n" ⇒
      case one [zero⇒ ` "n" |suc "m" ⇒ `suc (plus · ` "m" · ` "n")])
    · one
  ⟶⟨  β-ƛ (V-suc V-zero) ⟩
    case one [zero⇒ one |suc "m" ⇒ `suc (plus · ` "m" · one)]
  ⟶⟨  β-suc  V-zero ⟩
    `suc (plus · `zero · one)
    ⟶⟨  ξ-suc ( ξ-·₁ (ξ-·₁ β-μ))  ⟩
    `suc ((ƛ "m" ⇒ (ƛ "n" ⇒
      case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (plus · ` "m" · ` "n")]))
    · `zero · one)
  ⟶⟨  ξ-suc ( ξ-·₁ ( β-ƛ V-zero))  ⟩
    `suc ((ƛ "n" ⇒
      case `zero [zero⇒ ` "n" |suc "m" ⇒ `suc (plus · ` "m" · ` "n")])
    · one)
  ⟶⟨  ξ-suc (β-ƛ (V-suc V-zero))  ⟩
    `suc (case `zero [zero⇒ one |suc "m" ⇒ `suc (plus · ` "m" · one)])
  ⟶⟨  ξ-suc  β-zero ⟩
    `suc `suc `zero
  ∎



-- Syntax of Types

infixr 7 _⇒_

data Type : Set where
  _⇒_ : Type → Type → Type
  `ℕ  : Type


-- Typing Contexts

{-
  These store variables names along with their types
-}

infixl 5 _,_∶_

data Context : Set where
  ∅ : Context
  _,_∶_ : Context → Id → Type → Context


infix 4 _∋_∶_

data _∋_∶_ : Context → Id → Type → Set where

  Z : ∀ {Γ x A}
  ---------------------
    → Γ , x ∶ A ∋ x ∶ A

  S : ∀ {Γ x y A B}
    → x ≢ y
    → Γ ∋ x ∶ A
  --------------------
    → Γ , y ∶ B ∋ x ∶ A



infix 4 _⊢_∶_


data _⊢_∶_ : Context → Term → Type → Set where

  -- Axiom
  ⊢` : ∀ {Γ x A}
     → Γ ∋ x ∶ A
     ----------------
     → Γ ⊢ ` x ∶ A

  -- ⇒-I
  ⊢ƛ : ∀ {Γ x N A B}
     → Γ , x ∶ A ⊢ N ∶ B
     ----------------------
     → Γ ⊢ ƛ x ⇒ N ∶ A ⇒ B

  -- ⇒-E
  _·_ : ∀ {Γ L M A B}
      → Γ ⊢ L ∶ A ⇒ B
      → Γ ⊢ M ∶ A
      ---------------------
      → Γ ⊢ L · M ∶ B

  -- ℕ-I₁
  ⊢zero : ∀ {Γ}
        ---------------------
        → Γ ⊢ `zero ∶ `ℕ

  -- ℕ-I₂
  ⊢suc : ∀ {Γ M}
       → Γ ⊢ M ∶ `ℕ
       -----------------------
       → Γ ⊢ `suc M ∶ `ℕ

  -- ℕ-E
  ⊢case : ∀ {Γ L M x N A}
        → Γ ⊢ L ∶ `ℕ
        → Γ ⊢ M ∶ A
        → Γ , x ∶ `ℕ ⊢ N ∶ A
        ------------------------------
        → Γ ⊢ case L [zero⇒ M |suc x ⇒ N ] ∶ A

  ⊢μ : ∀ {Γ x M A}
     → Γ , x ∶ A ⊢ M ∶ A
     -----------------------------
     → Γ ⊢ μ x ⇒ M ∶ A


-- Checking inequality

_≠_ : ∀ (x y : Id) → x ≢ y
x ≠ y with x ≟ y
...   | no x≢y = x≢y
...   | yes _ = ⊥-elim impossible
  where postulate impossible : ⊥


-- Some type derivations

Ch : Type → Type
Ch A = (A ⇒ A) ⇒ A ⇒ A

⊢twoᶜ : ∀ {Γ A} → Γ ⊢ twoᶜ ∶ Ch A
⊢twoᶜ = ⊢ƛ (⊢ƛ (⊢` ∋s · (⊢` ∋s · ⊢` ∋z)))
  where ∋s = S ("s" ≠ "z") Z
        ∋z = Z


⊢two : ∀ {Γ} → Γ ⊢ two ∶ `ℕ
⊢two =  ⊢suc ( ⊢suc  ⊢zero)


⊢plus : ∀ {Γ} → Γ ⊢ plus ∶ `ℕ ⇒ `ℕ ⇒ `ℕ
⊢plus =  ⊢μ ( ⊢ƛ ( ⊢ƛ ( ⊢case ( ⊢` ∋m) ( ⊢` ∋n )
            ( ⊢suc (  ⊢` ∋+ · ⊢` ∋m' ·  ⊢`  ∋n')))))
  where ∋m = (S ("m" ≠ "n") Z)
        ∋n = Z
        ∋+ =  (S ("+" ≠ "m") ( S ("+" ≠ "n") (S ("+" ≠ "m") Z)))
        ∋m' =  Z
        ∋n' =  S ("n" ≠ "m") Z

⊢2+2 : ∅ ⊢ plus · two · two ∶ `ℕ
⊢2+2 =  ⊢plus · ⊢two · ⊢two


-- Lookup is injective

∋-injective : ∀ {Γ x A B} → Γ ∋ x ∶ A → Γ ∋ x ∶ B → A ≡ B
∋-injective Z Z =  refl
∋-injective Z (S x≢ _) =  ⊥-elim ( x≢ refl )
∋-injective (S x≢ _) Z = ⊥-elim ( x≢ refl )
∋-injective (S _ ∋x) (S _ ∋x') =  ∋-injective ∋x ∋x'




