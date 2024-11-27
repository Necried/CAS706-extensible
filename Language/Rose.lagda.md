This defines the Rose language as given in Chapter 4 of the paper.

```agda
module Rose where

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; _≢_)
open import Data.String using (String; _≟_)
open import Relation.Nullary.Decidable using ( Dec; yes; no; False; toWitnessFalse)
open import Data.Product using (_×_; proj₁; proj₂; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary.Negation using (¬_; contradiction)
import SystemF as F
```

The syntax of rows, predicates and types.
These three types are mutually recursive.

Operators
```agda
infix   4  _∋_⦂_
infix   4  _∋_꞉_
infix   4 _❙_⊢_⤳_⦂_
infix   4 _⇒_⦂_

infixl  5  _,_⦂_
infix   5  ƛ_⇒_
infix   5 _⨀_~_ 
infixl  5 _⧀_
infixr  7  _⇒_
infixr  7  _ᵐ⇒_
infixl  7  _★_

infix   9  `_
infix   9  ᵐ_
```

```agda
Id : Set
Id = String

Label : Set
Label = String

data Predicate : Set
data Type : Set
data Row : Set

data Predicate where
  _⧀_ : Row → Row → Predicate
  _⨀_~_ : Row → Row → Row → Predicate

data Type where
  `_ : Id → Type
  _⇒_ : Type → Type → Type
  Π_ : Row → Type
  Σ_ : Row → Type
  _▹_ : Label → Type → Type

data Row where
  _▹_,_ : Label → Type → Row
  ∎ᵣ : Row
```


Terms, with qualified types ,schemes and direction
```agda
data ℚType : Set where
  `_ : Type → ℚType
  _⇒_ : Predicate → ℚType → ℚType

data Scheme : Set where
  QType : ℚType → Scheme
  `∀_•_ : Id → Scheme → Scheme
  -- Omitted row polymorphic variables, could be
  -- combined with the ∀ abouve

-- If we need a monotype:
pattern ᵐ x = QType (` x)

data MonoType : Scheme → Set where
  Mono-v : ∀ {t : Type} → MonoType (ᵐ t)
  Mono⇒ : ∀ {τ v}
    → MonoType (ᵐ τ)
    → MonoType (ᵐ v)
      --------------
    → MonoType (ᵐ (τ ⇒ v))

-- MonoType arrows
_ᵐ⇒_
  : (τ₁ : Scheme)
  → (τ₂ : Scheme)
  → {isMono₁ : MonoType τ₁}
  → {isMono₂ : MonoType τ₂}
  → Scheme
ᵐ τ₁ ᵐ⇒ ᵐ τ₂ = ᵐ (τ₁ ⇒ τ₂)

data Direction : Set where
  L : Direction
  R : Direction

data Term : Set where
  `_     : Id → Term
  ƛ_⇒_   : Id → Term → Term
  _·_    : Term → Term → Term
  `let_⦂_＝_`in_ : Id → Scheme → Term → Term → Term
  _▹_ : Label → Term → Term
  _/_ : Term → Label → Term
  prj⟦_⟧_ : Direction → Term → Term
  _★_ : Term → Term → Term
  inj⟦_⟧_ : Direction → Term → Term
  _▿_ : Term → Term → Term
```

Context for predicates and Env for types
(I don't like this naming convention but it follows the paper)
```agda
data Context : Set where
  ∅ : Context
  _,_⦂_ : Context → Id → Predicate → Context

data Env : Set where
  ∅ : Env
  _,_⦂_ : Env → Id → Scheme → Env
```

```agda
data _∋_⦂_ : Env → Id → Scheme → Set where
  Z : ∀ {Γ x A} → Γ , x ⦂ A ∋ x ⦂ A
  S : ∀ {Γ x y A B} → x ≢ y → Γ ∋ x ⦂ A
    → Γ , y ⦂ B ∋ x ⦂ A

data _∋_꞉_ : Context → Id → Predicate → Set where
  Z : ∀ {Γ x A} → Γ , x ⦂ A ∋ x ꞉ A
  S : ∀ {Γ x y A B} → x ≢ y → Γ ∋ x ꞉ A
    → Γ , y ⦂ B ∋ x ꞉ A

```

Translating from Rose types to F⊗⊕
```agda
⟦_⟧ : Scheme → F.Type
⟦_⟧ = {!!}

⟪_⟫ : Predicate → F.Type
⟪_⟫ = {!!}
```

Free variables in the context and environment:
```agda
_∉FV[_,_] : Id → Context → Env → Set
y ∉FV[ P , Γ ] = ∀ {t ψ} → ¬ (Γ ∋ y ⦂ t) × ¬ (P ∋ y ꞉ ψ)
```

Type substitutions into schemes
```agda
infix 9 _ᵗ[_≔_]
_ᵗ[_≔_] : Scheme → Id → Type → Scheme
ᵐ A ᵗ[ t ≔ τ ] = {!!}
QType (ψ ⇒ ρ) ᵗ[ t ≔ τ ] = {!!}
(`∀ t′ • σ) ᵗ[ t ≔ τ ] = {!!}
```

The augmented entailment judgment P ⇒ F ∶ ψ denotes that
F is an F⊗⊕ term giving evidence for predicate ψ
```agda
open F.Term

data _⇒_⦂_ : Context → F.Term → Predicate → Set where
```

Extension of the equivalence relation ζ₁ ~ ζ₂ on rows
to an equivalence ⊢ τ₁ ≈ τ₂ on types
```agda
data ⊢_≈_ : Type → Type → Set where
```

Relating predicates to evidence of the predicate:
```agda
Evidence : Predicate → F.Type
Evidence (ζ₁ ⨀ ζ₂ ~ ζ₃) = ? -- ⟦ ᵐ (Π ζ₁) ⟧ → ⟦ ᵐ (Π ζ₂) ⟧ → ⟦ ᵐ (Π ζ₃) ⟧
Evidence n = ?

```

Rose typing rules and translation to F⊗⊕
```agda
data _❙_⊢_⤳_⦂_ : Context → Env → Term → F.Term → Scheme → Set where
  var : ∀ {P Γ x σ}
    → MonoType σ
    → Γ ∋ x ⦂ σ
      -------------
    → P ❙ Γ ⊢ ` x ⤳ ` x ⦂ σ

  `let : ∀ {P Γ M N E F σ τ x}
    → MonoType τ
    → P ❙ Γ ⊢ M ⤳ E ⦂ σ
    → P ❙ Γ , x ⦂ σ ⊢ N ⤳ F ⦂ τ
      ---------------------------
    → P ❙ Γ ⊢ (`let x ⦂ σ ＝ M `in N) ⤳ (ƛ x ⦂ ⟦ σ ⟧ ⇒ F) · E ⦂ τ

  →I : ∀ {P Γ M E τ v x}
    → (mono-τ : MonoType τ)
    → (mono-v : MonoType v)
    → P ❙ Γ , x ⦂ τ ⊢ M ⤳ E ⦂ v
      ---------------------------
    → P ❙ Γ ⊢ ƛ x ⇒ M ⤳ (ƛ x ⦂ ⟦ τ ⟧ ⇒ E) ⦂ (τ ᵐ⇒ v) {mono-τ} {mono-v}

  →E : ∀ {P Γ M N E F τ v}
    → (mono-τ : MonoType τ)
    → (mono-v : MonoType v)
    → P ❙ Γ ⊢ M ⤳ F ⦂ (τ ᵐ⇒ v) {mono-τ} {mono-v}
    → P ❙ Γ ⊢ N ⤳ E ⦂ τ
      ----------------------
    → P ❙ Γ ⊢ M · N ⤳ F · E ⦂ v

  ⇒I : ∀ {P ψ Γ M E v ρ}
    → P , v ⦂ ψ ❙ Γ ⊢ M ⤳ E ⦂ QType ρ
      ---------------------------
    → P ❙ Γ ⊢ M ⤳ ƛ v ⦂ ⟪ ψ ⟫ ⇒ E ⦂ QType (ψ ⇒ ρ)

  ⇒E : ∀ {P Γ E F M N ψ ρ}
    → P ❙ Γ ⊢ M ⤳ F ⦂ QType (ψ ⇒ ρ)
    → P ⇒ E ⦂ ψ
      --------------------------------
    → P ❙ Γ ⊢ M · N ⤳ F · E ⦂ QType ρ

  ∀I : ∀ {P Γ M E σ t}
    → P ❙ Γ ⊢ M ⤳ E ⦂ σ
    → t ∉FV[ P , Γ ]
      ------------------------
    → P ❙ Γ ⊢ M ⤳ Λ t ⇒ E ⦂ (`∀ t • σ)

  ∀E : ∀ {P Γ M E t σ}{τ : Type}
    → P ❙ Γ ⊢ M ⤳ E ⦂ `∀ t • σ
      ---------------------------
    → P ❙ Γ ⊢ M ⤳ E ＠ ⟦ ᵐ τ ⟧ ⦂ σ ᵗ[ t ≔ τ ]

  ▹I : ∀ {P Γ M E ℓ τ}
    → P ❙ Γ ⊢ M ⤳ E ⦂ ᵐ τ
      -------------------------
    → P ❙ Γ ⊢ ℓ ▹ M ⤳ E ⦂ ᵐ (ℓ ▹ τ)

  ▹E : ∀ {P Γ M E ℓ τ}
    → P ❙ Γ ⊢ M ⤳ E ⦂ ᵐ (ℓ ▹ τ)
      -------------------------
    → P ❙ Γ ⊢ M / ℓ ⤳ E ⦂ ᵐ τ

  SIM : ∀ {P Γ M E τ v}
    → P ❙ Γ ⊢ M ⤳ E ⦂ ᵐ τ
    → ⊢ τ ≈ v
      -------------------
    → P ❙ Γ ⊢ M ⤳ E ⦂ ᵐ v

{-
  ΠI : ∀ {P Γ M₁ M₂ E₁ E₂ F ζ₁ ζ₂ ζ₃}
    → P ❙ Γ ⊢ M₁ ⤳ E₁ ⦂ ᵐ (Π ζ₁)
    → P ❙ Γ ⊢ M₂ ⤳ E₂ ⦂ ᵐ (Π ζ₂)
    → P ⇒ F ⦂ ζ₁ ⨀ ζ₂ ~ ζ₃
      -------------------------
    → P ❙ Γ ⊢ M₁ ★ M₂ ⤳ Evidence (ζ₁ ⨀ ζ₂ ~ ζ₃) · E₁ · E₂ ⦂ ᵐ (Π ζ₃)
-}

-- ΠEd : 

```
