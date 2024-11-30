This defines the Rose language as given in Chapter 4 of the paper.

```agda
{-# OPTIONS --allow-unsolved-metas #-}
module Rose where

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; _≢_)
open import Data.String using (String; _≟_)
open import Relation.Nullary.Decidable using ( Dec; yes; no; False; toWitnessFalse)
open import Data.Product using (_×_; proj₁; proj₂; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Fin.Base using (Fin; zero; suc; toℕ; fromℕ)
open import Relation.Nullary.Negation using (¬_; contradiction)
open import Data.Nat.Base using (ℕ; zero; suc; pred; _+_; _∸_)
open import Data.Vec using (Vec; []; _∷_; _++_; map; lookup; length)
open import Function.Base using (_∘_)
import SystemF as F
open F using (π[_⦂_]_; ι[_⦂_]_; π[i⦂_]_⟨_≤i≤_⟩; case_ι[i⦂_]⟨_≤i≤_,_⟩; [_⋯_])
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
Row : ℕ → Set

-- Forcing the third row to have its length the sum of the first two rows
data Predicate where
  _⧀_ : ∀ {i j} → Row i → Row j → Predicate
  _⨀_~_ : ∀ {i j} → Row i → Row j → Row (i + j) → Predicate

data Type where
  Nat : Type
  `_ : Id → Type
  _⇒_ : Type → Type → Type
  Π_ : ∀ {n} → Row n → Type
  Σ_ : ∀ {n} → Row n → Type
  _▹_ : Label → Type → Type

Row n = Vec Type n
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
  con    : ℕ → Term
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

In the trivial type theory, row combination is treated as concatenation:
```agda
_⌢_ : ∀ {i j} → Row i → Row j → Row (i + j)
_⌢_ = _++_
```

Translating from Rose types to F⊗⊕
```agda
open F.Type

{-# TERMINATING #-}
⟦_⟧ : Scheme → F.Type
⟪_⟫ : Predicate → F.Type

⟦ ᵐ Nat ⟧ = Nat
⟦ ᵐ (` x) ⟧ = ` x
⟦ ᵐ (A ⇒ B) ⟧ = ⟦ ᵐ A ⟧ ⇒ ⟦ ᵐ B ⟧
⟦ ᵐ (Π ζ) ⟧ = ⊗[ length ζ ]⟨ map (⟦_⟧ ∘ ᵐ) ζ ⟩
⟦ ᵐ (Σ ζ) ⟧ = ⊕[ length ζ ]⟨ map (⟦_⟧ ∘ ᵐ) ζ ⟩
⟦ ᵐ (ℓ ▹ τ) ⟧ = ⟦ ᵐ τ ⟧
⟦ QType (ψ ⇒ ρ) ⟧ = ⟪ ψ ⟫ ⇒ ⟦ QType ρ ⟧
⟦ `∀ x • s ⟧ = `∀ x • ⟦ s ⟧

⟪_⟫ = {!!}

≺_≻ : Term → F.Term
≺_≻ = {!!}
```


There are 6 operations on trivial rows:
```agda
open F.Term
prjL : ∀ {j k} → Row j → Row k → F.Term
prjL {j = 1}{k} ζ₁ ζ₂ = ƛ "x" ⦂ ⟦ ᵐ (Π ζ₂) ⟧ ⇒ π[ 1 ⦂ k ] ` "x"
prjL {j}{k}     ζ₁ ζ₂ = ƛ "x" ⦂ ⟦ ᵐ (Π ζ₂) ⟧ ⇒ π[i⦂ k ] ` "x" ⟨ 1 ≤i≤ j ⟩

prjR : ∀ {j k} → Row j → Row k → F.Term
prjR {j = 1}{k} ζ₁ ζ₂ = ƛ "x" ⦂ ⟦ ᵐ (Π ζ₂) ⟧ ⇒ π[ k ⦂ k ] ` "x"
prjR {j}{k}     ζ₁ ζ₂ = ƛ "x" ⦂ ⟦ ᵐ (Π ζ₂) ⟧ ⇒ π[i⦂ k ] ` "x" ⟨ (suc k ∸ j) ≤i≤ k ⟩

injL : ∀ {j k} → Row j → Row k → F.Term
injL {j = 1}{k} ζ₁ ζ₂ = ƛ "x" ⦂ ⟦ ᵐ (Σ ζ₁) ⟧ ⇒ ι[ 1 ⦂ k ] ` "x"
injL {j}{k}     ζ₁ ζ₂ = ƛ "x" ⦂ ⟦ ᵐ (Σ ζ₁) ⟧ ⇒
                        case "x" ι[i⦂ k ]⟨ 1 ≤i≤ j , map (⟦_⟧ ∘ ᵐ) ζ₁ ⟩ 
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
Evidence (ζ₁ ⨀ ζ₂ ~ ζ₃) = {!!} -- ⟦ ᵐ (Π ζ₁) ⟧ → ⟦ ᵐ (Π ζ₂) ⟧ → ⟦ ᵐ (Π ζ₃) ⟧
Evidence n = {!!}

```

Rose typing rules and translation to F⊗⊕
```agda
data _❙_⊢_⤳_⦂_ : Context → Env → Term → F.Term → Scheme → Set where
  con : ∀ {P Γ}
    → (n : ℕ)
      ----------------
    → P ❙ Γ ⊢ con n ⤳ con n ⦂ ᵐ Nat

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

Test cases:
```agda
ζ₁ : Row 3
ζ₁ = ("x" ▹ Nat) ∷ "y" ▹ Nat ∷ ("z" ▹ Nat) ∷ []

ζ₂ : Row 2
ζ₂ = ("a" ▹ Nat) ∷ "b" ▹ Nat ∷ []

ζ₃ : Row 5
ζ₃ = ζ₁ ⌢ ζ₂

test-prjL : F.Term
test-prjL = prjL ζ₁ ζ₃

test-prjR : F.Term
test-prjR = prjR ζ₂ ζ₃
```
