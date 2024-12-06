This defines the Rose language as given in Chapter 4 of the paper.

```agda
{-# OPTIONS --allow-unsolved-metas #-}
module Rose where

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; _≢_)
open import Data.String using (String; _≟_)
open import Relation.Nullary.Decidable using ( Dec; yes; no; False; toWitnessFalse)
open import Data.Product using (_×_; proj₁; proj₂; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Function.Base using (_$_)
open import Data.Fin.Base using (Fin; zero; suc; toℕ; fromℕ)
open import Relation.Nullary.Negation using (¬_; contradiction)
open import Data.Nat.Base using (ℕ; zero; suc; pred; _+_; _∸_; _≤_; z≤n; s≤s)
open import Data.Nat using (_≤?_)
open import Data.Vec using (Vec; []; _∷_; _++_; map; lookup; length; zipWith)
open import Function.Base using (_∘_)
import SystemF as F
open F using (π[_⦂_]_; ι[_⦂_]_; π[i⦂_]_⟨_≤i≤_⟩; case_ι[i⦂_]⟨_≤i≤_,_⟩; [_⋯_])
open F.VecPattern
open import Utils using (∸cancel; ∸-≤-suc)
```

The syntax of rows, predicates and types.
These three types are mutually recursive.

Operators
```agda
infix   4  _∋_⦂_
infix   4  _∋_꞉_
infix   4  ⊢_≈_
infix   4  _❙_⊢_⇝_⦂_
infix   4  _⇒_⦂_

infixl  5  _,_⦂_
infix   5  ƛ_⇒_
infix   5 _⨀_~_ 
infixl  5 _⧀[_]_
infixr  7  _⇒_
infixr  7  _ᵐ⇒_
infixl  7  _★_

infix   9  `_
```

Direction of projections and injections
```agda
data Direction : Set where
  L : Direction
  R : Direction
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
  _⧀[_]_ : ∀ {i j} → Row i → Direction → Row j → Predicate
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

data Term : Set where
  con    : ℕ → Term
  `_     : Id → Term
  ƛ_⇒_   : Id → Term → Term
  _·_    : Term → Term → Term
  `let_⦂_＝_`in_ : Id → Scheme → Term → Term → Term
  _▹_ : Label → Term → Term
  _/_ : Term → Label → Term
  prj[_]_ : Direction → Term → Term
  _★_ : Term → Term → Term
  inj[_]_ : Direction → Term → Term
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

Translating from Rose types and predicates to F⊗⊕
```agda
open F.Type

{-# TERMINATING #-}
⟦_⟧ : Scheme → F.Type
⟪_⟫ : Predicate → F.Type

⟦ ᵐ Nat ⟧ = Nat
⟦ ᵐ (` x) ⟧ = ` x
⟦ ᵐ (A ⇒ B) ⟧ = ⟦ ᵐ A ⟧ ⇒ ⟦ ᵐ B ⟧
⟦ ᵐ (Π ζ) ⟧ = ⊗⟨ map (⟦_⟧ ∘ ᵐ) ζ ⟩
⟦ ᵐ (Σ ζ) ⟧ = ⊕⟨ map (⟦_⟧ ∘ ᵐ) ζ ⟩
⟦ ᵐ (ℓ ▹ τ) ⟧ = ⟦ ᵐ τ ⟧
⟦ QType (ψ ⇒ ρ) ⟧ = ⟪ ψ ⟫ ⇒ ⟦ QType ρ ⟧
⟦ `∀ x • s ⟧ = `∀ x • ⟦ s ⟧

⟪ ζ₁ ⧀[ _ ] ζ₂ ⟫ = ⊗⟨ ⟦ ᵐ (Π ζ₂) ⟧ ⇒ ⟦ ᵐ (Π ζ₁) ⟧ ∷
                      ⟦ ᵐ (Σ ζ₁) ⟧ ⇒ ⟦ ᵐ (Σ ζ₂) ⟧ ∷ [] ⟩
⟪ ζ₁ ⨀ ζ₂ ~ ζ₃ ⟫ = ⊗⟨
  ⟦ ᵐ (Π ζ₁) ⟧ ⇒ ⟦ ᵐ (Π ζ₂) ⟧ ⇒ ⟦ ᵐ (Π ζ₃) ⟧ ∷
  (`∀ "a" • (⟦ ᵐ (Σ ζ₁) ⟧ ⇒ ` "a")
         ⇒ (⟦ ᵐ (Σ ζ₂) ⟧ ⇒ ` "a") ⇒  ⟦ ᵐ (Σ ζ₃) ⟧ ⇒ ` "a") ∷
  ⟪ ζ₁ ⧀[ L ] ζ₃ ⟫ ∷
  ⟪ ζ₂ ⧀[ R ] ζ₃ ⟫ ∷ [] ⟩
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

injR : ∀ {j k} → Row j → Row k → {j ≤ k} → F.Term
injR {j = 1}{k} ζ₁ ζ₂ = ƛ "x" ⦂ ⟦ ᵐ (Σ ζ₁) ⟧ ⇒ ι[ k ⦂ k ] ` "x"
injR {j}{k} ζ₁ ζ₂ {j≤k} rewrite ∸cancel j (suc k) (∸-≤-suc j≤k)
  = ƛ "x" ⦂ ⟦ ᵐ (Σ ζ₁) ⟧ ⇒
      case "x" ι[i⦂ k ]⟨ (suc k ∸ j) ≤i≤ k , map (⟦_⟧ ∘ ᵐ) ζ₁ ⟩

concat : ∀ {j k} → Row j → Row k → F.Term
concat {j}{k} ζ₁ ζ₂ = ƛ "x" ⦂ ⟦ ᵐ (Π ζ₁) ⟧ ⇒
                (ƛ "y" ⦂ ⟦ ᵐ (Π ζ₂) ⟧ ⇒
                  ⟨ map (λ idx → π[ idx ⦂ j ] ` "x") [ 1 ⋯ j ] ++
                    map (λ idx → π[ idx ⦂ k ] ` "y") [ 1 ⋯ k ] ⟩)

branch : ∀ {j k} → Row j → Row k → F.Term
branch {j} {k} ζ₁ ζ₂ =
  Λ "a" ⇒
    ƛ "f" ⦂ (⟦ ᵐ (Σ ζ₁) ⟧ ⇒ ` "a") ⇒
    ƛ "g" ⦂ (⟦ ᵐ (Σ ζ₂) ⟧ ⇒ ` "a") ⇒
    ƛ "z" ⦂ ⟦ ᵐ (Σ (ζ₁ ⌢ ζ₂)) ⟧ ⇒
      case (` "z") ⟪ zipWith case-branch (ζ₁ ⌢ ζ₂) [ 1 ⋯ j + k ] ⟫
  where
    case-branch : Type → ℕ → F.Term
    case-branch τ i with i ≤? j
    ... | yes _ = ƛ "x" ⦂ ⟦ ᵐ τ ⟧ ⇒ ` "f" · (ι[ i ⦂ j ] ` "x")
    ... | no _  = ƛ "y" ⦂ ⟦ ᵐ τ ⟧ ⇒ ` "g" · (ι[ i ∸ j ⦂ k ] ` "y")
```

Free variables in the context and environment:
```agda
_∉FV[_,_] : Id → Context → Env → Set
y ∉FV[ P , Γ ] = ∀ {t ψ} → ¬ (Γ ∋ y ⦂ t) × ¬ (P ∋ y ꞉ ψ)
```

Type substitutions into schemes
```agda
infix 9 _ᵐ[_≔_]
infix 9 _ᵗ[_≔_]
infix 9 _ℚ[_≔_]
infix 9 _ᵖ[_≔_]

{-# TERMINATING #-}
_ᵐ[_≔_] : Type → Id → Type → Type
Nat ᵐ[ t ≔ τ ] = Nat
(` x) ᵐ[ t ≔ τ ] with x ≟ t
... | yes _          = τ
... | no  _          = ` x
(T ⇒ U) ᵐ[ t ≔ τ ] = T ᵐ[ t ≔ τ ] ⇒ U ᵐ[ t ≔ τ ]
(Π ζ) ᵐ[ t ≔ τ ] = Π (map _ᵐ[ t ≔ τ ] ζ)
(Σ ζ) ᵐ[ t ≔ τ ] = Σ (map _ᵐ[ t ≔ τ ] ζ)
(x ▹ ty) ᵐ[ t ≔ τ ] = x ▹ ty ᵐ[ t ≔ τ ]

_ᵖ[_≔_] : Predicate → Id → Type → Predicate
(ζ₁ ⧀[ D ] ζ₂) ᵖ[ t ≔ τ ] = (map _ᵐ[ t ≔ τ ] ζ₁) ⧀[ D ] (map _ᵐ[ t ≔ τ ] ζ₂)
(ζ₁ ⨀ ζ₂ ~ ζ₃) ᵖ[ t ≔ τ ] =
  map _ᵐ[ t ≔ τ ] ζ₁ ⨀ map _ᵐ[ t ≔ τ ] ζ₂ ~ map _ᵐ[ t ≔ τ ] ζ₃ 

_ℚ[_≔_] : ℚType → Id → Type → ℚType
(` A) ℚ[ t ≔ τ ] = ` (A ᵐ[ t ≔ τ ])
(ψ ⇒ ρ) ℚ[ t ≔ τ ] = ψ ᵖ[ t ≔ τ ] ⇒ ρ ℚ[ t ≔ τ ]

_ᵗ[_≔_] : Scheme → Id → Type → Scheme
QType Q ᵗ[ t ≔ τ ] = QType (Q ℚ[ t ≔ τ ])
(`∀ t′ • σ) ᵗ[ t ≔ τ ] with t′ ≟ t
... | yes _ = `∀ t′ • σ
... | no  _ = `∀ t′ • (σ ᵗ[ t ≔ τ ])
```

The augmented entailment judgment P ⇒ F ∶ ψ denotes that
F is an F⊗⊕ term giving evidence for predicate ψ
```agda

data _⇒_⦂_ : Context → F.Term → Predicate → Set where
  pred-var : ∀ {P v ψ}
    → P ∋ v ꞉ ψ
    ------------
    → P ⇒ ` v ⦂ ψ

  -- NOTE: I think paper has a typo here.
  pred-containL : ∀ {P F}{j k : ℕ}
                    {ζ₁ : Row j}{ζ₂ : Row k}{ζ₃}
    → P ⇒ F ⦂ (ζ₁ ⨀ ζ₂ ~ ζ₃)
      -----------------------
    → P ⇒ π 3 F ⦂ ζ₁ ⧀[ L ] ζ₃ -- paper has this as ζ₂. I think its wrong.

  pred-containR : ∀ {P F}{j k : ℕ}
                    {ζ₁ : Row j}{ζ₂ : Row k}{ζ₃}
    → P ⇒ F ⦂ (ζ₁ ⨀ ζ₂ ~ ζ₃)
      -----------------------
    → P ⇒ π 4 F ⦂ ζ₂ ⧀[ R ] ζ₂

  pred-concat : ∀ {P j k}{ζ₁ : Row j}{ζ₂ : Row k}{ζ₃}
    → ζ₁ ⌢ ζ₂ ≡ ζ₃
      --------------------------------------------------------
    → P ⇒ ⟨ [ concat ζ₁ ζ₂ ﹐
               branch ζ₁ ζ₂ ﹐
               ⟨ (prjL ζ₁ ζ₃)﹐ (injL ζ₁ ζ₃) ⟩ ﹐
               ⟨ (prjR ζ₂ ζ₃)﹐ (injL ζ₂ ζ₃) ⟩ ]
           ⟩ ⦂ ζ₁ ⨀ ζ₂ ~ ζ₃
```

Extension of the equivalence relation ζ₁ ~ ζ₂ on rows
to an equivalence ⊢ τ₁ ≈ τ₂ on types.

This extension serves to relate singleton records/variants
to their underlying type
```agda
data ⊢_≈_ : Type → Type → Set where
  ≈-refl : ∀ {τ}
    → ⊢ τ ≈ τ

  ≈-sym : ∀ {τ₁ τ₂}
    → ⊢ τ₁ ≈ τ₂
      --------
    → ⊢ τ₂ ≈ τ₁

  ≈-trans : ∀ {τ₁ τ₂ τ₃}
    → ⊢ τ₁ ≈ τ₂
    → ⊢ τ₂ ≈ τ₃
      ----------
    → ⊢ τ₁ ≈ τ₃

  ≈-Π : ∀ {τ}
    → ⊢ Π (τ ∷ []) ≈ τ

  ≈-Σ : ∀ {τ}
    → ⊢ Σ (τ ∷ []) ≈ τ

  ≈-Π≡ : ∀ {n : ℕ}{ζ₁ ζ₂ : Row n}
    → ζ₁ ≡ ζ₂
      ----------
    → ⊢ Π ζ₁ ≈ Π ζ₂

  ≈-Σ≡ : ∀ {n : ℕ}{ζ₁ ζ₂ : Row n}
    → ζ₁ ≡ ζ₂
      ----------
    → ⊢ Σ ζ₁ ≈ Σ ζ₂
```

Rose typing rules and translation to F⊗⊕
```agda
data _❙_⊢_⇝_⦂_ : Context → Env → Term → F.Term → Scheme → Set where
  con : ∀ {P Γ n}
      ----------------
    → P ❙ Γ ⊢ con n ⇝ con n ⦂ ᵐ Nat

  var : ∀ {P Γ x σ}
    → MonoType σ
    → Γ ∋ x ⦂ σ
      -------------
    → P ❙ Γ ⊢ ` x ⇝ ` x ⦂ σ

  `let : ∀ {P Γ M N E F σ τ x}
    → MonoType τ
    → P ❙ Γ ⊢ M ⇝ E ⦂ σ
    → P ❙ Γ , x ⦂ σ ⊢ N ⇝ F ⦂ τ
      ---------------------------
    → P ❙ Γ ⊢ (`let x ⦂ σ ＝ M `in N) ⇝ (ƛ x ⦂ ⟦ σ ⟧ ⇒ F) · E ⦂ τ

  →I : ∀ {P Γ M E τ v x}
    → (mono-τ : MonoType τ)
    → (mono-v : MonoType v)
    → P ❙ Γ , x ⦂ τ ⊢ M ⇝ E ⦂ v
      ---------------------------
    → P ❙ Γ ⊢ ƛ x ⇒ M ⇝ (ƛ x ⦂ ⟦ τ ⟧ ⇒ E) ⦂ (τ ᵐ⇒ v) {mono-τ} {mono-v}

  →E : ∀ {P Γ M N E F τ v}
    → (mono-τ : MonoType τ)
    → (mono-v : MonoType v)
    → P ❙ Γ ⊢ M ⇝ F ⦂ (τ ᵐ⇒ v) {mono-τ} {mono-v}
    → P ❙ Γ ⊢ N ⇝ E ⦂ τ
      ----------------------
    → P ❙ Γ ⊢ M · N ⇝ F · E ⦂ v

  ⇒I : ∀ {P ψ Γ M E v ρ}
    → P , v ⦂ ψ ❙ Γ ⊢ M ⇝ E ⦂ QType ρ
      ---------------------------
    → P ❙ Γ ⊢ M ⇝ ƛ v ⦂ ⟪ ψ ⟫ ⇒ E ⦂ QType (ψ ⇒ ρ)

  ⇒E : ∀ {P Γ E F M N ψ ρ}
    → P ❙ Γ ⊢ M ⇝ F ⦂ QType (ψ ⇒ ρ)
    → P ⇒ E ⦂ ψ
      --------------------------------
    → P ❙ Γ ⊢ M · N ⇝ F · E ⦂ QType ρ

  ∀I : ∀ {P Γ M E σ t}
    → P ❙ Γ ⊢ M ⇝ E ⦂ σ
    → t ∉FV[ P , Γ ]
      ------------------------
    → P ❙ Γ ⊢ M ⇝ Λ t ⇒ E ⦂ (`∀ t • σ)

  ∀E : ∀ {P Γ M E t σ}{τ : Type}
    → P ❙ Γ ⊢ M ⇝ E ⦂ `∀ t • σ
      ---------------------------
    → P ❙ Γ ⊢ M ⇝ E ＠ ⟦ ᵐ τ ⟧ ⦂ σ ᵗ[ t ≔ τ ]

  ▹I : ∀ {P Γ M E ℓ τ}
    → P ❙ Γ ⊢ M ⇝ E ⦂ ᵐ τ
      -------------------------
    → P ❙ Γ ⊢ ℓ ▹ M ⇝ E ⦂ ᵐ (ℓ ▹ τ)

  ▹E : ∀ {P Γ M E ℓ τ}
    → P ❙ Γ ⊢ M ⇝ E ⦂ ᵐ (ℓ ▹ τ)
      -------------------------
    → P ❙ Γ ⊢ M / ℓ ⇝ E ⦂ ᵐ τ

  SIM : ∀ {P Γ M E τ v}
    → ⊢ τ ≈ v
    → P ❙ Γ ⊢ M ⇝ E ⦂ ᵐ τ
      -------------------
    → P ❙ Γ ⊢ M ⇝ E ⦂ ᵐ v

  ΠI : ∀ {P Γ M₁ M₂ E₁ E₂ F} {j k : ℕ}
         {ζ₁ : Row j} {ζ₂ : Row k}{ζ₃}
    → P ❙ Γ ⊢ M₁ ⇝ E₁ ⦂ ᵐ (Π ζ₁)
    → P ❙ Γ ⊢ M₂ ⇝ E₂ ⦂ ᵐ (Π ζ₂)
    → P ⇒ F ⦂ ζ₁ ⨀ ζ₂ ~ ζ₃
      -------------------------
    → P ❙ Γ ⊢ M₁ ★ M₂ ⇝ π 1 F · E₁ · E₂ ⦂ ᵐ (Π ζ₃)

  ΠEd : ∀ {P Γ M D E F}{j k : ℕ}
          {ζ₁ : Row j} {ζ₂ : Row k}
    → P ❙ Γ ⊢ M ⇝ E ⦂ ᵐ (Π ζ₂)
    → P ⇒ F ⦂ ζ₁ ⧀[ D ] ζ₂
      -------------------------
    → P ❙ Γ ⊢ prj[ D ] M ⇝ π 1 F · E ⦂ ᵐ (Π ζ₁)

  ΣId : ∀ {P Γ M D E F}{j k : ℕ}
          {ζ₁ : Row j} {ζ₂ : Row k}
    → P ❙ Γ ⊢ M ⇝ E ⦂ ᵐ (Σ ζ₁)
    → P ⇒ F ⦂ ζ₁ ⧀[ D ] ζ₂
      -------------------------
    → P ❙ Γ ⊢ inj[ D ] M ⇝ π 2 F · E ⦂ ᵐ (Σ ζ₂)

  ΣE : ∀ {P Γ M₁ M₂ E₁ E₂ F τ} {j k : ℕ}
         {ζ₁ : Row j} {ζ₂ : Row k}{ζ₃}
    → P ❙ Γ ⊢ M₁ ⇝ E₁ ⦂ ᵐ (Σ ζ₁ ⇒ τ)
    → P ❙ Γ ⊢ M₂ ⇝ E₂ ⦂ ᵐ (Σ ζ₂ ⇒ τ)
    → P ⇒ F ⦂ ζ₁ ⨀ ζ₂ ~ ζ₃
      -------------------------
    → P ❙ Γ ⊢ M₁ ▿ M₂ ⇝ (π 2 F ＠ ⟦ ᵐ τ ⟧) · E₁ · E₂ ⦂ ᵐ (Π ζ₃)

```

Test cases for the entailment operations:
```agda
ζ₁ : Row 3
ζ₁ = ("x" ▹ Nat) ∷ "y" ▹ Nat ∷ ("z" ▹ Nat) ∷ []

ζ₂ : Row 2
ζ₂ = ("a" ▹ Nat) ∷ "b" ▹ Nat ∷ []

ζ₃ : Row 5
ζ₃ = ζ₁ ⌢ ζ₂

test-prjL : prjL ζ₁ ζ₃ ≡ ƛ "x" ⦂ ⊗⟨ Nat ∷ Nat ∷ Nat ∷ Nat ∷ Nat ∷ [] ⟩ ⇒
                           ⟨ π 1 (` "x") ∷ π 2 (` "x") ∷ π 3 (` "x") ∷ [] ⟩
test-prjL = refl

test-prjR : prjR ζ₂ ζ₃ ≡ ƛ "x" ⦂ ⊗⟨ Nat ∷ Nat ∷ Nat ∷ Nat ∷ Nat ∷ [] ⟩ ⇒
                           ⟨ π 4 (` "x") ∷ π 5 (` "x") ∷ [] ⟩
test-prjR = refl

test-injL : injL ζ₁ ζ₃ ≡ ƛ "x" ⦂ ⊕⟨ Nat ∷ Nat ∷ Nat ∷ [] ⟩ ⇒
                          case ` "x" ⟪
                           (ƛ "y" ⦂ Nat ⇒ ι 1 (` "y")) ∷
                           (ƛ "y" ⦂ Nat ⇒ ι 2 (` "y")) ∷
                           (ƛ "y" ⦂ Nat ⇒ ι 3 (` "y")) ∷ [] ⟫
test-injL = refl

test-injR : injR ζ₂ ζ₃ {s≤s (s≤s z≤n)} ≡
  ƛ "x" ⦂ ⊕⟨ Nat ∷ Nat ∷ [] ⟩ ⇒
    case ` "x" ⟪
      (ƛ "y" ⦂ Nat ⇒ ι 4 (` "y")) ∷
      (ƛ "y" ⦂ Nat ⇒ ι 5 (` "y")) ∷ [] ⟫
test-injR = refl

test-concat : concat ζ₁ ζ₂ ≡
  ƛ "x" ⦂ ⊗⟨ Nat ∷ Nat ∷ Nat ∷ [] ⟩ ⇒
   (ƛ "y" ⦂ ⊗⟨ Nat ∷ Nat ∷ [] ⟩ ⇒
   ⟨ π 1 (` "x") ∷
     π 2 (` "x") ∷
     π 3 (` "x") ∷
     π 1 (` "y") ∷
     π 2 (` "y") ∷ [] ⟩)
test-concat = refl

test-branch : branch ζ₁ ζ₂ ≡
  Λ "a" ⇒
    (ƛ "f" ⦂ (⊕⟨ Nat ∷ Nat ∷ Nat ∷ [] ⟩ ⇒ ` "a") ⇒
      (ƛ "g" ⦂ (⊕⟨ Nat ∷ Nat ∷ [] ⟩ ⇒ ` "a") ⇒
        (ƛ "z" ⦂ (⊕⟨ Nat ∷ Nat ∷ Nat ∷ Nat ∷ Nat ∷ [] ⟩) ⇒
        case ` "z" ⟪
          (ƛ "x" ⦂ Nat ⇒ ` "f" · ι 1 (` "x")) ∷
          (ƛ "x" ⦂ Nat ⇒ ` "f" · ι 2 (` "x")) ∷
          (ƛ "x" ⦂ Nat ⇒ ` "f" · ι 3 (` "x")) ∷
          (ƛ "y" ⦂ Nat ⇒ ` "g" · ι 1 (` "y")) ∷
          (ƛ "y" ⦂ Nat ⇒ ` "g" · ι 2 (` "y")) ∷ [] ⟫ )))
test-branch = refl
```

Test cases for Rose typing rules and translations.
```agda
test-combine-access : Term
test-combine-access =
  (prj[ L ] ("x" ▹ con 10 ★ "y" ▹ con 42)) / "x"

disgustingly-long-test-combine-access-F : F.Term
disgustingly-long-test-combine-access-F =
  π 1
    (π 3
       ⟨
         [ concat (("x" ▹ Nat) ∷ []) (("y" ▹ Nat) ∷ []) ﹐
           branch (("x" ▹ Nat) ∷ []) (("y" ▹ Nat) ∷ []) ﹐
           ⟨ prjL (("x" ▹ Nat) ∷ []) rec ﹐ injL (("x" ▹ Nat) ∷ []) rec ⟩ ﹐
           ⟨ prjR (("y" ▹ Nat) ∷ []) rec ﹐ injL (("y" ▹ Nat) ∷ []) rec ⟩
         ]
    ⟩)
    ·
    (π 1
      ⟨
      [ concat (("x" ▹ Nat) ∷ []) (("y" ▹ Nat) ∷ []) ﹐
        branch (("x" ▹ Nat) ∷ []) (("y" ▹ Nat) ∷ []) ﹐
        ⟨ prjL (("x" ▹ Nat) ∷ []) rec ﹐ injL (("x" ▹ Nat) ∷ []) rec ⟩ ﹐
        ⟨ prjR (("y" ▹ Nat) ∷ []) rec ﹐ injL (("y" ▹ Nat) ∷ []) rec ⟩
      ]
      ⟩
      · con 10
      · con 42)
  where
    rec : Row 2
    rec = "x" ▹ Nat ∷ "y" ▹ Nat ∷ []

manually-simplified-not-reducing-entailments : F.Term
manually-simplified-not-reducing-entailments =
  prjL (("x" ▹ Nat) ∷ []) rec
  · concat (("x" ▹ Nat) ∷ []) (("y" ▹ Nat) ∷ [])
  · con 10
  · con 42
  where
    rec : Row 2
    rec = "x" ▹ Nat ∷ "y" ▹ Nat ∷ []

manually-simplified-reduced-entailments : F.Term
manually-simplified-reduced-entailments =
  (ƛ "x" ⦂ ⊗⟨ Nat ﹐ Nat ⟩ ⇒ π 1 (` "x"))
  · (ƛ "x" ⦂ ⊗⟨ Nat ∷ [] ⟩ ⇒ (ƛ "y" ⦂ ⊗⟨ Nat ∷ [] ⟩ ⇒ ⟨ (` "x") ﹐ (` "y") ⟩))
  · con 10
  · con 42

_ : ∅ ❙ ∅ ⊢ test-combine-access ⇝ disgustingly-long-test-combine-access-F ⦂ ᵐ Nat
_ = ▹E $ SIM ≈-Π $ ΠEd
     (ΠI
       (SIM (≈-sym ≈-Π) (▹I con))
       (SIM (≈-sym ≈-Π) (▹I con))
       (pred-concat refl))
     (pred-containL (pred-concat refl))

-- Concatenate two records and project the "left" argument:
test-concat-proj : Term
test-concat-proj = ƛ "m" ⇒ ƛ "n" ⇒ (prj[ L ] (` "m" ★ ` "n")) / "x"

-- type-concat-proj : Type
-- type-concat-proj = `∀ t • `∀ z₁ • `∀ z₂ • ("x" ▹ ` "t") ⧀[ L ] ()
```

