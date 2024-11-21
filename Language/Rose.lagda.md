This defines the Rose language as given in Chapter 4 of the paper.

```agda
module Rose where

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; _≢_)
open import Data.String using (String; _≟_)
open import Relation.Nullary.Decidable using ( Dec; yes; no; False; toWitnessFalse)

```

The syntax of rows, predicates and types.
These three types are mutually recursive.

Operators
```agda
infix   4  _∋_⦂_
infixl  5  _,_⦂_

infixr  7  _⇒_

infix   5  ƛ_⇒_
infixl  7  _·_
infix   9  `_
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
  Π_ : Predicate → Type
  Σ_ : Predicate → Type
  _▹_ : Label → Type → Type

data Row where
  _▹_,_ : Label → Type → Row
  ∎ᵣ : Row
```


Terms, with qualified types ,schemes and direction
```agda
data ℚType : Set where
  `_ : Type → ℚType
  _⇒_ : Predicate → ℚType

data Scheme : Set where
  QType : ℚType → Scheme
  `∀_•_ : Id → Scheme
  -- Omitted row polymorphic variables, could be
  -- combined with the ∀ abouve

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
  _⋆_ : Term → Term → Term
  inj⟦_⟧_ : Direction → Term → Term
  _▿_ : Term → Term → Term
```

Context for predicates and environment for types
```agda
data Context : Set where
  ∅ : Context
  _,_⦂_ : Context → Id → Predicate → Context

data Env : Set where
  ∅ : Env
  _,_⦂_ : Env → Id → Type → Env
```

```agda
data _∋_⦂_ : Env → Id → Type → Set where
  Z : ∀ {Γ x A} → Γ , x ⦂ A ∋ x ⦂ A
  S : ∀ {Γ x y A B} → x ≢ y → Γ ∋ x ⦂ A
    → Γ , y ⦂ B ∋ x ⦂ A
```

F⊗⊕ type and terms
```agda
data TermF⊗⊕ : Set where
```

Rose typing rules and translation to F⊗⊕
```agda
data _❙_⊢_⤳_⦂_ : Context → Env → Term → TermF⊗⊕ → Type → Set where
```
