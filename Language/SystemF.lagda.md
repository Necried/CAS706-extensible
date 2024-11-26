This module defines the target language, which is 
a version of System F, extended with arbitrary-width
product and sum types.

```agda
module SystemF where

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; _≢_)
open import Data.String using (String; _≟_)
open import Relation.Nullary.Decidable using ( Dec; yes; no; False; toWitnessFalse)
open import Data.Nat.Base
open import Data.Fin.Base using (Fin; zero; suc; toℕ)
open import Data.Vec using (Vec; []; _∷_; map; lookup)
open import Relation.Nullary.Negation using (¬_; contradiction)
```

Operators:
```agda
infix   4  _∋_⦂_
infixl  4 _∋′_
infix   4 _⨾_⊢_⦂_

infix   5  _,_⦂_
infixl  5 _⸴_


infixl  5  _⊢_type
infix   5  ƛ_⦂_⇒_
infix   5  Λ_⇒_
infix   5  `∀_•_

infixr  7  _⇒_
infixl  7  _·_
infix   9  _＠_
infix   9  `_
```



Types:
```agda
Id : Set
Id = String

data Type : Set where
  Nat      : Type
  `_       : Id → Type
  _⇒_     : Type → Type → Type
  `∀_•_    : Id → Type → Type
  -- Can length `n` be implicit?
  ⊗[_]⟨_⟩  : (n : ℕ) → Vec Type n → Type
  ⊕[_]⟨_⟩  : (n : ℕ) → Vec Type n → Type
```

Terms:
```agda

data Term : Set where
  -- added primitive naturals
  con        : ℕ → Term
  `_         : Id → Term
  -- Lambda argument is annotated with type
  ƛ_⦂_⇒_     : Id → Type → Term → Term
  _·_        : Term → Term → Term
  -- Polymorphic lambda, ∀-intro
  Λ_⇒_      : Id → Term → Term
  -- Polymorphic specialization, ∀-elim
  -- Inspiration from Haskell's TypeApplications syntax
  _＠_       : Term → Type → Term
  -- Product intro and elim Should `n` be implicit/explicit?
  ⟨_⟩        : ∀ {n : ℕ} → Vec Term n → Term
  π          : ℕ → Term → Term
  -- Coproduct intro and elim
  ι          : ℕ → Term → Term
  case_⟪_⟫   : ∀ {n : ℕ} → Term → Vec Term n → Term

```

Type variable environment
```agda
data TyVarEnv : Set where
  ∅ : TyVarEnv
  _⸴_ : TyVarEnv → Id → TyVarEnv

data _∋′_ : TyVarEnv → Id → Set where
  Z : ∀ {Δ x} → Δ ⸴ x ∋′ x
  S : ∀ {Δ x y} → x ≢ y → Δ ∋′ x
    → Δ ⸴ y ∋′ x
```

Type variable judgments
```agda
data _⊢_type      : TyVarEnv → Type → Set
data _⊢[_]_type  : TyVarEnv → (n : ℕ) → Vec Type n → Set

data _⊢[_]_type where
  Δ-[] : ∀ {Δ}
    → Δ ⊢[ 0 ] [] type

  Δ-cons : ∀ {Δ A n} {V : Vec Type n}
    → Δ ⊢ A type
    → Δ ⊢[ n ] V type
      ----------------
    → Δ ⊢[ suc n ] (A ∷ V) type

data _⊢_type where
  Δ-nat : ∀ {Δ}
      ----------
    → Δ ⊢ Nat type

  Δ-var : ∀ {Δ a}
    → Δ ∋′ a
      ---------
    → Δ ⊢ ` a type

  Δ-app : ∀ {Δ A B}
    → Δ ⊢ A type
    → Δ ⊢ B type
      -------------
    → Δ ⊢ A ⇒ B type

  Δ-∀ : ∀ {Δ a A}
    → Δ ⸴ a ⊢ A type
      ---------------
    → Δ ⊢ `∀ a • A type

  Δ-⊗ : ∀ {Δ n} {V : Vec Type n}
    → Δ ⊢[ n ] V type
      ----------------
    → Δ ⊢ ⊗[ n ]⟨ V ⟩ type

  Δ-⊕ : ∀ {Δ n} {V : Vec Type n}
    → Δ ⊢[ n ] V type
      ----------------
    → Δ ⊢ ⊕[ n ]⟨ V ⟩ type
```

Substitution on types
This doesn't pass termination checking!
```agda
infix 9 _ᵗ[_≔_]
{-# TERMINATING #-}
_ᵗ[_≔_] : Type → Id → Type → Type
Nat ᵗ[ a ≔ B ]           = Nat
(` x) ᵗ[ a ≔ B ] with x ≟ a
... | yes _             = B
... | no  _             = ` x
(T ⇒ U) ᵗ[ a ≔ B ]      = T ᵗ[ a ≔ B ] ⇒ U ᵗ[ a ≔ B ]
(`∀ x • ty) ᵗ[ a ≔ B ] with x ≟ a
... | yes  _            = `∀ x • ty
... | no   _            = `∀ x • ty ᵗ[ a ≔ B ]
⊗[ n ]⟨ tys ⟩ ᵗ[ a ≔ B ] = ⊗[ n ]⟨  map _ᵗ[ a ≔ B ] tys  ⟩
⊕[ n ]⟨ tys ⟩ ᵗ[ a ≔ B ] = ⊕[ n ]⟨  map _ᵗ[ a ≔ B ] tys  ⟩
```

Type judgment on terms
```agda
data Context : Set where
  ∅ : Context
  _,_⦂_ : Context → Id → Type → Context

data _∋_⦂_ : Context → Id → Type → Set where
  Z : ∀ {Γ x A} → Γ , x ⦂ A ∋ x ⦂ A
  S : ∀ {Γ x y A B} → x ≢ y → Γ ∋ x ⦂ A
    → Γ , y ⦂ B ∋ x ⦂ A
```

```agda
data _⨾_⊢[_]_⦂_ : TyVarEnv → Context → (n : ℕ) → Vec Term n → Vec Type n → Set
data _⨾_⊢_⦂_ : TyVarEnv → Context → Term → Type → Set

data _⨾_⊢[_]_⦂_ where
  Δ⨾Γ-[] : ∀ {Δ Γ}
      ----------------
    → Δ ⨾ Γ ⊢[ 0 ] [] ⦂ []

  Δ⨾Γ-cons : ∀ {Δ Γ n E A} {VecE : Vec Term n} {VecA : Vec Type n}
    → Δ ⨾ Γ ⊢ E ⦂ A
    → Δ ⨾ Γ ⊢[ n ] VecE ⦂ VecA
      ----------------
    → Δ ⨾ Γ ⊢[ suc n ] (E ∷ VecE) ⦂ (A ∷ VecA)
 

data _⨾_⊢_⦂_ where
  con : ∀ {Δ Γ}
    → (n : ℕ)
      ----------
    → Δ ⨾ Γ ⊢ con n ⦂ Nat

  var : ∀ {Δ Γ A x}
    → Γ ∋ x ⦂ A
      -------------
    → Δ ⨾ Γ ⊢ ` x ⦂ A

  ∀I : ∀ {Δ Γ a E A}
    → Δ ⸴ a ⨾ Γ ⊢ E ⦂ A
    → ¬ (Δ ∋′ a)
      ------------------
    → Δ ⨾ Γ ⊢ Λ a ⇒ E ⦂ `∀ a • A

  ∀E : ∀ {Δ Γ E a A B}
    → Δ ⨾ Γ ⊢ E ⦂ `∀ a • A
    → Δ ⊢ B type
      ---------------------
    → Δ ⨾ Γ ⊢ E ＠ B  ⦂ A ᵗ[ a ≔ B ]

  ⇒I : ∀ {Δ Γ x A E B}
    → Δ ⊢ A type
    → Δ ⨾ Γ , x ⦂ A ⊢ E ⦂ B
      --------------------
    → Δ ⨾ Γ ⊢ ƛ x ⦂ A ⇒ E ⦂ A ⇒ B

  ⇒E : ∀ {Δ Γ A B F E}
    → Δ ⨾ Γ ⊢ F ⦂ A ⇒ B
    → Δ ⨾ Γ ⊢ E ⦂ A
      ------------------
    → Δ ⨾ Γ ⊢ F · E ⦂ B

  ⊗I : ∀ {Δ Γ} {n : ℕ} {VecE : Vec Term n} {VecA : Vec Type n}
    → Δ ⨾ Γ ⊢[ n ] VecE ⦂ VecA
      -------------------------
    → Δ ⨾ Γ ⊢ ⟨ VecE ⟩ ⦂ ⊗[ n ]⟨ VecA ⟩

  ⊗E : ∀ {Δ Γ E n} {VecA : Vec Type n}
    → Δ ⨾ Γ ⊢ E ⦂ ⊗[ n ]⟨ VecA ⟩
    → (idx : Fin n)
      ----------------------------
    → Δ ⨾ Γ ⊢ π (toℕ idx) E ⦂ lookup VecA idx

  ⊕I : ∀ {Δ Γ E n} {VecA : Vec Type n}
    → (idx : Fin n)
    → Δ ⨾ Γ ⊢ E ⦂ lookup VecA idx
      ------------------
    → Δ ⨾ Γ ⊢ ι (toℕ idx) E ⦂ ⊕[ n ]⟨ VecA ⟩

  ⊕E : ∀ {Δ Γ E n B} {VecA : Vec Type n} {VecF : Vec Term n}
    → Δ ⨾ Γ ⊢ E ⦂ ⊕[ n ]⟨ VecA ⟩
    → Δ ⨾ Γ ⊢[ n ] VecF ⦂ map (_⇒ B) VecA
      -------------------------------------
    → Δ ⨾ Γ ⊢ case E ⟪ VecF ⟫ ⦂ B
```

Nicer tupling syntax:
```agda
pattern _﹐_ y z = y ∷ z ∷ []
pattern _﹐_﹐_ x y z = x ∷ y ∷ z ∷ []
pattern _﹐_﹐_﹐_ w x y z = w ∷ x ∷ y ∷ z ∷ []
```

Examples:
```agda
pairNat : Term
pairNat = ⟨ con 3 ﹐ con 4 ⟩

projPairNat : Term
projPairNat = π zero pairNat

-- Not auto-able, nor refinable, for some of the holes
⊢projPairNat : ∀ {Δ Γ} → Δ ⨾ Γ ⊢ projPairNat ⦂ Nat
⊢projPairNat = ⊗E (⊗I (Δ⨾Γ-cons (con 3) (Δ⨾Γ-cons (con 4) Δ⨾Γ-[]))) zero

sumNat : Term
sumNat = ι 2 (con 10)

idFunc : Term
idFunc = Λ "a" ⇒ ƛ "x" ⦂ ` "a" ⇒ ` "x"

caseNat : Term
caseNat = case sumNat ⟪ (idFunc ＠ Nat) ﹐ (idFunc ＠ Nat) ﹐ (idFunc ＠ Nat) ⟫

⊢caseNat : ∀ {Γ} → ∅ ⨾ Γ ⊢ caseNat ⦂ Nat
⊢caseNat = ⊕E (⊕I (suc (suc zero)) (con 10))
  (Δ⨾Γ-cons (∀E idTy Δ-nat)
  (Δ⨾Γ-cons (∀E idTy Δ-nat)
  (Δ⨾Γ-cons (∀E idTy Δ-nat)
  Δ⨾Γ-[])))
  where
    idTy : ∀ {Γ} → ∅ ⨾ Γ ⊢ idFunc ⦂ `∀ "a" • (` "a" ⇒ ` "a")
    idTy = ∀I (⇒I (Δ-var Z) (var Z)) (λ ())
```
