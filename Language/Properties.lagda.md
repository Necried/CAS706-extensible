Some properties of typing and translation of Rose terms

```agda
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; _≢_)
open import Data.Product.Base using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Vec using (Vec; []; _∷_; _++_; map; lookup; length; zipWith; foldl′; foldl)
open import Data.Nat.Base using (ℕ; zero; suc; pred; _+_; _∸_; _≤_; z≤n; s≤s)
open import Data.Fin.Base using (Fin; zero; suc; toℕ; fromℕ)
open import Rose
import SystemF as F
open F.Type
open F.Term
open F.VecPattern
open F using (_⨾_⊢_⦂_; ∅; _⸴_)
  renaming (_,_⦂_ to _,ᶠ_⦂_)
open _⨾_⊢_⦂_
```

Operators:
```agda
```

Constrainted type schemes
```agda
record ConstrainedScheme : Set where
  constructor _❙_
  field
    P : Context
    σ : Scheme

ᶜ⟪_⟫ : ConstrainedScheme → F.Type
ᶜ⟪ ∅ ❙ σ ⟫ = ⟦ σ ⟧
ᶜ⟪ (P , v₁ ⦂ ψ₁) ❙ σ ⟫ = ⟪ ψ₁ ⟫ ⇒ ᶜ⟪ P ❙ σ ⟫

toScheme : ConstrainedScheme → Scheme
toScheme (∅ ❙ σ) = σ
toScheme ((P , v ⦂ ψ) ❙ σ) with toScheme (P ❙ σ)
... | QType ρ = QType (ψ ⇒ ρ)
... | `∀ x • newScheme = σ -- is this correct?
```

Generality relation on type schemes:
```agda
id-F : F.Term
id-F = Λ "a" ⇒ ƛ "x" ⦂ (` "a") ⇒ ` "x"

-- TODO: Complete from Figure 9
data _⦂_⊒_ : F.Term → Scheme → Scheme → Set where
  id-⊒ : ∀ {τ₁ τ₂ σ}
    → ⊢ τ₁ ≈ τ₂
      -----------
    → id-F ⦂ σ ⊒ σ

_⦂_⊒ᶜ_ : F.Term → ConstrainedScheme → ConstrainedScheme → Set
C ⦂ cs₁ ⊒ᶜ cs₂ = C ⦂ toScheme cs₁ ⊒ toScheme cs₂ 

lemma10 : ∀ {C P₁ P₂ σ₁ σ₂ Δ Γ}
  → C ⦂ (P₁ ❙ σ₁) ⊒ᶜ (P₂ ❙ σ₂)
    -----------------------------
  → Δ ⨾ Γ ⊢ C ⦂ (⟦ σ₁ ⟧ ⇒ ⟦ σ₂ ⟧)
lemma10 {C}{P₁}{P₂}{σ₁}{σ₂} ord = {!!}
```

```agda
σ₁ : Scheme
σ₁ = `∀ "ζ₁" • ᵐ ((Π `[ ` "ζ₁" ]) ⇒ Nat)

P₁ : Predicate
P₁ = `[ ` "ζ₁" ] ⨀ `[ ` "ζ₂" ] ~ {!`[ ` "ζ₃" ]!}
```

Free variables as a function that calculates them from the input:
```agda
infixl 5 _∪_
_∪_ : F.TyVarEnv → F.TyVarEnv → F.TyVarEnv
Δ₁ ∪ ∅ = Δ₁
Δ₁ ∪ (Δ₂ ⸴ x) = Δ₁ ∪ Δ₂ ⸴ x

{-# TERMINATING #-}
FV-Type : Type → F.TyVarEnv
FV-Row : ∀ {n} → Row n → F.TyVarEnv

FV-Type Nat = ∅
FV-Type (` x) = ∅ ⸴ x
FV-Type (A ⇒ B) = FV-Type A ∪ FV-Type B 
FV-Type (Π x) = FV-Row x
FV-Type (Σ x) = FV-Row x
FV-Type (x ▹ ty) = FV-Type ty

FV-Row ζ = foldl′ (λ ζ′ t → ζ′ ∪ FV-Type t) ∅ ζ 

FV-P : Predicate → F.TyVarEnv
FV-P (ζ₁ ⧀[ _ ] ζ₂) = FV-Row ζ₁ ∪ FV-Row ζ₂
FV-P (ζ₁ ⨀ ζ₂ ~ ζ₃) = FV-Row ζ₁ ∪ FV-Row ζ₂ ∪ FV-Row ζ₃

FV-Context  : Context → F.TyVarEnv
FV-Context ∅ = ∅
FV-Context (ctx , x ⦂ _) = FV-Context ctx ⸴ x

FV-Pψ : Context → Predicate → F.TyVarEnv
FV-Pψ P ψ = FV-Context P ∪ FV-P ψ

-- TODO: Implement FV for Env and Scheme!
FV-PΓσ : Context → Env → Scheme → F.TyVarEnv
FV-PΓσ P Γ σ = {!!}

⟦_⟧ᴾ : Context → F.Context
⟦ ∅ ⟧ᴾ = ∅
⟦ ctx , x ⦂ ψ ⟧ᴾ = ⟦ ctx ⟧ᴾ ,ᶠ x ⦂ ⟪ ψ ⟫

⟦_⟧ᵉ : Env → F.Context
⟦ ∅ ⟧ᵉ = ∅
⟦ e , x ⦂ t ⟧ᵉ = ⟦ e ⟧ᵉ ,ᶠ x ⦂ ⟦ t ⟧
```


```agda
lemma8-1 : ∀ {Δ P F ψ}
  → P ⇒ F ⦂ ψ
  → Δ ≡ FV-Pψ P ψ
  → Δ ⨾ ⟦ P ⟧ᴾ ⊢ F ⦂ ⟪ ψ ⟫
lemma8-1 (pred-var Z) refl = var F.Z
lemma8-1 (pred-var (S v≢y Γ∋v∶ψ)) refl
  with lemma8-1 (pred-var Γ∋v∶ψ) refl
... | var x = var (F.S v≢y x)
-- This appears unsolvable without external knowledge on how to
-- unify row variables.
lemma8-1 {F = π 3 (` x)} (pred-containL {ζ₁ = ζ₁} {ζ₂} {ζ₃} P⇒F⦂ψ) refl = {!!}
lemma8-1 {Δ}{F = π 3 ⟨ t ∷ ts ⟩}
  (pred-containL {ζ₁ = ζ₁} {ζ₂} {ζ₃} P⇒F⦂ψ) refl
  = {!!}
lemma8-1 {F = π 4 (` x)} (pred-containR {ζ₁ = ζ₁} {ζ₂} {ζ₃} P⇒F⦂ψ) refl = {!!}
lemma8-1 {F = π 4 ⟨ x ⟩} (pred-containR {ζ₁ = ζ₁} {ζ₂} {ζ₃} P⇒F⦂ψ) refl = {!!}
lemma8-1 (pred-concat refl) refl = {!!}

lemma8-2 : ∀ {ψ ζ₁ ζ₂ Δ P F D}
  → P ⇒ F ⦂ ψ
  → Δ ≡ FV-Pψ P ψ
  → ψ ≡ ζ₁ ⧀[ D ] ζ₂  -- Why is this "stuck"?
  → Δ ⨾ ⟦ P ⟧ᴾ ⊢ F prjD ⦂ ⟦ ᵐ (Π ζ₂) ⟧ ⇒ ⟦ ᵐ (Π ζ₁) ⟧
lemma8-2 P⇒F⦂ψ refl ψ≡ζ₁⧀ζ₂ = {!!}

lemma8-3 : ∀ {ψ ζ₁ ζ₂ ζ₃ Δ P F}
  → P ⇒ F ⦂ ψ
  → Δ ≡ FV-Pψ P ψ
  → ψ ≡ ζ₁ ⨀ ζ₂ ~ ζ₃ -- Why is this also "stuck"?
  → Δ ⨾ ⟦ P ⟧ᴾ ⊢ F ⦂ ⟦ ᵐ (Π ζ₁) ⟧ ⇒ ⟦ ᵐ (Π ζ₂) ⟧ ⇒ ⟦ ᵐ (Π (ζ₁ ⌢ ζ₂)) ⟧
lemma8-3 P⇒F⦂ψ refl combEq = {!!}

-- The lemmas above should help with proving soundness:
soundness : ∀ {P Γ M E σ Δ}
  → P ❙ Γ ⊢ M ⇝ E ⦂ σ
  → Δ ≡ FV-PΓσ P Γ σ
  → Δ ⨾ ⟦ Γ ⟧ᵉ ⊢ E ⦂ ⟦ σ ⟧
soundness (con {n = n}) refl = con n
soundness (var x Z) refl = var F.Z
soundness (var x (S x₁ Γ∋x)) refl = {!!}
soundness (`let x deriv deriv₁) refl = {!!}
soundness (→I mono-τ mono-v deriv) refl = {!!}
soundness (→E mono-τ mono-v deriv deriv₁) refl = {!!}
soundness (⇒I deriv) refl = {!!}
soundness (⇒E deriv x) refl = {!!}
soundness (∀I deriv x) refl = {!!}
soundness (∀E deriv) refl = {!!}
soundness (▹I deriv) refl = {!!}
soundness (▹E deriv) refl = {!!}
soundness (SIM x deriv) refl = {!!}
soundness (ΠI deriv deriv₁ x) refl = {!!}
soundness (ΠEd deriv x) refl = {!!}
soundness (ΣId deriv x) refl = {!!}
soundness (ΣE deriv deriv₁ x) refl = {!!}
```
