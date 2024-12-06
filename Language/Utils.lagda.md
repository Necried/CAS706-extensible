```agda
module Utils where

open import Data.Nat.Base using (ℕ; zero; suc; pred; _+_; _∸_)
open import Data.Nat using (_≤_; _≤?_; z≤n; s≤s)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; _≢_)
open Eq.≡-Reasoning
open import Data.Nat.Properties using (n∸n≡0; m≤n⇒n∸m≤n)
open import Data.Bool.Base using (T)
open import Relation.Nullary.Decidable using
  (⌊_⌋; True; toWitness)

```

```agda
∸suc-comm : ∀ (a b : ℕ) → b ≤ a → suc (a ∸ b) ≡ suc a ∸ b
∸suc-comm zero zero b≤a = refl
∸suc-comm (suc a) zero b≤a = refl
∸suc-comm (suc a) (suc b) (s≤s b≤a) = ∸suc-comm a b b≤a

∸cancel : ∀ (j k : ℕ) → j ≤ k → j ≡ k ∸ (k ∸ j)
∸cancel zero k j≤k = sym (n∸n≡0 k)
∸cancel (suc j) (suc k) (s≤s j≤k) = sym (begin
  suc k ∸ (suc k ∸ suc j) ≡⟨⟩
  suc k ∸ (k ∸ j)         ≡⟨ sym (∸suc-comm k (k ∸ j) (m≤n⇒n∸m≤n j≤k)) ⟩
  suc (k ∸ (k ∸ j))       ≡⟨ sym (cong suc (∸cancel j k j≤k)) ⟩
  suc j ∎
  )

∸-≤-suc : ∀ {j k : ℕ} → j ≤ k → j ≤ suc k
∸-≤-suc z≤n       = z≤n
∸-≤-suc (s≤s j≤k) = s≤s (∸-≤-suc j≤k)
```


Computing p - q
```agda
minus : (p q : ℕ) (q≤p : q ≤ p) → ℕ
minus p zero z≤n = p
minus (suc p) (suc q) (s≤s q≤p) = minus p q q≤p

minus′ : {p q : ℕ} (q≤p : q ≤ p) → ℕ
minus′ {p} z≤n = p
minus′     (s≤s q≤p) = minus′ q≤p

```

Unfortunately, it is painful to use, since we have to explicitly provide
the proof that `n ≤ m`:

```agda
_ : minus 5 3 (s≤s (s≤s (s≤s z≤n))) ≡ 2
_ = refl
```

But we can mine decidability:

```agda
_-_ : (m n : ℕ) {n≤m : T ⌊ n ≤? m ⌋} → ℕ
_-_ m n {n≤m} = minus m n (toWitness n≤m)
```
