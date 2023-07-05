\begin{code}
module lib where

open import Data.List
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
import Relation.Binary
open import Data.Vec.Base as Vec using (Vec; []; _∷_)
open import Data.Fin as Fin using (Fin)
open import Relation.Nullary


-- ⌊ a ⌋ : Maybe-PreImage f b  means that b = f a
data Maybe-PreImage {A B : Set}(f : A → B) : B → Set where
   ⌊_⌋ : ∀ a → Maybe-PreImage f (f a)
   ⊥ : ∀ {b} → Maybe-PreImage f b

\end{code}
%<*membership>
\begin{code}
data _∈_ {A : Set} (a : A) : List A → Set where
  Ο  : ∀ {ℓ} → a ∈ (a ∷ ℓ)
  1+ : ∀ {x ℓ}  → a ∈ ℓ → a ∈ (x ∷ ℓ)
\end{code}
%</membership>
\begin{code}

_[_∶_] : ∀ {A}(Γ : List A) {m} → m ∈ Γ → A → List A
.(_ ∷ ℓ) [ Ο {ℓ} ∶ b ] = b ∷ ℓ
.(_ ∷ _) [ 1+ {x}{ℓ} a∈ ∶ b ] = x ∷ ℓ [ a∈ ∶ b ]

_∶_ : ∀ {A}{Γ : List A} {m} → (M : m ∈ Γ) → (a : A) → a ∈ (Γ [ M ∶ a ])
Ο ∶ a = Ο
1+ M ∶ a = 1+ (M ∶ a)

infixl 20 _⑊_

_⑊_ : ∀ {A}(ℓ : List A){a}(a∈ : a ∈ ℓ) → List A
.(_ ∷ _) ⑊ Ο {ℓ} = ℓ
.(_ ∷ _) ⑊ (1+ {x}{ℓ} a∈) = x ∷ ℓ ⑊ a∈



module _ {A : Set}(_≟_ : Relation.Binary.Decidable (_≡_ {A = A})) where

  nth⁻¹ : ∀ a {n} (l : Vec A n) → Maybe-PreImage (Vec.lookup l) a
  nth⁻¹ a [] = ⊥
  nth⁻¹ a (x ∷ l) with a ≟ x
  ... | yes ≡.refl = ⌊ Fin.zero ⌋
  ... | no _ with nth⁻¹ a l
  ...    | ⊥ = ⊥
  ...    | ⌊ x ⌋ = ⌊ Fin.suc x ⌋



module _ {A} where

  data _Maybe-⑊_ {ℓ : List A}{a}(a∈ : a ∈ ℓ) : ∀ {a'} → a' ∈ ℓ → Set where
    ⊥ : a∈ Maybe-⑊ a∈
    ⌊_⌋ : ∀ {a'}{a'∈ : a' ∈ ℓ} → a ∈ (ℓ ⑊ a'∈) → a∈ Maybe-⑊ a'∈

  _⑊?_ : ∀ {l : List A}{a}(a∈ : a ∈ l){a'} → (a'∈ : a' ∈ l) → a∈ Maybe-⑊ a'∈
  Ο ⑊? Ο = ⊥
  Ο ⑊? 1+ a'∈ = ⌊ Ο ⌋
  1+ a∈ ⑊? Ο = ⌊ a∈ ⌋
  1+ a∈ ⑊? 1+ a'∈ with a∈ ⑊? a'∈
  ... | ⌊ a∈ ⌋ = ⌊ 1+ a∈ ⌋
  ... | ⊥ = ⊥

\end{code}
