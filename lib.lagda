\begin{code}
module lib where

open import Data.List hiding (_─_ ; any)
open import Data.List.Relation.Unary.Any using (here ; there ; any ; _∷=_ ) renaming (_─_ to _⑊_ )
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_ ; setoid)
import Relation.Binary
open import Data.Vec.Base as Vec using (Vec; []; _∷_)
open import Data.Fin as Fin using (Fin)
open import Relation.Nullary
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Setoid.Properties using (∈-∷=⁺-updated)

-- ⌊ a ⌋ : Maybe-PreImage f b  means that b = f a
data Maybe-PreImage {i j}{A : Set i}{B : Set j}(f : A → B) : B → Set i where
   ⌊_⌋ : ∀ a → Maybe-PreImage f (f a)
   ⊥ : ∀ {b} → Maybe-PreImage f b

pattern Ο {l} = here {xs = l} ≡.refl
pattern 1+ {x}{l} a = there {x}{l} a

module _ {i}{A : Set i} where
  _[_∶_] : ∀ (Γ : List A) {m} → m ∈ Γ → A → List A
  ℓ [ M ∶ m ] = M ∷= m

  _∶_ : ∀ {Γ : List A} {m} → (M : m ∈ Γ) → (a : A) → a ∈ (Γ [ M ∶ a ])
  M ∶ m = ∈-∷=⁺-updated (setoid A) M

  data _Maybe-⑊_ {ℓ : List A}{a}(a∈ : a ∈ ℓ) : ∀ {a'} → a' ∈ ℓ → Set i where
    ⊥ : a∈ Maybe-⑊ a∈
    ⌊_⌋ : ∀ {a'}{a'∈ : a' ∈ ℓ} → a ∈ (ℓ ⑊ a'∈) → a∈ Maybe-⑊ a'∈

  _⑊?_ : ∀ {l : List A}{a}(a∈ : a ∈ l){a'} → (a'∈ : a' ∈ l) → a∈ Maybe-⑊ a'∈
  Ο ⑊? Ο = ⊥
  Ο ⑊? 1+ a'∈ = ⌊ Ο ⌋
  1+ a∈ ⑊? Ο = ⌊ a∈ ⌋
  1+ a∈ ⑊? 1+ a'∈ with a∈ ⑊? a'∈
  ... | ⌊ a∈ ⌋ = ⌊ 1+ a∈ ⌋
  ... | ⊥ = ⊥

  module _ (_≟_ : Relation.Binary.Decidable (_≡_ {A = A})) where

    open import Data.Vec.Membership.DecPropositional _≟_
    open import Data.Vec.Relation.Unary.Any using (index)
    open import Data.Vec.Relation.Unary.Any.Properties using (lookup-index)
    nth⁻¹ : ∀ a {n} (l : Vec A n) → Maybe-PreImage (Vec.lookup l) a
    nth⁻¹ a {n} l with a ∈? l
    ... | no _ = ⊥
    ... | yes a∈ rewrite lookup-index a∈ = ⌊ index a∈ ⌋

\end{code}

