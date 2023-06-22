\begin{code}
{-# OPTIONS --type-in-type  #-}
module lib where

open import Agda.Builtin.Unit
open import Data.Sum.Base using () renaming (_⊎_ to _∨_ ; inj₁ to left ; inj₂ to right)
open import Data.Maybe.Base hiding (map) renaming (nothing to ⊥ ; just to ⌊_⌋)
open import Data.List hiding (map)
open import Data.Product using (_,_; Σ; _×_)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
open import Relation.Binary using (Rel; IsEquivalence; Setoid)
open import Data.Nat using (ℕ)
open import Data.Vec.Base as Vec using (Vec; []; _∷_)
open import Data.Fin as Fin using (Fin)
open import Relation.Nullary
open import Agda.Builtin.Bool renaming (Bool to 𝔹)



data PreImage {A B : Set}(f : A → B) : B → Set where
   Pre : ∀ a → PreImage f (f a)

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

  nth⁻¹ : (a : A) {n : ℕ}(l : Vec A n) → Maybe (PreImage (Vec.lookup l) a)
  nth⁻¹ a [] = ⊥
  nth⁻¹ a (x ∷ l) with a ≟ x
  ... | yes ≡.refl = ⌊ Pre Fin.zero ⌋
  ... | no _ = do
       Pre x ← nth⁻¹ a l
       ⌊ Pre (Fin.suc x) ⌋



module _ {A} where

  data _⑊∨=_ {ℓ : List A}{a}(a∈ : a ∈ ℓ) : ∀ {a'} → a' ∈ ℓ → Set where
    ⊥ : a∈ ⑊∨= a∈
    ⌊_⌋ : ∀ {a'}{a'∈ : a' ∈ ℓ} → a ∈ (ℓ ⑊ a'∈) → a∈ ⑊∨= a'∈ 

  _⑊?_ : ∀ {l : List A}{a}(a∈ : a ∈ l){a'} → (a'∈ : a' ∈ l) → a∈ ⑊∨= a'∈
  Ο ⑊? Ο = ⊥
  Ο ⑊? 1+ a'∈ = ⌊ Ο ⌋
  1+ a∈ ⑊? Ο = ⌊ a∈ ⌋
  1+ a∈ ⑊? 1+ a'∈ with a∈ ⑊? a'∈
  ... | ⌊ a∈ ⌋ = ⌊ 1+ a∈ ⌋
  ... | ⊥ = ⊥



module VecList where

  -- VecList B [l₀ ; .. ; lₙ] ≃ B l₀ × .. × B lₙ
  VecList : ∀ {A : Set}(B : A → Set)(l : List A)  → Set
  VecList B [] = ⊤
  VecList B (x ∷ l) = B x × VecList B l


  map : ∀ {A : Set}{B B' : A → Set}{l : List A} → (∀ a → B a → B' a) → VecList B l → VecList B' l
  map {l = []} f xs = tt
  map {l = a ∷ l} f (x , xs) = f a x  , map f xs


  nth : ∀ {A : Set}{B : A → Set}{l : List A}{a} → a ∈ l → VecList B l →  B a
  nth Ο (t , _) = t
  nth (1+ a∈) (_ , ts) = nth a∈ ts



\end{code}
