\begin{code}
{-# OPTIONS --type-in-type --no-termination-check #-}
module lib where

open import Agda.Builtin.Unit
open import Data.Maybe.Base hiding (map)
open import Data.List hiding (map)
open import Data.Product using (_,_; Σ; _×_)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
open import Relation.Binary using (Rel; IsEquivalence; Setoid)
open import Data.Nat using (ℕ)
open import Data.Vec.Base as Vec using (Vec; []; _∷_)
open import Data.Fin as Fin using (Fin)
open import Relation.Nullary
open import Agda.Builtin.Bool renaming (Bool to 𝔹)

data PreImage {A : Set}{B : Set}(f : A → B) : B → Set where
   Pre : ∀ a → PreImage f (f a)

\end{code}
%<*membership>
\begin{code}
data _∈_ {A : Set} (a : A) : List A → Set where
  here  : ∀ xs   → a ∈ (a ∷ xs)
  there : ∀ {x xs}  → a ∈ xs → a ∈ (x ∷ xs)
\end{code}
%</membership>
\begin{code}

_without_ : ∀ {A}(l : List A){a}(a∈ : a ∈ l) → List A
.(_ ∷ _) without (here l) = l
.(_ ∷ _) without (there {x = x}{xs = l} a∈) = x ∷ l without a∈

module _ {A : Set}(_≟_ : Relation.Binary.Decidable (_≡_ {A = A})) where

  find-PreImage-Vec : (a : A) {n : ℕ}(l : Vec A n) → Maybe (PreImage (Vec.lookup l) a)
  find-PreImage-Vec a [] = nothing
  find-PreImage-Vec a (x ∷ l) with a ≟ x
  ... | yes ≡.refl = just (Pre Fin.zero)
  ... | false because ofⁿ ¬p = do
       Pre x ← find-PreImage-Vec a l
       just (Pre (Fin.suc x))

  find-∈ : (a : A) {n : ℕ}(l : Vec A n) → Maybe (Fin n)
  find-∈ a l = do
      Pre x ← find-PreImage-Vec a l
      just x

restricts∈ : ∀ {A}{l : List A} {a}(t : a ∈ l){a'}(t' : a' ∈ l) → Maybe (a' ∈ (l without t))
restricts∈ (here _) (here _) = nothing
restricts∈ (here _) (there t') = just t'
restricts∈ (there _) (here _) = just (here _)
restricts∈ (there t) (there t') = do
    i ← restricts∈ t t'
    just (there i)


module VecList where

  -- VecList.t B [l₀ ; .. ; lₙ] ≃ B l₀ × .. × B lₙ
  t : ∀ {A : Set}(B : A → Set)(l : List A)  → Set
  t B [] = ⊤
  t B (x ∷ l) = B x × t B l


  map : ∀ {A : Set}{B B' : A → Set}{l : List A} → (∀ a → B a → B' a) → t B l → t B' l
  map {l = []} f xs = tt
  map {l = a ∷ l} f (x , xs) = f a x  , map f xs


  nth : ∀ {A : Set}{B : A → Set}{l : List A}{a} → a ∈ l → t B l →  B a
  nth (here xs) (t , _) = t
  nth (there a∈) (t , ts) = nth a∈ ts


