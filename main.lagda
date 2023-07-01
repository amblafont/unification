\begin{code}
{-# OPTIONS --type-in-type --no-termination-check #-}
module main where

open import Agda.Builtin.Unit
open import Agda.Builtin.Bool renaming (Bool to 𝔹)
open import Data.Nat as ℕ using (ℕ; _+_)
open import Data.Fin as Fin using (Fin)
open import Data.Sum.Base using () renaming (_⊎_ to _∨_ ; inj₁ to left ; inj₂ to right)
open import Relation.Nullary
open import Data.List as List hiding (map ; [_])
open import Data.List.Relation.Binary.Pointwise using (Pointwise ; [] ; _∷_)
open import Data.Vec.Base as Vec using (Vec; []; _∷_; toList)
open import Data.Product using (_,_; Σ; _×_ ; uncurry) -- renaming (Σ[_∈_]_ to Σ[_∶_]_)
open import Data.Maybe.Base hiding (map) renaming (nothing to ⊥ ; just to ⌊_⌋)

open import Relation.Binary using (Rel; IsEquivalence; Setoid)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

open import lib
open VecList using (VecList)



\end{code}
%<*signature>
\begin{code}
record Signature : Set where
  field
    A : Set
    _⇒_ : A → A → Set
    id  : ∀ {a} → (a ⇒ a)
    _∘_ : ∀ {a b c} → (b ⇒ c) → (a ⇒ b) → (a ⇒ c)
    O : A → Set
    α : ∀ {a} → O a → List A

  -- [a₁,⋯, aₙ] ⟹ [b₁,⋯, bₘ] is isomorphic to a₁⇒b₁ × ⋯ × aₙ⇒bₙ if n=m
  -- Otherwise, it is isomorphic to the empty type.
  _⟹_ : List A → List A → Set
  as ⟹ bs = Pointwise _⇒_ as bs

  field
    -- The last two fields account for functoriality
    _｛_｝  : ∀ {a} → O a → ∀ {b} (x : a ⇒ b) → O b
    _^_ : ∀ {a b}(x : a ⇒ b)(o : O a) → α o ⟹ α (o ｛ x  ｝ )
\end{code}
%</signature>

%<*friendlysignature>
\begin{code}
record isFriendly (S : Signature) : Set where
   open Signature S
   field
     equaliser : ∀ {a m} → (x y : m ⇒ a) → Σ A (λ p → p ⇒ m)
     pullback : ∀ {m m' a} → (x : m ⇒ a) → (y : m' ⇒ a) → Σ A (λ p → p ⇒ m × p ⇒ m')
     _≟_ : ∀ {a}(o o' : O a) → Dec (o ≡ o')
     _｛_｝⁻¹ : ∀ {a}(o : O a) → ∀ {b}(x : b ⇒ a) → Maybe-PreImage (_｛ x ｝) o
\end{code}
%</friendlysignature>

\begin{code}
module Tm (S : Signature) where
   open Signature S
   MetaContext : Set
   infix 3 _⟶_
   _⟶_ : MetaContext → MetaContext → Set
\end{code}
%<*syntax>
\begin{code}
   MetaContext = List A
   data Tm (Γ : MetaContext) (a : A) : Set where
     Rigid : ∀ (o : O a) → (α o ⟶ Γ) → Tm Γ a
     _﹙_﹚ : ∀ {m} → m ∈ Γ → m ⇒ a → Tm Γ a
\end{code}
%</syntax>
\begin{code}
   Γ ⟶ Δ = VecList (Tm Δ) Γ

{- ----------------------

Renaming

-------------------------- -}
   _❴_❵ : ∀ {Γ a b} → Tm Γ a → a ⇒ b → Tm Γ b
   _❴_❵s : ∀ {Γ Γ' Δ} → Γ ⟶ Δ
         → Γ ⟹ Γ' → Γ' ⟶ Δ

   Rigid o ts ❴ f ❵ = Rigid (o ｛ f ｝) (ts ❴ f ^ o ❵s)
   M ﹙ x ﹚ ❴ f ❵ = M ﹙ f ∘ x ﹚

   [] ❴ [] ❵s = []
   (t , ts) ❴ f ∷ fs ❵s = t ❴ f ❵ , ts ❴ fs ❵s

{- ----------------------

Weakening

-------------------------- -}
   wkₜ : ∀ {Γ a m} → Tm Γ a → Tm (m ∷ Γ) a

   wkₛ : ∀{Γ Δ m}  → (Γ ⟶ Δ) → (Γ ⟶ m ∷ Δ)
   wkₛ σ = VecList.map (λ _ → wkₜ) σ

   wkₜ (Rigid o ts) = Rigid o (wkₛ ts)
   wkₜ (M ﹙ x ﹚) = 1+ M ﹙ x ﹚


   open import Common A _⇒_ id Tm _﹙_﹚ wkₛ public

\end{code}
%<*gen-subst>
\begin{code}
   _[_]t : ∀ {Γ a} → Tm Γ a → ∀ {Δ} → (Γ ⟶ Δ) → Tm Δ a
   _[_]s : ∀ {Γ₁ Γ₂ Γ₃} → (Γ₁ ⟶ Γ₂) → (Γ₂ ⟶ Γ₃) → (Γ₁ ⟶ Γ₃)

   Rigid o δ [ σ ]t = Rigid o (δ [ σ ]s)
   M ﹙ x ﹚ [ σ ]t = VecList.nth M σ ❴ x ❵

   δ [ σ ]s = VecList.map (λ _ t → t [ σ ]t) δ
\end{code}
%</gen-subst>
\begin{code}


{- ----------------------

Occur check

-------------------------- -}

   infixl 20 _⑊?ₜ_
\end{code}
% <*occur-check>
\begin{code}
   _⑊?ₜ_ : ∀ {Γ m a} → Tm Γ a → (M : m ∈ Γ) → Maybe (Tm (Γ ⑊ M) a)
   _⑊?ₛ_ : ∀ {Γ m Δ} → Δ ⟶ Γ → (M : m ∈ Γ) → Maybe (Δ ⟶ (Γ ⑊ M))

   Rigid o ts ⑊?ₜ M = do
       ts' ← ts ⑊?ₛ M
       ⌊ Rigid o ts' ⌋
   M' ﹙ y ﹚ ⑊?ₜ M with M' ⑊? M
   ... | ⊥ = ⊥
   ... | ⌊ M' ⌋ = ⌊ M' ﹙ y ﹚ ⌋

   _⑊?ₛ_ (t , ts) M = do
       ts' ← ts ⑊?ₛ M
       t' ← t ⑊?ₜ M
       ⌊ t' , ts' ⌋
   _⑊?ₛ_ [] M = ⌊ [] ⌋

   occur-check : ∀ {Γ m n} → (M : m ∈ Γ) → Tm Γ n → occur-cases M n
   occur-check M (M' ﹙ x ﹚) with M' ⑊? M 
   ... | ⊥ = Same-MVar x
   ... | ⌊ M' ⌋ = No-Cycle (M' ﹙ x ﹚)
   occur-check M t with t ⑊?ₜ M
   ... | ⊥ = Cycle
   ... | ⌊ t' ⌋ = No-Cycle t'

\end{code}
% </occur-check>

\begin{code}

module Unification (S : Signature) (F : isFriendly S) where
  open Signature S
  open Tm S
  open isFriendly F

{- ----------------------

Pruning

-------------------------- -}
  \end{code}
  %<*prune-proto>
  \begin{code}
  data _∪_⟶? (Γ Γ' : MetaContext) : Set where
     _◄_,,_ : ∀ Δ → (Γ ⟶ Δ) → (Γ' ⟶ Δ) → Γ ∪ Γ' ⟶?
  prune : ∀ {Γ a m} → Tm Γ a → m ⇒ a → Maybe (m ∷ Γ ⟶?)
  prune-σ : ∀ {Γ Γₐ Γₘ} → (Γₐ ⟶ Γ) → (Γₘ ⟹ Γₐ) → Maybe (Γₘ ∪ Γ ⟶?)
  \end{code}
  %</prune-proto>
  %<*prune-subst>
  \begin{code}
  prune-σ {Γ} [] [] = ⌊ Γ ◄ [] ,, idₛ ⌋
  prune-σ (t , δ) (x₀ ∷ xs) = do
      Δ₁ ◄ t' , σ₁  ← prune t x₀
      Δ₂ ◄ δ' ,, σ₂ ← prune-σ (δ [ σ₁ ]s) xs
      ⌊ Δ₂ ◄ (t' [ σ₂ ]t , δ') ,, (σ₁ [ σ₂ ]s) ⌋
  \end{code}
  %</prune-subst>
  %<*prune-rigid>
  \begin{code}
  prune (Rigid o δ) x with o ｛ x ｝⁻¹
  ... | ⊥ = ⊥
  ... | ⌊ o' ⌋ = do
       Δ ◄ δ' ,, σ ← prune-σ δ (x ^ o')
       ⌊ Δ ◄ Rigid o' δ' , σ ⌋
  \end{code}
  %</prune-rigid>
  %<*prune-flex>
  \begin{code}
  prune {Γ} (M ﹙ x ﹚) y =
    let p , r , l = pullback x y in
    ⌊ Γ [ M ∶ p ] ◄ (M ∶ p) ﹙ l ﹚ , M ↦-﹙ r ﹚ ⌋
  \end{code}
  %</prune-flex>
  \begin{code}

{- ----------------------

Unification

-------------------------- -}
  unify-flex-* : ∀ {Γ m a} → m ∈ Γ → m ⇒ a → Tm Γ a → Maybe (Γ ⟶?)
  \end{code}
%<*unify-flex-def>
  \begin{code}
  unify-flex-* {Γ} M x t with occur-check M t
  ... | Same-MVar y =
     let p , z = equaliser x y in
     ⌊ Γ [ M ∶ p ] ◄ M ↦-﹙ z ﹚ ⌋
  ... | Cycle = ⊥
  ... | No-Cycle t' = do
        Δ ◄ u , σ ← prune t' x
        ⌊ Δ ◄ M ↦ u , σ ⌋
  \end{code}
%</unify-flex-def>
  %<*unifyprototype>
  \begin{code}
  unify : ∀ {Γ a} → Tm Γ a → Tm Γ a → Maybe (Γ ⟶?)
  unify-σ : ∀ {Γ Γ'} → (Γ' ⟶ Γ) → (Γ' ⟶ Γ) → Maybe (Γ ⟶?)
  \end{code}
  %</unifyprototype>
  %<*unify-subst>
  \begin{code}
  unify-σ {Γ} [] [] = ⌊ Γ ◄ idₛ ⌋
  unify-σ (t₁ , δ₁) (t₂ , δ₂) = do
      Δ  ◄ σ  ← unify t₁ t₂
      Δ' ◄ σ' ← unify-σ (δ₁ [ σ ]s) (δ₂ [ σ ]s)
      ⌊ Δ' ◄ σ [ σ' ]s ⌋
  \end{code}
  %</unify-subst>
  \begin{code}
  unify t (M ﹙ x ﹚) = unify-flex-* M x t
  unify (M ﹙ x ﹚) t = unify-flex-* M x t
  \end{code}
  %<*unify-rigid>
  \begin{code}
  unify (Rigid o δ) (Rigid o' δ') with o ≟ o'
  ... | no _ = ⊥
  ... | yes ≡.refl = unify-σ δ δ'
  \end{code}
  %</unify-rigid>
