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
     equalizers : ∀ {a m} → (x y : m ⇒ a) → Σ A (λ p → p ⇒ m)
     pullbacks : ∀ {m m' a} → (x : m ⇒ a) → (y : m' ⇒ a) → Σ A (λ p → p ⇒ m × p ⇒ m')
     _≟_ : ∀ {a}(o o' : O a) → Dec (o ≡ o')
     _｛_｝⁻¹ : ∀ {a}(o : O a) → ∀ {b}(f : b ⇒ a) → Maybe-PreImage (_｛ f ｝) o


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

\end{code}
% </occur-check>

\begin{code}

module Unification (S : Signature) (F : isFriendly S) where
  open Signature S
  open Tm S
  open isFriendly F

{- ----------------------

Unification of two metavariables

-------------------------- -}
\end{code}
%<*unify-flex-flex-proto>
\begin{code}
  unify-flex-flex : ∀ {Γ m m' a} → m  ∈ Γ → m  ⇒ a
                               → m' ∈ Γ → m' ⇒ a → Γ ⟶?
  unify-flex-flex {Γ} M x M' y with M' ⑊? M
\end{code}
%</unify-flex-flex-proto>
%<*unify-flex-flex-same>
\begin{code}
  ... | ⊥ =
   let p , z = equalizers x y in
   Γ [ M ∶ p ] ◄ M ↦-﹙ z ﹚
\end{code}
%</unify-flex-flex-same>
%<*unify-flex-flex-diff>
\begin{code}
  ... | ⌊ M' ⌋ =
   let p , l , r = pullbacks x y in
   Γ ⑊ M [ M' ∶ p ] ◄ M ↦ (M' ∶ p) ﹙ l ﹚
                     , M' ↦-﹙ r ﹚
\end{code}
%</unify-flex-flex-diff>

\begin{code}
{- ----------------------

Non cyclic unification

-------------------------- -}
  \end{code}
  %<*unify-no-cycle-proto>
  \begin{code}
  data _∪_⟶? (Γ Γ' : MetaContext) : Set where
     _◄_,,_ : ∀ Δ → (Γ ⟶ Δ) → (Γ' ⟶ Δ) → Γ ∪ Γ' ⟶?
  unify-no-cycle : ∀ {Γ a m} → Tm Γ a → m ⇒ a → Maybe (m ∷ Γ ⟶?)
  unify-σ-no-cycle : ∀ {Γ Γₐ Γₘ} → (Γₐ ⟶ Γ) → (Γₘ ⟹ Γₐ) → Maybe (Γₘ ∪ Γ ⟶?)
  \end{code}
  %</unify-no-cycle-proto>
  %<*unify-no-cycle-subst>
  \begin{code}
  unify-σ-no-cycle {Γ}[] [] = ⌊ Γ ◄ [] ,, idₛ ⌋
  unify-σ-no-cycle (t , δ) (x₀ ∷ xs) = do
      Δ₁ ◄ t' , σ₁  ← unify-no-cycle t x₀
      Δ₂ ◄ δ' ,, σ₂ ← unify-σ-no-cycle (δ [ σ₁ ]s) xs
      ⌊ Δ₂ ◄ (t' [ σ₂ ]t , δ') ,, (σ₁ [ σ₂ ]s) ⌋
  \end{code}
  %</unify-no-cycle-subst>
  %<*unify-no-cycle-rigid>
  \begin{code}
  unify-no-cycle (Rigid o δ) x with o ｛ x ｝⁻¹
  ... | ⊥ = ⊥
  ... | ⌊ o' ⌋ = do
       Δ ◄ δ' ,, σ ← unify-σ-no-cycle δ (x ^ o')
       ⌊ Δ ◄ Rigid o' δ' , σ ⌋
  \end{code}
  %</unify-no-cycle-rigid>
  \begin{code}
  unify-no-cycle (M ﹙ x ﹚) y =
      ⌊ unify-flex-flex (1+ M) x Ο y ⌋
  \end{code}
  \begin{code}

{- ----------------------

Unification

-------------------------- -}
  unify-flex-* : ∀ {Γ m a} → m ∈ Γ → m ⇒ a → Tm Γ a → Maybe (Γ ⟶?)
  unify-flex-* M x (N ﹙ y ﹚) = ⌊ unify-flex-flex M x N y ⌋
  unify-flex-* M x u = do
      u ← u ⑊?ₜ M
      Δ ◄ t , σ ← unify-no-cycle u x
      ⌊ Δ ◄ M ↦ t , σ ⌋
  \end{code}
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
  unify u (M ﹙ x ﹚) = unify-flex-* M x u
  unify (M ﹙ x ﹚) u = unify-flex-* M x u
  \end{code}
  %<*unify-rigid>
  \begin{code}
  unify (Rigid o δ) (Rigid o' δ') with o ≟ o'
  ... | no _ = ⊥
  ... | yes ≡.refl = unify-σ δ δ'
  \end{code}
  %</unify-rigid>
