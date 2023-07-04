\begin{code}
-- here, the terminal substitution is not primitive
-- different notations than ⌊ . ⌋
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
open import Data.Maybe.Base hiding (map ; _>>=_) renaming (nothing to ⊥ ; just to ⌊_⌋)

open import Relation.Binary using (Rel; IsEquivalence; Setoid)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

open import lib
open VecList using (VecList)



\end{code}
%<*signature-core>
\begin{code}
record Signature : Set where
  field
    A : Set
    _⇒_ : A → A → Set
    id  : ∀ {a} → (a ⇒ a)
    _∘_ : ∀ {a b c} → (b ⇒ c) → (a ⇒ b) → (a ⇒ c)
    O : A → Set
    α : ∀ {a} → O a → List A
\end{code}
%</signature-core>
\begin{code}
  -- [a₁,⋯, aₙ] ⟹ [b₁,⋯, bₘ] is isomorphic to a₁⇒b₁ × ⋯ × aₙ⇒bₙ if n=m
  -- Otherwise, it is isomorphic to the empty type.
\end{code}
%<*renaming-vectors>
\begin{code}
  _⟹_ : List A → List A → Set
  as ⟹ bs = Pointwise _⇒_ as bs
\end{code}
%</renaming-vectors>
\begin{code}
  field
\end{code}
%<*signature-functoriality>
\begin{code}
    -- Functoriality components
    _｛_｝  : ∀ {a} → O a → ∀ {b} (x : a ⇒ b) → O b
    _^_ : ∀ {a b}(x : a ⇒ b)(o : O a) → α o ⟹ α (o ｛ x  ｝ )
\end{code}
%</signature-functoriality>

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
   MetaContext· : Set
   infix 3 _·⟶_
   infix 3 _·⟶·_
\end{code}
%<*syntax>
\begin{code}
   MetaContext· = List A
   MetaContext = Maybe MetaContext·

   data Tm  : MetaContext → A → Set
   _·⟶_ : MetaContext· → MetaContext → Set

   _·⟶·_ = λ Γ Δ → Γ ·⟶ ⌊ Δ ⌋
   Tm· = λ Γ a → Tm ⌊ Γ ⌋ a

   data Tm where
     Rigid· : ∀ {Γ a}(o : O a) → (α o ·⟶· Γ) → Tm· Γ a
     _﹙_﹚ : ∀ {Γ a m} → m ∈ Γ → m ⇒ a → Tm· Γ a
     ! : ∀ {a} → Tm ⊥ a

   Γ ·⟶ Δ = VecList (Tm Δ) Γ
\end{code}
%</syntax>
\begin{code}
   open import Common A _⇒_ id Tm _﹙_﹚ ! public

   Rigid : ∀ {Γ a}(o : O a) → ( α o ·⟶ Γ ) → Tm Γ a
   Rigid {⊥} o δ = !
   Rigid {⌊ Γ ⌋} o δ = Rigid· o δ

{- ----------------------

Renaming

-------------------------- -}
   _❴_❵ : ∀ {Γ a b} → Tm Γ a → a ⇒ b → Tm Γ b
   _❴_❵s : ∀ {Γ Γ' Δ} → Γ ·⟶ Δ
         → Γ ⟹ Γ' → Γ' ·⟶ Δ

   Rigid· o ts ❴ x ❵ = Rigid· (o ｛ x ｝) (ts ❴ x ^ o ❵s)
   M ﹙ y ﹚ ❴ x ❵ = M ﹙ x ∘ y ﹚
   ! ❴ f ❵ = !

   [] ❴ [] ❵s = []
   (t , ts) ❴ f ∷ fs ❵s = t ❴ f ❵ , ts ❴ fs ❵s

{- ----------------------

Weakening

-------------------------- -}
   wkₜ : ∀ {Γ a m} → Tm· Γ a → Tm· (m ∷ Γ) a

   wkₛ : ∀{Γ Δ m}  → (Γ ·⟶· Δ) → (Γ ·⟶· m ∷ Δ)
   wkₛ σ = VecList.map (λ _ → wkₜ) σ


   wkₜ (Rigid· o ts) = Rigid· o (wkₛ ts)
   wkₜ (M ﹙ x ﹚) = 1+ M ﹙ x ﹚




   import Common as C
   module Common = C A _⇒_ id Tm _﹙_﹚ !
   -- import Common A _⇒_ id Tm _﹙_﹚ ! as Common public
{- ----------------------

Substitution

-------------------------- -}
   open Common.Substitution public
\end{code}
%<*gen-subst>
\begin{code}
   _[_]t : ∀ {Γ a} → Tm Γ a → ∀ {Δ} → (Γ ⟶ Δ) → Tm Δ a
   _·[_]s : ∀ {Γ₁ Γ₂ Γ₃} → (Γ₁ ·⟶ Γ₂) → (Γ₂ ⟶ Γ₃) → (Γ₁ ·⟶ Γ₃)

   Rigid· o δ [ σ ]t = Rigid o (δ ·[ σ ]s)  
   M ﹙ x ﹚ [ ⌊ σ ⌋ ]t = VecList.nth M σ ❴ x ❵
   ! [ 1⊥ ]t = !


   δ ·[ σ ]s = VecList.map (λ _ t → t [ σ ]t) δ
\end{code}
%</gen-subst>
\begin{code}
   open Common.MoreSubstitution wkₛ _·[_]s public


{- ----------------------

Occur check

-------------------------- -}

   infixl 20 _⑊?ₜ_
\end{code}
% <*occur-check>
\begin{code}
   _⑊?ₜ_ : ∀ {Γ m a} → Tm· Γ a → (M : m ∈ Γ) → Maybe (Tm· (Γ ⑊ M) a)
   _⑊?ₛ_ : ∀ {Γ m Δ} → Δ ·⟶· Γ  → (M : m ∈ Γ) → Maybe (Δ ·⟶· Γ ⑊ M )

   Rigid· o ts ⑊?ₜ M = do
       ts' ← ts ⑊?ₛ M
       ⌊ Rigid· o ts' ⌋
       where open Data.Maybe.Base using (_>>=_)
   M' ﹙ y ﹚ ⑊?ₜ M with M' ⑊? M
   ... | ⊥ = ⊥
   ... | ⌊ M' ⌋ = ⌊ M' ﹙ y ﹚ ⌋

   _⑊?ₛ_ (t , ts) M = do
       ts' ← ts ⑊?ₛ M
       t' ← t ⑊?ₜ M
       ⌊ t' , ts' ⌋
       where open Data.Maybe.Base using (_>>=_)
   _⑊?ₛ_ [] M = ⌊ [] ⌋

   open Common.OccurCheckType public

   occur-check : ∀ {Γ m n} → (M : m ∈ Γ) → Tm· Γ n → occur-cases M n
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
  open IdentityDoNotation
  open Common.PruneUnifyTypes
  \end{code}
  %<*prune-proto>
  \begin{code}
  data _∪_⟶? (Γ : MetaContext·)(Γ' : MetaContext) : Set where
    _◄_ : ∀ Δ → (Γ ·⟶ Δ) × (Γ' ⟶ Δ) → Γ ∪ Γ' ⟶?



  prune : ∀ {Γ a m} → Tm Γ a → m ⇒ a → [ m ]∪ Γ ⟶?
  prune-σ : ∀ {Γ Γₐ Γₘ} → (Γₐ ·⟶ Γ) → (Γₘ ⟹ Γₐ) → Γₘ ∪ Γ ⟶?
  \end{code}
  %</prune-proto>
  %<*prune-subst>
  \begin{code}
  prune-σ {Γ} [] [] = Γ ◄ ([] , 1ₛ)
  prune-σ (t , δ) (x₀ ∷ xs) = do
        Δ₁ ◄ t' , σ₁ ← prune t x₀
        Δ₂ ◄ δ' , σ₂ ← prune-σ (δ ·[ σ₁ ]s) xs
        Δ₂ ◄  (t' [ σ₂ ]t , δ') , (σ₁ [ σ₂ ]s) 
  \end{code}
  %</prune-subst>
  %<*prune-rigid>
  \begin{code}
  prune (Rigid· o δ) x with o ｛ x ｝⁻¹
  ... | ⊥ = ⊥ ◄  ! , !ₛ
  ... | ⌊ o' ⌋ = do
       Δ ◄ δ' , σ  ←  prune-σ δ  (x ^ o')
       Δ ◄ Rigid o'  δ' , σ
  \end{code}
  %</prune-rigid>
  %<*prune-flex>
  \begin{code}
  prune {⌊ Γ ⌋} (M ﹙ x ﹚) y =
     let p , r , l = pullback x y in
     Γ [ M ∶ p ] ·◄ (M ∶ p) ﹙ l ﹚ ,· M ↦-﹙ r ﹚
  \end{code}
  %</prune-flex>
  \begin{code}
  prune ! y = ⊥ ◄ ! , !ₛ



{- ----------------------

Unification

-------------------------- -}


  unify-flex-* : ∀ {Γ m a} → m ∈ Γ → m ⇒ a → Tm· Γ a → Γ ·⟶?
  \end{code}
%<*unify-flex-def>
  \begin{code}
  unify-flex-* {Γ} M x t with occur-check M t
  ... | Same-MVar y =
     let p , z = equaliser x y in
     Γ [ M ∶ p ] ·◄· M ↦-﹙ z ﹚
  ... | Cycle = ⊥ ◄ !ₛ
  ... | No-Cycle t' = do
            Δ ◄ u ,· σ ← prune t' x
            Δ ◄· M ↦ u , σ
  \end{code}
%</unify-flex-def>
  %<*unifyprototype>
  \begin{code}
  unify : ∀ {Γ a} → Tm Γ a → Tm Γ a → Γ ⟶?
  unify-σ : ∀ {Γ Γ'} → (Γ' ·⟶ Γ) → (Γ' ·⟶ Γ) → (Γ ⟶?)
  \end{code}
  %</unifyprototype>
  %<*unify-subst>
  \begin{code}
  unify-σ {Γ} [] [] = Γ ◄ 1ₛ
  unify-σ (t₁ , δ₁) (t₂ , δ₂) = do
      Δ ◄ σ ← unify t₁ t₂
      Δ' ◄ σ' ← unify-σ (δ₁ ·[ σ ]s) (δ₂ ·[ σ ]s)
      Δ' ◄ σ [ σ' ]s
  \end{code}
  %</unify-subst>
  \begin{code}
  unify t (M ﹙ x ﹚) = unify-flex-* M x t
  unify (M ﹙ x ﹚) t = unify-flex-* M x t
  \end{code}
  %<*unify-rigid>
  \begin{code}
  unify (Rigid· o δ) (Rigid· o' δ') with o ≟ o'
  ... | no _ = ⊥ ◄ !ₛ
  ... | yes ≡.refl = unify-σ δ δ'
  \end{code}
  %</unify-rigid>
  %<*unify-fail>
  \begin{code}
  unify ! ! = ⊥ ◄ !ₛ
  \end{code}
  %</unify-fail>
  \begin{code}
