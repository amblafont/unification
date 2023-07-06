\begin{code}
{-# OPTIONS --no-termination-check #-}
module main where

open import Relation.Nullary using (Dec ; yes ; no)
open import Data.List as List hiding (map ; [_])
open import Data.List.Relation.Binary.Pointwise using (Pointwise ; [] ; _∷_)
open import Data.Product using (_,_; Σ; _×_ )
open import Data.Maybe.Base using (Maybe) renaming (nothing to ⊥ ; just to ⌊_⌋)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
open import Agda.Primitive

open import lib

\end{code}
%<*signature-core>
\begin{code}
record Signature i j k : Set (lsuc (i ⊔ j ⊔ k)) where
  field
    A : Set i
    _⇒_ : A → A → Set j
    id  : ∀ {a} → (a ⇒ a)
    _∘_ : ∀ {a b c} → (b ⇒ c) → (a ⇒ b) → (a ⇒ c)
    O : A → Set k
    α : ∀ {a} → O a → List A
\end{code}
%</signature-core>
\begin{code}
  -- [a₁,⋯, aₙ] ⟹ [b₁,⋯, bₘ] is isomorphic to a₁⇒b₁ × ⋯ × aₙ⇒bₙ if n=m
  -- Otherwise, it is isomorphic to the empty type.
\end{code}
%<*renaming-vectors>
\begin{code}
  _⟹_ : List A → List A → Set (i ⊔ j)
  as ⟹ bs = Pointwise _⇒_ as bs
\end{code}
%</renaming-vectors>
\begin{code}
  field
\end{code}
%<*signature-functoriality>
\begin{code}
    -- Functoriality components
    _｛_｝  : ∀ {a b} → O a → (a ⇒ b) → O b
    _^_ : ∀ {a b}(x : a ⇒ b)(o : O a) → α o ⟹ α (o ｛ x  ｝ )
\end{code}
%</signature-functoriality>

%<*friendlysignature>
\begin{code}
record isFriendly {i j k}(S : Signature i j k) : Set (i ⊔ j ⊔ k) where
   open Signature S
   field
     equaliser : ∀ {a} m → (x y : m ⇒ a) → Σ A (λ p → p ⇒ m)
     pullback : ∀ m {m' a} → (x : m ⇒ a) → (y : m' ⇒ a) → Σ A (λ p → p ⇒ m × p ⇒ m')
     _≟_ : ∀ {a}(o o' : O a) → Dec (o ≡ o')
     _｛_｝⁻¹ : ∀ {a}(o : O a) → ∀ {b}(x : b ⇒ a) → Maybe-PreImage (_｛ x ｝) o
\end{code}
%</friendlysignature>
\begin{code}
module Tm {i j k}(S : Signature i j k) where
   open Signature S
   MetaContext : Set i
   MetaContext· : Set i
\end{code}
%<*metacontext>
\begin{code}
   MetaContext· = List A
   MetaContext = Maybe MetaContext·
\end{code}
%</metacontext>
\begin{code}
   Tm· : MetaContext· → A → Set (i ⊔ j ⊔ k)
\end{code}
%<*syntax-decl>
\begin{code}
   data Tm  : MetaContext → A → Set (i ⊔ j ⊔ k)
   Tm· Γ a = Tm ⌊ Γ ⌋ a
\end{code}
%</syntax-decl>
\begin{code}
   import Common as C
   module Common = C {k = k} A _⇒_ id Tm
   open Common.SubstitutionDef public
\end{code}
%<*syntax-def>
\begin{code}
   data Tm where
     Rigid· : ∀ {Γ a}(o : O a) → (α o ·⟶· Γ)
          → Tm· Γ a
     _﹙_﹚ : ∀ {Γ a m} → m ∈ Γ → m ⇒ a
          → Tm· Γ a
     ! : ∀ {a} → Tm ⊥ a
\end{code}
%</syntax-def>
\begin{code}
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

   open Common.wkₛ wkₜ public

   wkₜ (Rigid· o ts) = Rigid· o (wkₛ ts)
   wkₜ (M ﹙ x ﹚) = 1+ M ﹙ x ﹚


{- ----------------------

Substitution

-------------------------- -}
   open Common.!ₛ ! public

\end{code}
%<*gen-substitution-proto>
\begin{code}
   _[_]t : ∀ {Γ a} → Tm Γ a → ∀ {Δ} → (Γ ⟶ Δ) → Tm Δ a
\end{code}
%</gen-substitution-proto>
\begin{code}

   open Common.-[-]s _[_]t public

\end{code}
%<*gen-substitution-def>
\begin{code}
   Rigid· o δ [ σ ]t = Rigid o (δ [ σ ]s)
   M ﹙ x ﹚ [ σ ]t =  nth σ M ❴ x ❵
   ! [ 1⊥ ]t = !
\end{code}
%</gen-substitution-def>
\begin{code}


   open Common.1ₛ wkₜ _﹙_﹚ public
   open Common.Substitution wkₜ _﹙_﹚ public



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

   open Common.occur-cases public

   occur-check : ∀ {Γ m n} → (M : m ∈ Γ) → Tm· Γ n → occur-cases M n
   occur-check M (M' ﹙ x ﹚) with M' ⑊? M
   ... | ⊥ = Same-MVar x
   ... | ⌊ M' ⌋ = No-Cycle (M' ﹙ x ﹚)
   occur-check M t with t ⑊?ₜ M
   ... | ⊥ = Cycle
   ... | ⌊ t' ⌋ = No-Cycle t'

module Unification {i j k}(S : Signature i j k) (F : isFriendly S) where
  open Signature S
  open Tm S
  open isFriendly F

{- ----------------------

Pruning

-------------------------- -}
  open Common.PruneUnifyTypes
  pattern _∶_﹙_﹚ M m x = _﹙_﹚ {m = m} M x
  \end{code}
  %<*prune-proto>
  \begin{code}
  record _∪_⟶? (Γ : MetaContext·)(Γ' : MetaContext) : Set (i ⊔ j ⊔ k) where
    constructor _◄_
    field
      Δ : MetaContext
      δ,σ : (Γ ·⟶ Δ) × (Γ' ⟶ Δ)


  prune : ∀ {Γ a m} → Tm Γ a → m ⇒ a → [ m ]∪ Γ ⟶?
  prune-σ : ∀ {Γ Γ' Γ''} → (Γ' ·⟶ Γ) → (Γ'' ⟹ Γ') → Γ'' ∪ Γ ⟶?
  \end{code}
  %</prune-proto>
  %<*prune-subst>
  \begin{code}
  prune-σ {Γ} [] [] = Γ ◄ ([] , 1ₛ)
  prune-σ (t , δ) (x₀ ∷ xs) = 
    let Δ₁ ◄ t' , σ₁ = prune t x₀
        Δ₂ ◄ δ' , σ₂ = prune-σ (δ [  σ₁  ]s) xs
    in  Δ₂ ◄  (t' [ σ₂ ]t , δ') , (σ₁ [ σ₂ ]s) 
  \end{code}
  %</prune-subst>
  %<*prune-rigid>
  \begin{code}
  prune (Rigid· o δ) x with o ｛ x ｝⁻¹
  ... | ⊥ = ⊥ ◄  ! ,  !ₛ 
  ... | ⌊ o' ⌋ =
    let Δ ◄ δ' , σ  =  prune-σ δ  (x ^ o')
    in  Δ ◄ Rigid o'  δ' ,  σ
  \end{code}
  %</prune-rigid>
  %<*prune-flex>
  \begin{code}
  prune {⌊ Γ ⌋} (M ∶ m ﹙ x ﹚) y =
    let p , r , l = pullback m x y in
    Γ [ M ∶ p ] ·◄  (M ∶ p) ﹙ l ﹚ , M ↦-﹙ r ﹚
  \end{code}
  %</prune-flex>
  \begin{code}
  prune ! y = ⊥ ◄ ! ,  !ₛ 


{- ----------------------

Unification

-------------------------- -}


  unify-flex-* : ∀ {Γ m a} → m ∈ Γ → m ⇒ a → Tm· Γ a → Γ ·⟶?
  \end{code}
%<*unify-flex-def>
  \begin{code}
  unify-flex-* {Γ} {m} M x t
                  with occur-check M t
  ... | Same-MVar y =
    let p , z = equaliser m x y
    in  Γ [ M ∶ p ] ·◄ M ↦-﹙ z ﹚
  ... | Cycle = ⊥ ◄ !ₛ
  ... | No-Cycle t' = 
    let Δ ◄ u , σ = prune t' x
    in  Δ ◄ M ↦ u , σ
  \end{code}
%</unify-flex-def>
  %<*unifyprototype>
  \begin{code}
  unify : ∀ {Γ a} → Tm Γ a → Tm Γ a → Γ ⟶?
  unify-σ : ∀ {Γ Γ'} → (Γ' ⟶ Γ) → (Γ' ⟶ Γ) → (Γ ⟶?)
  \end{code}
  %</unifyprototype>
  %<*unify-subst>
  \begin{code}
  unify-σ {Γ} [] [] = Γ ◄ 1ₛ
  unify-σ (t₁ , δ₁) (t₂ , δ₂) =
    let Δ ◄ σ = unify t₁ t₂
        Δ' ◄ σ' = unify-σ (δ₁ [ σ ]s) (δ₂ [ σ ]s)
    in  Δ' ◄ σ [ σ' ]s
  unify-σ 1⊥ 1⊥ = ⊥ ◄ !ₛ
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
