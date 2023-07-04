\begin{code}
open import Data.List as List hiding (map ; [_])
open import lib
open VecList using (VecList)
open import Data.Maybe.Base hiding (map ; _>>=_) renaming (nothing to ⊥ ; just to ⌊_⌋)


module Common (A : Set) 
     (_⇒_ : A → A → Set)
     (id : ∀{a} → a ⇒ a)
     (Tm : Maybe (List A) → A → Set)
     (_﹙_﹚ : ∀ {Γ a m} → m ∈ Γ → m ⇒ a → Tm ⌊ Γ ⌋ a)
     (! : ∀ {a} → Tm ⊥ a)
  where

open import Agda.Builtin.Unit
open import Agda.Builtin.Bool renaming (Bool to 𝔹)
open import Data.Nat using (ℕ; _≟_ ; _+_)
open import Data.Fin as Fin using (Fin)
open import Data.Sum.Base using () renaming (_⊎_ to _∨_ ; inj₁ to left ; inj₂ to right)
open import Relation.Nullary
open import Data.Vec.Base as Vec using (Vec; []; _∷_)
open import Data.Product using (_,_; Σ; _×_)

open import Relation.Binary using (Rel; IsEquivalence; Setoid)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

private
  MetaContext· = List A
  MetaContext = Maybe MetaContext·

  Tm· = λ Γ a → Tm ⌊ Γ ⌋ a
  infix 3 _·⟶_
  infix 3 _·⟶·_
  _·⟶_ : MetaContext· → MetaContext → Set
  Γ ·⟶ Δ = VecList (Tm Δ) Γ

  _·⟶·_ = λ Γ Δ → Γ ·⟶ ⌊ Δ ⌋

module Substitution where
  infix 3 _⟶_

-- precedence below _∷_, which is 4
\end{code}
%<*substitution-def>
\begin{code}
  data _⟶_ : MetaContext → MetaContext → Set where
     ⌊_⌋ : ∀ {Γ Δ} → (Γ ·⟶  Δ) → (⌊ Γ ⌋ ⟶ Δ)
     1⊥ : ⊥ ⟶ ⊥
\end{code}
%</substitution-def>
\begin{code}
  !· : ∀ {Γ} →  Γ ·⟶ ⊥
  !· {Γ} = VecList.init (λ a → !) Γ

  !ₛ : ∀ {Γ} → Γ ⟶ ⊥
  !ₛ {⊥} = 1⊥
  !ₛ {⌊ Γ ⌋} = ⌊ !· ⌋

open Substitution

module MoreSubstitution
  (wkₛ : ∀{Γ Δ m}  → (Γ ·⟶· Δ) → (Γ ·⟶· m ∷ Δ))
  (_·[_]s : ∀ {Γ₁ Γ₂ Γ₃} → (Γ₁ ·⟶ Γ₂) → (Γ₂ ⟶ Γ₃) → (Γ₁ ·⟶ Γ₃))
 where
\end{code}
  %<*id-subst>
  \begin{code}
  1· : ∀ {Γ} → Γ ·⟶· Γ
  1· {[]} = []
  1· {m ∷ Γ} = Ο ﹙ id ﹚ , wkₛ 1·

  1ₛ : ∀ {Γ} → Γ ⟶ Γ
  1ₛ {⊥} = 1⊥
  1ₛ {⌊ Γ ⌋} = ⌊ 1· ⌋
  \end{code}
  %</id-subst>
  \begin{code}
  _[_]s : ∀ {Γ₁ Γ₂ Γ₃} → (Γ₁ ⟶ Γ₂) → (Γ₂ ⟶ Γ₃) → (Γ₁ ⟶ Γ₃)

  ⌊ δ ⌋ [ σ ]s =  ⌊ δ ·[ σ ]s ⌋
  1⊥ [ 1⊥ ]s = 1⊥
  \end{code}
  %<*extend-subst>
  \begin{code}
  _↦_,_ : ∀ {Γ Δ m} → (M : m ∈ Γ) → Tm Δ m
           → (Γ ⑊ M ·⟶ Δ) → (Γ ·⟶ Δ)
  Ο ↦ t , σ = t , σ
  1+ M ↦ t , (u , σ) = u , M ↦ t , σ
  \end{code}
  %</extend-subst>
  \begin{code}
  infix 21 _↦-﹙_﹚
  \end{code}
  %<*replace-mvar>
  \begin{code}
  _↦-﹙_﹚ : ∀ {Γ m p} → (M : m ∈ Γ) → p ⇒ m
           → Γ ·⟶· Γ [ M ∶ p ]
  Ο ↦-﹙ x ﹚ = Ο ﹙ x ﹚ , wkₛ 1·
  1+ M ↦-﹙ x ﹚ = Ο ﹙ id ﹚ ,  wkₛ (M ↦-﹙ x ﹚) 
  \end{code}
  %</replace-mvar>
  \begin{code}

module OccurCheckType where
    {- ----------------------
    Occur check
    -------------------------- -}
  data occur-cases {Γ m} (M : m ∈ Γ) a : Set where
       Same-MVar : m ⇒ a → occur-cases M a
       Cycle : occur-cases M a
       No-Cycle : Tm· (Γ ⑊ M) a → occur-cases M a
  open occur-cases public
  
module PruneUnifyTypes where
  
\end{code}
%<*prune-type>
\begin{code}
  data [_]∪_⟶? (m : A)(Γ : MetaContext) : Set where
    _◄_ : ∀ Δ → (Tm Δ m) × (Γ ⟶ Δ) → [ m ]∪ Γ ⟶?
\end{code}
%</prune-type>
%<*substfrom>
\begin{code}
  data _⟶? (Γ : MetaContext) : Set where
    _◄_ : ∀ Δ → (Γ ⟶ Δ) → Γ ⟶?
\end{code}
%</substfrom>
\begin{code}
  infix 3 _◄_
  
  infix 3 _·◄_
  infix 3 _◄·_
  infix 3 _·◄·_
  pattern _·◄_ Δ σ = ⌊ Δ ⌋ ◄ σ
  pattern _·◄·_ Δ σ = ⌊ Δ ⌋ ◄ ⌊ σ ⌋
  pattern _◄·_ Δ σ = Δ ◄ ⌊ σ ⌋
  
  infixr 4 _,·_
  pattern _,·_ σ δ = σ , ⌊ δ ⌋
  
  _·⟶? : MetaContext· → Set
  Γ ·⟶?  = ⌊ Γ ⌋ ⟶?
