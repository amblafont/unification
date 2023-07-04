\begin{code}
open import Data.List as List hiding (map ; [_])
open import lib
open import Data.Maybe.Base hiding (map ; _>>=_) renaming (nothing to ⊥ ; just to ⌊_⌋)


module Common (A : Set) 
     (_⇒_ : A → A → Set)
     (id : ∀{a} → a ⇒ a)
     (Tm : Maybe (List A) → A → Set)
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

module SubstitutionDef where
  infix 3 _·⟶_
  infix 3 _·⟶·_
  infix 3 _⟶_
  data _⟶_ : MetaContext → MetaContext → Set
  _·⟶_ : MetaContext· → MetaContext → Set
  _·⟶·_ : MetaContext· → MetaContext· → Set
  
  Γ ·⟶ Δ = ⌊ Γ ⌋ ⟶ Δ
  Γ ·⟶· Δ = ⌊ Γ ⌋ ⟶ ⌊ Δ ⌋
  
  data _⟶_ where
       [] : ∀ {Δ} → ([] ·⟶ Δ )
       _,_ : ∀ {Γ Δ m} → Tm Δ m → (Γ ·⟶ Δ) → (m ∷ Γ) ·⟶ Δ
       1⊥ : ⊥ ⟶ ⊥
  
  nth : ∀ {Γ Δ m} → (Γ ·⟶ Δ) → m ∈ Γ → Tm Δ m
  nth (t , δ) Ο = t
  nth (t , δ) (1+ M) = nth δ M

open SubstitutionDef

module wkₛ 
   (wkₜ : ∀ {Γ a m} → Tm· Γ a → Tm· (m ∷ Γ) a)
   where

   wkₛ : ∀{Γ Δ m}  → (Γ ·⟶· Δ) → (Γ ·⟶· m ∷ Δ)
   wkₛ [] = []
   wkₛ (t , σ) = wkₜ t , wkₛ σ


module !ₛ (! : ∀ {a} → Tm ⊥ a) where
  !ₛ : ∀ {Γ} → Γ ⟶ ⊥
  !ₛ {⊥} = 1⊥
  !ₛ {⌊ [] ⌋} = []
  !ₛ {⌊ m ∷ Γ ⌋} = ! , !ₛ

module -[-]s
   (_[_]t : ∀ {Γ a} → Tm Γ a → ∀ {Δ} → (Γ ⟶ Δ) → Tm Δ a) where

   _[_]s : ∀ {Γ₁ Γ₂ Γ₃} → (Γ₁ ⟶ Γ₂) → (Γ₂ ⟶ Γ₃) → (Γ₁ ⟶ Γ₃)

   [] [ σ ]s = []
   (t , δ) [ σ ]s = t [ σ ]t , δ [ σ ]s
   1⊥ [ 1⊥ ]s = 1⊥

module 1ₛ 
   (wkₜ : ∀ {Γ a m} → Tm· Γ a → Tm· (m ∷ Γ) a)
   (_﹙_﹚ : ∀ {Γ a m} → m ∈ Γ → m ⇒ a → Tm ⌊ Γ ⌋ a)
 where
     open wkₛ wkₜ
   \end{code}
     %<*id-subst>
     \begin{code}
     1ₛ : ∀ {Γ} → Γ ⟶ Γ
     1ₛ {⊥} = 1⊥
     1ₛ {⌊ [] ⌋} = []
     1ₛ {⌊ m ∷ Γ ⌋} = Ο ﹙ id ﹚ , wkₛ 1ₛ
     \end{code}
     %</id-subst>
     \begin{code}
module Substitution 
     (wkₜ : ∀ {Γ a m} → Tm· Γ a → Tm· (m ∷ Γ) a)
     (_﹙_﹚ : ∀ {Γ a m} → m ∈ Γ → m ⇒ a → Tm ⌊ Γ ⌋ a)
   where
   open wkₛ wkₜ
   open 1ₛ wkₜ _﹙_﹚
   
   _↦_,_ : ∀ {Γ Δ m} → (M : m ∈ Γ) → Tm Δ m
            → (Γ ⑊ M ·⟶ Δ) → (Γ ·⟶ Δ)
   Ο ↦ t , σ = t , σ
   1+ M ↦ t , (u , σ) = u , M ↦ t , σ

   _↦-﹙_﹚ : ∀ {Γ m p} → (M : m ∈ Γ) → p ⇒ m
            → Γ ·⟶· Γ [ M ∶ p ]
   Ο ↦-﹙ x ﹚ = Ο ﹙ x ﹚ , wkₛ 1ₛ
   1+ M ↦-﹙ x ﹚ = Ο ﹙ id ﹚ ,  wkₛ (M ↦-﹙ x ﹚) 

-- precedence below _∷_, which is 4
\end{code}
%<*substitution-def>
\begin{code}
\end{code}
%</substitution-def>
\begin{code}

module occur-cases where
    {- ----------------------
    Occur check
    -------------------------- -}
  data occur-cases {Γ m} (M : m ∈ Γ) a : Set where
       Same-MVar : m ⇒ a → occur-cases M a
       Cycle : occur-cases M a
       No-Cycle : Tm· (Γ ⑊ M) a → occur-cases M a
  -- open occur-cases public

module PruneUnifyTypes where
\end{code}
%<*prune-type>
\begin{code}
  record [_]∪_⟶? (m : A)(Γ : MetaContext) : Set where
    constructor _◄_
    field
       Δ : MetaContext
       u,σ : (Tm Δ m) × (Γ ⟶ Δ)
\end{code}
%</prune-type>
%<*substfrom>
\begin{code}
  record _⟶? (Γ : MetaContext) : Set where
    constructor _◄_
    field
        Δ : MetaContext
        σ : Γ ⟶ Δ
\end{code}
%</substfrom>
\begin{code}
  infix 3 _◄_
  infix 3 _·◄_
  pattern _·◄_ Δ σ = ⌊ Δ ⌋ ◄ σ

  _·⟶? : MetaContext· → Set
  Γ ·⟶?  = ⌊ Γ ⌋ ⟶?
