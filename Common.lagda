\begin{code}
open import Data.List as List hiding ([_])
open import Data.List.Membership.Propositional 
open import Data.List.Relation.Unary.Any renaming (_─_ to _⑊_ )
open import lib
open import Data.Maybe.Base using (Maybe) renaming (nothing to ⊥ ; just to ⌊_⌋)
open import Data.Product using (_,_; Σ; _×_)
open import Agda.Primitive


-- k' is typically instantiated as i ⊔ j ⊔ k
module Common {i}{j}{k}(A : Set i)
     (hom : A → A → Set j)
     (id : ∀{a} → hom a a)
     (Tm-parameter : Maybe (List A) → A → Set (i ⊔ j ⊔ k))
  where


private
  k' = i ⊔ j ⊔ k
  MetaContext· = List A
  MetaContext = Maybe MetaContext·
  -- we don't use directly Tm-parameter because the generated latex
  -- font is ugly for a module parameter
  Tm = Tm-parameter
  Tm· = λ Γ a → Tm ⌊ Γ ⌋ a

module SubstitutionDef where
  infix 3 _·⟶_
  infix 3 _·⟶·_
  infix 3 _⟶_
  data _⟶_ : MetaContext → MetaContext → Set k'
  _·⟶_ : MetaContext· → MetaContext → Set k'
  _·⟶·_ : MetaContext· → MetaContext· → Set k'

\end{code}
%<*dotted-substitution>
\begin{code}
  -- Proper substitutions
  Γ ·⟶ Δ = ⌊ Γ ⌋ ⟶ Δ
\end{code}
%</dotted-substitution>
%<*successful-substitution>
\begin{code}
  -- Successful substitutions
  Γ ·⟶· Δ = ⌊ Γ ⌋ ⟶ ⌊ Δ ⌋
\end{code}
%</successful-substitution>
%<*substitution-def>
\begin{code}
  data _⟶_ where
       [] : ∀ {Δ} → ([] ·⟶ Δ )
       _,_ : ∀ {Γ Δ m} → Tm Δ m → (Γ ·⟶ Δ) → (m ∷ Γ ·⟶ Δ)
       1⊥ : ⊥ ⟶ ⊥
\end{code}
%</substitution-def>
\begin{code}

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
   (_[_]t-parameter : ∀ {Γ a} → Tm Γ a → ∀ {Δ} → (Γ ⟶ Δ) → Tm Δ a) where

   private
   -- we don't use directly Tm-parameter because the generated latex
   -- font is ugly for a module parameter
     _[_]t = _[_]t-parameter
\end{code}
%<*compose-substitution-proto>
\begin{code}
   _[_]s : ∀ {Γ Δ E} → (Γ ⟶ Δ) → (Δ ⟶ E) → (Γ ⟶ E)
\end{code}
%</compose-substitution-proto>
%<*compose-substitution-def>
\begin{code}
   [] [ σ ]s = []
   (t , δ) [ σ ]s = t [ σ ]t , δ [ σ ]s
   1⊥ [ 1⊥ ]s = 1⊥
\end{code}
%</compose-substitution-def>
\begin{code}

module 1ₛ 
   (wkₜ : ∀ {Γ a m} → Tm· Γ a → Tm· (m ∷ Γ) a)
   (_﹙_﹚ : ∀ {Γ a m} → m ∈ Γ → hom m a → Tm ⌊ Γ ⌋ a)
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
     (_﹙_﹚ : ∀ {Γ a m} → m ∈ Γ → hom m a → Tm ⌊ Γ ⌋ a)
   where
   open wkₛ wkₜ
   open 1ₛ wkₜ _﹙_﹚
   
   _↦_,_ : ∀ {Γ Δ m} → (M : m ∈ Γ) → Tm Δ m
            → (Γ ⑊ M ·⟶ Δ) → (Γ ·⟶ Δ)
   Ο ↦ t , σ = t , σ
   1+ M ↦ t , (u , σ) = u , M ↦ t , σ

   _↦-﹙_﹚ : ∀ {Γ m p} → (M : m ∈ Γ) → hom p m
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
  data occur-cases {Γ m} (M : m ∈ Γ) a : Set k' where
       Same-MVar : hom m a → occur-cases M a
       Cycle : occur-cases M a
       No-Cycle : Tm· (Γ ⑊ M) a → occur-cases M a

module PruneUnifyTypes where
\end{code}
%<*prune-type>
\begin{code}
  record [_]∪_⟶? m Γ : Set k' where
    constructor _◄_
    field
       Δ : MetaContext
       u,σ : (Tm Δ m) × (Γ ⟶ Δ)
\end{code}
%</prune-type>
%<*substfrom>
\begin{code}
  record _⟶? Γ : Set k' where
    constructor _◄_
    field
        Δ : MetaContext
        σ : Γ ⟶ Δ
\end{code}
%</substfrom>
\begin{code}
  infix 19 _◄_
  infix 19 _·◄_
  pattern _·◄_ Δ σ = ⌊ Δ ⌋ ◄ σ

  _·⟶? : MetaContext· → Set k'
  Γ ·⟶?  = ⌊ Γ ⌋ ⟶?

