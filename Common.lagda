\begin{code}
open import Data.List as List hiding (map ; [_])
open import lib
open VecList using (VecList)


module Common (A : Set) 
     (_⇒_ : A → A → Set)
     (id : ∀{a} → a ⇒ a)
     (Tm : List A → A → Set)
     (_﹙_﹚ : ∀ {Γ : List A}{a}{m} → m ∈ Γ → m ⇒ a → Tm Γ a)
     (let infix 3 _⟶_ ; _⟶_ = λ Γ Δ → VecList (Tm Δ) Γ)
     (wkₛ : ∀{Γ Δ m}  → (Γ ⟶ Δ) → (Γ ⟶ m ∷ Δ))
  where

open import Agda.Builtin.Unit
open import Agda.Builtin.Bool renaming (Bool to 𝔹)
open import Data.Nat using (ℕ; _≟_ ; _+_)
open import Data.Fin as Fin using (Fin)
open import Data.Sum.Base using () renaming (_⊎_ to _∨_ ; inj₁ to left ; inj₂ to right)
open import Relation.Nullary
open import Data.Vec.Base as Vec using (Vec; []; _∷_)
open import Data.Product using (_,_; Σ; _×_)
open import Data.Maybe.Base hiding (map) renaming (nothing to ⊥ ; just to ⌊_⌋)

open import Relation.Binary using (Rel; IsEquivalence; Setoid)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
private
\end{code}
%<*metacontext>
\begin{code}
  MetaContext : Set
  MetaContext = List A
\end{code}
%</metacontext>

%<*id-subst>
\begin{code}
idₛ : ∀ {Γ} → Γ ⟶ Γ
idₛ {[]} = []
idₛ {m ∷ Γ} = Ο ﹙ id ﹚ , wkₛ idₛ
\end{code}
%</id-subst>
%<*extend-subst>
\begin{code}
_↦_,_ : ∀ {Γ Δ m} → (M : m ∈ Γ) → Tm Δ m
         → (Γ ⑊ M ⟶ Δ) → (Γ ⟶ Δ)
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
         → Γ ⟶ (Γ [ M ∶ p ])
Ο ↦-﹙ x ﹚ = Ο ﹙ x ﹚ , wkₛ idₛ
1+ M ↦-﹙ x ﹚ = Ο ﹙ id ﹚ ,  wkₛ (M ↦-﹙ x ﹚) 
\end{code}
%</replace-mvar>
\begin{code}


{- ----------------------

Unification of two metavariables

-------------------------- -}
infix 3 _◄_
infix 3 _⟶?
\end{code}
%<*substfrom>
\begin{code}
data _⟶? (Γ : MetaContext) : Set where
    _◄_ : ∀ Δ → (Γ ⟶ Δ) → Γ ⟶?
\end{code}
%</substfrom>

\begin{code}
{- ----------------------

Occur check

-------------------------- -}

data occur-cases {Γ m} (M : m ∈ Γ) a : Set where
   Same-MVar : m ⇒ a → occur-cases M a
   Cycle : occur-cases M a
   No-Cycle : Tm (Γ ⑊ M) a → occur-cases M a


open occur-cases public
