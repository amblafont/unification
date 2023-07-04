\begin{code}
module lc where

open import Agda.Builtin.Unit
open import Agda.Builtin.Bool renaming (Bool to 𝔹)
open import Data.Nat using (ℕ; _≟_ ; _+_)
open import Data.Fin as Fin using (Fin)
open import Data.Sum.Base using () renaming (_⊎_ to _∨_ ; inj₁ to left ; inj₂ to right)
open import Relation.Nullary
open import Data.List as List hiding (map ; [_])
open import Data.Vec.Base as Vec using (Vec; []; _∷_)
open import Data.Product using (_,_; Σ; _×_) 
open import Data.Maybe.Base hiding (map ; _>>=_) renaming (nothing to ⊥ ; just to ⌊_⌋)


open import Relation.Binary using (Rel; IsEquivalence; Setoid)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

open import lib
open VecList using (VecList)

\end{code}
%<*lc-renamings>
\begin{code}
_⇒_ : ℕ → ℕ → Set
m ⇒ n = Vec (Fin n) m
\end{code}
%</lc-renamings>
\begin{code}


\end{code}
%<*compose-renamings>
\begin{code}
_∘_ : ∀ {p q r} → (q ⇒ r) → (p ⇒ q) → (p ⇒ r)
xs ∘ [] = []
xs ∘ (y ∷ ys) = Vec.lookup xs y ∷ (xs ∘ ys)
\end{code}
%</compose-renamings>
%<*id-renaming>
\begin{code}
id : ∀{n} → n ⇒ n
id {n} = Vec.allFin n
\end{code}
%</id-renaming>
%<*wk-renamings>
\begin{code}
_↑ : ∀ {p q} → p ⇒ q → (1 + p) ⇒ (1 + q)
_↑ {p}{q} x = Vec.insert (Vec.map Fin.inject₁ x)
                    (Fin.fromℕ p) (Fin.fromℕ q)
\end{code}
%</wk-renamings>
\begin{code}

_｛_｝ : ∀ {n p} → Fin n → (n ⇒ p) → Fin p
i ｛ x ｝ = Vec.lookup x i

_｛_｝⁻¹ : ∀ {n p}(x : Fin p) → ∀ (f : n ⇒ p) → Maybe-PreImage (_｛ f ｝) x
i ｛ x ｝⁻¹ = nth⁻¹ Fin._≟_ i x

\end{code}
%<*common-positions>
\begin{code}
commonPositions : ∀ {n m} → (x y : m ⇒ n) → Σ ℕ (λ p → p ⇒ m)
commonPositions [] [] = 0 , []
commonPositions (x₀ ∷ x) (y₀ ∷ y) with commonPositions x y | x₀ Fin.≟ y₀
... | p , z | yes _ = p     , Vec.map Fin.suc z
... | p , z | no _  = 1 + p , Fin.zero ∷ Vec.map Fin.suc z
\end{code}
%</common-positions>
\begin{code}


\end{code}
%<*common-values>
\begin{code}
commonValues : ∀ {m m' n} → (x : m ⇒ n) → (y : m' ⇒ n) → Σ ℕ (λ p → p ⇒ m × p ⇒ m')
commonValues [] y = 0 , [] , []
commonValues (x₀ ∷ x) y with commonValues x y | x₀ ｛ y ｝⁻¹ 
... | p , l , r | ⊥         = p     , Vec.map Fin.suc l            , r
... | p , l , r | ⌊ i ⌋  = 1 + p , Fin.zero ∷ Vec.map Fin.suc l , i ∷ r
\end{code}
%</common-values>
\begin{code}


\end{code}
%<*lc-metacontext>
\begin{code}
MetaContext· = List ℕ
MetaContext = Maybe MetaContext·
\end{code}
%</lc-metacontext>
%<*lc-syntax-decl>
\begin{code}
data Tm  : MetaContext → ℕ → Set
Tm· = λ Γ a → Tm ⌊ Γ ⌋ a
\end{code}
%</lc-syntax-decl>
\begin{code}
\end{code}
%<*lc-syntax-ind>
\begin{code}
data Tm where
   App· : ∀ {Γ n} → Tm· Γ n → Tm· Γ n → Tm· Γ n
   Lam· : ∀ {Γ n} → Tm· Γ (1 + n) → Tm· Γ n
   Var· : ∀ {Γ n} → Fin n → Tm· Γ n
   _﹙_﹚ : ∀ {Γ n m} → m ∈ Γ → m ⇒ n → Tm· Γ n
   ! : ∀ {n} → Tm ⊥ n
\end{code}
%</lc-syntax-ind>
%<*lc-syntax-app-decl>
\begin{code}
App : ∀ {Γ n} → Tm Γ n → Tm Γ n → Tm Γ n
\end{code}
%</lc-syntax-app-decl>
%<*lc-syntax-lam-decl>
\begin{code}
Lam : ∀ {Γ n} → Tm Γ (1 + n) → Tm Γ n
\end{code}
%</lc-syntax-lam-decl>
%<*lc-syntax-var-decl>
\begin{code}
Var : ∀ {Γ n} → Fin n → Tm Γ n
\end{code}
%</lc-syntax-var-decl>
%<*lc-syntax-app-def>
\begin{code}
App {⊥} ! ! = !
App {⌊ Γ ⌋} t u = App· t u
\end{code}
%</lc-syntax-app-def>
%<*lc-syntax-lam-def>
\begin{code}
Lam {⊥} ! = !
Lam {⌊ Γ ⌋} t = Lam· t
\end{code}
%</lc-syntax-lam-def>
%<*lc-syntax-var-def>
\begin{code}
Var {⊥} i = !
Var {⌊ Γ ⌋} i = Var· i
\end{code}
%</lc-syntax-var-def>
\begin{code}
infix 3 _·⟶_
infix 3 _·⟶·_

_·⟶_ : MetaContext· → MetaContext → Set
\end{code}
%<*dot-substitution-def>
\begin{code}
Γ ·⟶ Δ = VecList (Tm Δ) Γ
\end{code}
%</dot-substitution-def>
\begin{code}
_·⟶·_ = λ Γ Δ → Γ ·⟶ ⌊ Δ ⌋

\end{code}
\begin{code}

{- ----------------------

Renaming

-------------------------- -}

\end{code}
%<*lc-renaming>
\begin{code}
_❴_❵ : ∀ {Γ n p} → Tm Γ n → n ⇒ p → Tm Γ p

App· t u ❴ x ❵ = App· (t ❴ x ❵) (u ❴ x ❵)
Lam· t ❴ x ❵ = Lam· (t ❴ x ↑ ❵)
Var· i ❴ x ❵ = Var· (i ｛ x ｝)
M ﹙ y ﹚ ❴ x ❵ = M ﹙ x ∘ y ﹚
! ❴ x ❵ = !
\end{code}
%</lc-renaming>
\begin{code}
{- ----------------------

Weakening

-------------------------- -}
wkₜ : ∀ {Γ n m} → Tm· Γ n → Tm· (m ∷ Γ) n

wkₜ (App· t u) = App· (wkₜ t) (wkₜ u)
wkₜ (Lam· t) = Lam· (wkₜ t)
wkₜ (Var· x) = Var· x
wkₜ (M ﹙ x ﹚) = 1+ M ﹙ x ﹚

import Common ℕ _⇒_ id Tm _﹙_﹚ ! as Common 
\end{code}
%<*wk-substitution>
\begin{code}
wkₛ : ∀{Γ Δ m}  → (Γ ·⟶· Δ) → (Γ ·⟶· m ∷ Δ)
wkₛ σ = VecList.map (λ _ → wkₜ) σ
\end{code}
%</wk-substitution>
\begin{code}

{- ----------------------

Substitution

-------------------------- -}
open Common.Substitution

\end{code}
%<*lc-substitution>
\begin{code}
_[_]t : ∀ {Γ n} → Tm Γ n → ∀ {Δ} → (Γ ⟶ Δ) → Tm Δ n
App· t u [ σ ]t = App (t [ σ ]t) (u [ σ ]t)
Lam· t [ σ ]t = Lam (t [ σ ]t)
Var· i [ σ ]t = Var i
M ﹙ x ﹚ [ ⌊ σ ⌋ ]t = VecList.nth M σ ❴ x ❵ 
! [ 1⊥ ]t = !
\end{code}%
%</lc-substitution>
\begin{code}
-- to make the type signature of _·[_]s shorter
module _ {Γ₁ : MetaContext·}{Γ₂ Γ₃ : MetaContext} where
\end{code}
%<*composesubst>
\begin{code}
  _·[_]s : (Γ₁ ·⟶ Γ₂) → (Γ₂ ⟶ Γ₃) → (Γ₁ ·⟶ Γ₃)
  δ ·[ σ ]s = VecList.map (λ _ t → t [ σ ]t) δ
\end{code}
%</composesubst>
\begin{code}

open Common.MoreSubstitution wkₛ _·[_]s public

{- ----------------------

Occur check

-------------------------- -}

\end{code}
% <*lc-occur-check>
\begin{code}
module _ where
  open Data.Maybe.Base using (_>>=_)
  infixl 20 _⑊?ₜ_
  _⑊?ₜ_ : ∀ {Γ m a} → Tm· Γ a → (M : m ∈ Γ) → Maybe (Tm· (Γ ⑊ M) a)
  Var· i ⑊?ₜ M = ⌊ Var· i ⌋
  App· t u ⑊?ₜ M = do
      t' ← t ⑊?ₜ M
      u' ← u ⑊?ₜ M
      ⌊ App· t' u' ⌋
  Lam· t ⑊?ₜ M = do
      t' ← t ⑊?ₜ M
      ⌊ Lam· t' ⌋
  M' ﹙ y ﹚ ⑊?ₜ M with M' ⑊? M 
  ... | ⊥ = ⊥
  ... | ⌊ M' ⌋ = ⌊ M' ﹙ y ﹚ ⌋


open Common.OccurCheckType

occur-check : ∀ {Γ m n} → (M : m ∈ Γ) → Tm· Γ n → occur-cases M n
occur-check M (M' ﹙ x ﹚) with M' ⑊? M 
... | ⊥ = Same-MVar x
... | ⌊ M' ⌋ = No-Cycle (M' ﹙ x ﹚)
occur-check M t with t ⑊?ₜ M
... | ⊥ = Cycle
... | ⌊ t' ⌋ = No-Cycle t'
\end{code}
% </lc-occur-check>
\begin{code}

{- ----------------------

Pruning

-------------------------- -}
open IdentityDoNotation
open Common.PruneUnifyTypes
{-# TERMINATING #-}
\end{code}
%<*lc-prune-proto>
\begin{code}
prune : ∀ {Γ n m} → Tm Γ n → m ⇒ n → [ m ]∪ Γ ⟶?
\end{code}
%</lc-prune-proto>
%<*prune-app>
\begin{code}
prune (App· t u) x = do
          Δ₁ ◄ t' , σ₁ ← prune t x
          Δ₂ ◄ u' , σ₂ ← prune (u [ σ₁ ]t) x
          Δ₂ ◄ App (t' [ σ₂ ]t) u' , σ₁ [ σ₂ ]s 
\end{code}
%</prune-app>
%<*prune-lam>
\begin{code}
prune (Lam· t) x = do
          Δ ◄ t' , σ ← prune t (x ↑)
          Δ ◄ Lam t' , σ
\end{code}
%</prune-lam>
%<*prune-var>
\begin{code}
prune {Γ} (Var· i) x with i ｛ x ｝⁻¹
... | ⊥ = ⊥ ◄ ! , !ₛ
... | ⌊ j ⌋ = Γ ◄ Var j , 1ₛ
\end{code}
%</prune-var>
%<*lc-prune-flex>
\begin{code}
prune {⌊ Γ ⌋} (M ﹙ x ﹚) y =
   let p , r , l = commonValues x y in
    Γ [ M ∶ p ] ·◄ (M ∶ p) ﹙ l ﹚ ,· M ↦-﹙ r ﹚
\end{code}
%</lc-prune-flex>
%<*prune-fail>
\begin{code}
prune ! y = ⊥ ◄ ! , !ₛ
\end{code}
%</prune-fail>

{- ----------------------

Unification

-------------------------- -}

\end{code}
%<*lc-unify-flex-proto>
\begin{code}
unify-flex-* : ∀ {Γ m n} → m ∈ Γ → m ⇒ n → Tm· Γ n → Γ ·⟶?
\end{code}
%</lc-unify-flex-proto>
%<*lc-unify-flex-def>
\begin{code}
unify-flex-* {Γ} M x t with occur-check M t
... | Same-MVar y =
   let p , z = commonPositions x y in
   Γ [ M ∶ p ] ·◄· M ↦-﹙ z ﹚
... | Cycle = ⊥ ◄ !ₛ
... | No-Cycle t' = do
          Δ ◄ u ,· σ ← prune t' x
          Δ ◄· M ↦ u , σ
\end{code}
%</lc-unify-flex-def>
\begin{code}


{-# TERMINATING #-}
\end{code}
%<*lc-unifyprototype>
\begin{code}
unify : ∀ {Γ n} → Tm Γ n → Tm Γ n → Γ ⟶?
\end{code}
%</lc-unifyprototype>
%<*unify-flex>
\begin{code}
unify t (M ﹙ x ﹚) = unify-flex-* M x t
unify (M ﹙ x ﹚) t = unify-flex-* M x t
\end{code}
%</unify-flex>
%<*unify-app>
\begin{code}
unify (App· t u) (App· t' u') = do
  Δ₁ ◄ σ₁ ← unify t t'
  Δ₂ ◄ σ₂ ← unify (u [ σ₁ ]t) (u' [ σ₁ ]t)
  Δ₂ ◄ σ₁ [ σ₂ ]s
\end{code}
%</unify-app>
%<*unify-lam>
\begin{code}
unify (Lam· t) (Lam· t') = unify t t'
\end{code}
%</unify-lam>
%<*unify-var>
\begin{code}
unify {Γ} (Var· i) (Var· j) with i Fin.≟ j
... | no _ = ⊥ ◄ !ₛ
... | yes _ = Γ ◄ 1ₛ
\end{code}
%</unify-var>
%<*unify-last>
\begin{code}
unify ! ! = ⊥ ◄ !ₛ
unify _ _ = ⊥ ◄ !ₛ
\end{code}
%</unify-last>
