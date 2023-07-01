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
open import Data.Maybe.Base hiding (map) renaming (nothing to ⊥ ; just to ⌊_⌋)

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
MetaContext : Set
MetaContext = List ℕ
\end{code}
%</lc-metacontext>
%<*lc-syntax>
\begin{code}
data Tm (Γ : MetaContext) (n : ℕ) : Set where
   Var : Fin n → Tm Γ n
   App : Tm Γ n → Tm Γ n → Tm Γ n
   Lam : Tm Γ (1 + n) → Tm Γ n
   _﹙_﹚ : ∀ {m} → m ∈ Γ → m ⇒ n → Tm Γ n
\end{code}
%</lc-syntax>
\begin{code}
-- precedence below _∷_, which is 4
infix 3 _⟶_
\end{code}
%<*substitution-def>
\begin{code}
_⟶_  : MetaContext → MetaContext → Set
Γ ⟶ Δ = VecList (Tm Δ) Γ
\end{code}
%</substitution-def>
\begin{code}


{- ----------------------

Renaming

-------------------------- -}

\end{code}
%<*lc-renaming>
\begin{code}
_❴_❵ : ∀ {Γ n p} → Tm Γ n → n ⇒ p → Tm Γ p

App t u ❴ x ❵ = App (t ❴ x ❵) (u ❴ x ❵)
Lam t ❴ x ❵ = Lam (t ❴ x ↑ ❵)
Var i ❴ x ❵ = Var (i ｛ x ｝)
M ﹙ y ﹚ ❴ x ❵ = M ﹙ x ∘ y ﹚
\end{code}
%</lc-renaming>
\begin{code}
{- ----------------------

Weakening

-------------------------- -}
wkₜ : ∀ {Γ n m} → Tm Γ n → Tm (m ∷ Γ) n

wkₜ (App t u) = App (wkₜ t) (wkₜ u)
wkₜ (Lam t) = Lam (wkₜ t)
wkₜ (Var x) = Var x
wkₜ (M ﹙ x ﹚) = 1+ M ﹙ x ﹚

\end{code}
%<*wk-substitution>
\begin{code}
wkₛ : ∀{Γ Δ m}  → (Γ ⟶ Δ) → (Γ ⟶ m ∷ Δ)
wkₛ σ = VecList.map (λ _ → wkₜ) σ
\end{code}
%</wk-substitution>
\begin{code}

{- ----------------------

Meta substitution

-------------------------- -}

open import Common ℕ _⇒_ id Tm _﹙_﹚ wkₛ
\end{code}
%<*lc-substitution>
\begin{code}
_[_]t : ∀ {Γ n} → Tm Γ n → ∀ {Δ} → (Γ ⟶ Δ) → Tm Δ n
App t u [ σ ]t = App (t [ σ ]t) (u [ σ ]t)
Lam t [ σ ]t = Lam (t [ σ ]t)
Var i [ σ ]t = Var i
M ﹙ x ﹚ [ σ ]t = VecList.nth M σ ❴ x ❵ 
\end{code}%
%</lc-substitution>
%<*composesubst>
\begin{code}
_[_]s : ∀ {Γ₁ Γ₂ Γ₃} → (Γ₁ ⟶ Γ₂) → (Γ₂ ⟶ Γ₃) → (Γ₁ ⟶ Γ₃)
δ [ σ ]s = VecList.map (λ _ t → t [ σ ]t) δ 
\end{code}
%</composesubst>
\begin{code}



{- ----------------------

Occur check

-------------------------- -}

infixl 20 _⑊?ₜ_
\end{code}
% <*lc-occur-check>
\begin{code}
_⑊?ₜ_ : ∀ {Γ m n} → Tm Γ n → (M : m ∈ Γ) → Maybe (Tm (Γ ⑊ M) n)
Var i ⑊?ₜ M = ⌊ Var i ⌋
App t u ⑊?ₜ M = do
     t' ← t ⑊?ₜ M
     u' ← u ⑊?ₜ M
     ⌊ App t' u' ⌋
Lam t ⑊?ₜ M = do
     t' ← t ⑊?ₜ M
     ⌊ Lam t' ⌋
M' ﹙ y ﹚ ⑊?ₜ M with M' ⑊? M 
... | ⊥ = ⊥
... | ⌊ M' ⌋ = ⌊ M' ﹙ y ﹚ ⌋

occur-check : ∀ {Γ m n} → (M : m ∈ Γ) → Tm Γ n → occur-cases M n
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
{-# TERMINATING #-}
\end{code}
%<*lc-prune-proto>
\begin{code}
prune : ∀ {Γ n} → Tm Γ n → ∀ {m} → m ⇒ n → Maybe (m ∷ Γ ⟶?)
\end{code}
%</lc-prune-proto>
%<*prune-app>
\begin{code}
prune (App t u) x = do
          Δ₁ ◄ t' , σ₁ ← prune t x
          Δ₂ ◄ u' , σ₂ ← prune (u [ σ₁ ]t) x
          ⌊ Δ₂ ◄ App (t' [ σ₂ ]t) u' , σ₁ [ σ₂ ]s ⌋
\end{code}
%</prune-app>
%<*prune-lam>
\begin{code}
prune (Lam t) x = do
          Δ ◄ t' , σ ← prune t (x ↑)
          ⌊ Δ ◄ Lam t' , σ ⌋
\end{code}
%</prune-lam>
%<*prune-var>
\begin{code}
prune {Γ} (Var i) x with i ｛ x ｝⁻¹
... | ⊥ = ⊥
... | ⌊ j ⌋ = ⌊ Γ ◄ Var j , idₛ ⌋
\end{code}
%</prune-var>
%<*lc-prune-flex>
\begin{code}
prune {Γ} (M ﹙ x ﹚) y =
   let p , r , l = commonValues x y in
    ⌊ Γ [ M ∶ p ] ◄ (M ∶ p) ﹙ l ﹚ , M ↦-﹙ r ﹚ ⌋
\end{code}
%</lc-prune-flex>
\begin{code}
{- ----------------------

Unification

-------------------------- -}

\end{code}
%<*lc-unify-flex-proto>
\begin{code}
unify-flex-* : ∀ {Γ m n} → m ∈ Γ → m ⇒ n → Tm Γ n → Maybe (Γ ⟶?)
\end{code}
%</lc-unify-flex-proto>
%<*lc-unify-flex-def>
\begin{code}
unify-flex-* {Γ} M x t with occur-check M t
... | Same-MVar y =
   let p , z = commonPositions x y in
   ⌊ Γ [ M ∶ p ] ◄ M ↦-﹙ z ﹚ ⌋
... | Cycle = ⊥
... | No-Cycle t' = do
      Δ ◄ u , σ ← prune t' x
      ⌊ Δ ◄ M ↦ u , σ ⌋
\end{code}
%</lc-unify-flex-def>
\begin{code}

{-# TERMINATING #-}
\end{code}
%<*lc-unifyprototype>
\begin{code}
unify : ∀ {Γ n} → Tm Γ n → Tm Γ n → Maybe (Γ ⟶?)
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
unify (App t u) (App t' u') = do
  Δ₁ ◄ σ₁ ← unify t t'
  Δ₂ ◄ σ₂ ← unify (u [ σ₁ ]t) (u' [ σ₁ ]t)
  ⌊ Δ₂ ◄ σ₁ [ σ₂ ]s ⌋
\end{code}
%</unify-app>
%<*unify-lam>
\begin{code}
unify (Lam t) (Lam t') = unify t t'
\end{code}
%</unify-lam>
%<*unify-var>
\begin{code}
unify {Γ} (Var i) (Var j) with i Fin.≟ j
... | no _ = ⊥
... | yes _ = ⌊ Γ ◄ idₛ ⌋
\end{code}
%</unify-var>
%<*unify-last>
\begin{code}
unify _ _ = ⊥
\end{code}
%</unify-last>
