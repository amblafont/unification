\begin{code}
module lc where

open import Data.Nat using (ℕ; _≟_ ; _+_)
open import Data.Fin as Fin using (Fin)
open import Relation.Nullary using (yes ; no)
open import Data.List as List using (List ; [] ; _∷_) 
open import Data.Vec.Base as Vec using (Vec; []; _∷_)
open import Data.Product using (_,_; Σ; _×_)
open import Data.Maybe.Base using (Maybe) renaming (nothing to ⊥ ; just to ⌊_⌋)

open import lib

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
commonPositions : ∀ {n} m → (x y : m ⇒ n) → Σ ℕ (λ p → p ⇒ m)
commonPositions m [] [] = 0 , []
commonPositions (ℕ.suc m) (x₀ ∷ x) (y₀ ∷ y) with commonPositions m x y | x₀ Fin.≟ y₀
... | p , z | yes _ = p     , Vec.map Fin.suc z
... | p , z | no _  = 1 + p , Fin.zero ∷ Vec.map Fin.suc z
\end{code}
%</common-positions>
\begin{code}


\end{code}
%<*common-values>
\begin{code}
commonValues : ∀ m {m' n} → (x : m ⇒ n) → (y : m' ⇒ n) → Σ ℕ (λ p → p ⇒ m × p ⇒ m')
commonValues m [] y = 0 , [] , []
commonValues (ℕ.suc m ) (x₀ ∷ x) y with commonValues m x y | x₀ ｛ y ｝⁻¹ 
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
\begin{code}
Tm· : MetaContext· → ℕ → Set
\end{code}
%<*lc-syntax-decl>
\begin{code}
data Tm  : MetaContext → ℕ → Set
Tm· Γ n = Tm ⌊ Γ ⌋ n
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

import Common as C
module Common = C ℕ _⇒_ id Tm
open Common.SubstitutionDef public

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

open Common.wkₛ wkₜ

{- ----------------------

Substitution

-------------------------- -}
open Common.!ₛ ! public

\end{code}
%<*lc-substitution>
\begin{code}
_[_]t : ∀ {Γ n} → Tm Γ n → ∀ {Δ} → (Γ ⟶ Δ) → Tm Δ n
App· t u [ σ ]t = App (t [ σ ]t) (u [ σ ]t)
Lam· t [ σ ]t = Lam (t [ σ ]t)
Var· i [ σ ]t = Var i
M ﹙ x ﹚ [ σ ]t = nth σ M ❴ x ❵ 
! [ 1⊥ ]t = !
\end{code}
%</lc-substitution>
\begin{code}

open Common.-[-]s _[_]t public
open Common.1ₛ wkₜ _﹙_﹚ public
open Common.Substitution wkₜ _﹙_﹚ public

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

open Common.occur-cases public
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

open Common.PruneUnifyTypes 
pattern _∶_﹙_﹚ M m x = _﹙_﹚ {m = m} M x

{-# TERMINATING #-}
\end{code}
%<*lc-prune-proto>
\begin{code}
prune : ∀ {Γ m n} → Tm Γ n → m ⇒ n → [ m ]∪ Γ ⟶?
\end{code}
%</lc-prune-proto>
%<*prune-app>
\begin{code}
prune (App· t u) x =
  let Δ₁ ◄ t' , σ₁ = prune t x
      Δ₂ ◄ u' , σ₂ = prune (u [ σ₁ ]t) x
  in  Δ₂ ◄ App (t' [ σ₂ ]t) u' , σ₁ [ σ₂ ]s 
\end{code}
%</prune-app>
%<*prune-lam>
\begin{code}
prune (Lam· t) x =
  let Δ ◄ t' , σ = prune t (x ↑)
  in  Δ ◄ Lam t' , σ
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
prune {⌊ Γ ⌋} (M ∶ m ﹙ x ﹚) y =
  let p , r , l = commonValues m x y
  in Γ [ M ∶ p ] ·◄ (M ∶ p) ﹙ l ﹚ , M ↦-﹙ r ﹚
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
unify-flex-* {Γ} {m} M x t
                  with occur-check M t
... | Same-MVar y =
  let p , z = commonPositions m x y
  in  Γ [ M ∶ p ] ·◄ M ↦-﹙ z ﹚
... | Cycle = ⊥ ◄ !ₛ
... | No-Cycle t' = 
  let Δ ◄ u , σ = prune t' x
  in  Δ ◄ M ↦ u , σ
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
unify (App· t u) (App· t' u') = 
  let Δ₁ ◄ σ₁ = unify t t'
      Δ₂ ◄ σ₂ = unify (u [ σ₁ ]t) (u' [ σ₁ ]t)
  in  Δ₂ ◄ σ₁ [ σ₂ ]s
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
