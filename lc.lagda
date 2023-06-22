\begin{code}
{-# OPTIONS --type-in-type --no-termination-check #-}
module lc where

open import Agda.Builtin.Unit
open import Agda.Builtin.Bool renaming (Bool to 𝔹)
open import Data.Nat using (ℕ; _≟_ ; _+_)
open import Data.Fin as Fin using (Fin)
open import Data.Sum.Base using () renaming (_⊎_ to _∨_ ; inj₁ to left ; inj₂ to right)
open import Relation.Nullary
open import Data.List as List hiding (map ; [_])
open import Data.Vec.Base as Vec using (Vec; []; _∷_)
open import Data.Product using (_,_; Σ; _×_) -- renaming (Σ[_∈_]_ to Σ[_∶_]_)
open import Data.Maybe.Base hiding (map) renaming (nothing to ⊥ ; just to ⌊_⌋)

open import Relation.Binary using (Rel; IsEquivalence; Setoid)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

open import lib
open VecList using (VecList)

module _ where
\end{code}
%<*renamings>
\begin{code}
  _⇒_ : ℕ → ℕ → Set
  m ⇒ n = Vec (Fin n) m
\end{code}
%</renamings>
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

module _ where
 -- open A




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

 _｛_｝ : ∀ {n p} → Fin n → (n ⇒ p) → Fin p
 i ｛ x ｝ = Vec.lookup x i

 _｛_｝⁻¹ : ∀ {n p}(x : Fin p) → ∀ (f : n ⇒ p) → Maybe (PreImage (_｛ f ｝) x)
 i ｛ x ｝⁻¹ = nth⁻¹ Fin._≟_ i x

\end{code}
%<*common-values>
\begin{code}
 commonValues : ∀ {m m' n} → (x : m ⇒ n) → (y : m' ⇒ n) → Σ ℕ (λ p → p ⇒ m × p ⇒ m')
 commonValues [] y = 0 , [] , []
 commonValues (x₀ ∷ x) y with commonValues x y | x₀ ｛ y ｝⁻¹ 
 ... | p , l , r | ⊥         = p     , Vec.map Fin.suc l            , r
 ... | p , l , r | ⌊ Pre i ⌋  = 1 + p , Fin.zero ∷ Vec.map Fin.suc l , i ∷ r
\end{code}
%</common-values>
\begin{code}


module _ where

\end{code}
%<*metacontext>
\begin{code}
   MetaContext : Set
   MetaContext = List ℕ
\end{code}
%</metacontext>
\begin{code}

   module _ where
    -- open A
\end{code}
%<*syntax>
\begin{code}
    data Tm (Γ : MetaContext) (n : ℕ) : Set where
       Var : Fin n → Tm Γ n
       App : Tm Γ n → Tm Γ n → Tm Γ n
       Lam : Tm Γ (1 + n) → Tm Γ n
       _﹙_﹚ : ∀ {m} → m ∈ Γ → m ⇒ n → Tm Γ n
\end{code}
%</syntax>
\begin{code}


{- ----------------------

Renaming

-------------------------- -}

\end{code}
%<*renaming>
\begin{code}
    _❴_❵ : ∀ {Γ n p} → Tm Γ n → n ⇒ p → Tm Γ p

    App t u ❴ f ❵ = App (t ❴ f ❵) (u ❴ f ❵)
    Lam t ❴ f ❵ = Lam (t ❴ f ↑ ❵)
    Var i ❴ f ❵ = Var (i ｛ f ｝)
    M ﹙ x ﹚ ❴ f ❵ = M ﹙ f ∘ x ﹚
\end{code}
%</renaming>
\begin{code}
{- ----------------------

Weakening

-------------------------- -}
   wkₜ : ∀ {Γ n m} → Tm Γ n → Tm (m ∷ Γ) n

   wkₜ (App t u) = App (wkₜ t) (wkₜ u)
   wkₜ (Lam t) = Lam (wkₜ t)
   wkₜ (Var x) = Var x
   wkₜ (M ﹙ x ﹚) = 1+ M ﹙ x ﹚


{- ----------------------

MetaSubstitution

-------------------------- -}

   -- precedence below _∷_, which is 4
   infix 3 _⟶_
\end{code}
%<*substitution-def>
\begin{code}
   _⟶_  : MetaContext → MetaContext → Set
   Γ ⟶ Δ = VecList (Tm Δ) Γ
\end{code}
%</substitution-def>
%<*wk-substitution>
\begin{code}
   wkₛ : ∀{Γ Δ m}  → (Γ ⟶ Δ) → (Γ ⟶ m ∷ Δ)
   wkₛ σ = VecList.map (λ _ → wkₜ) σ
\end{code}
%</wk-substitution>
%<*substitution>
\begin{code}

   _[_]t : ∀ {Γ n} → Tm Γ n → ∀ {Δ} → (Γ ⟶ Δ) → Tm Δ n
   App t u [ σ ]t = App (t [ σ ]t) (u [ σ ]t)
   Lam t [ σ ]t = Lam (t [ σ ]t)
   Var i [ σ ]t = Var i
   M ﹙ x ﹚ [ σ ]t = VecList.nth M σ ❴ x ❵ 
\end{code}
%</substitution>
%<*composesubst>
\begin{code}
   _[_]s : ∀ {Γ₁ Γ₂ Γ₃} → (Γ₁ ⟶ Γ₂) → (Γ₂ ⟶ Γ₃) → (Γ₁ ⟶ Γ₃)
   δ [ σ ]s = VecList.map (λ _ t → t [ σ ]t) δ 
\end{code}
%</composesubst>
\begin{code}


{- ----------------------

The category of metavariable contexts and substitutions

-------------------------- -}

\end{code}
%<*id-subst>
\begin{code}
   idₛ : ∀ {Γ} → Γ ⟶ Γ

   idₛ {[]} = tt
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

Occur check

-------------------------- -}

   infixl 20 _⑊?ₜ_
\end{code}
% <*occur-check>
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
\end{code}
% </occur-check>
\begin{code}

{- ----------------------

Unification of two metavariables

-------------------------- -}
module _ where
  -- open A
  infix 3 _◄_
  infix 3 _⟶?
\end{code}
%<*substfrom>
\begin{code}
  data _⟶? (Γ : MetaContext) : Set where
     _◄_ : ∀ Δ → (Γ ⟶ Δ) → Γ ⟶?
\end{code}
%</substfrom>
%<*unify-flex-flex-proto>
\begin{code}
  unify-flex-flex : ∀ {Γ m m' n} → m  ∈ Γ → m  ⇒ n
                                 → m' ∈ Γ → m' ⇒ n → Γ ⟶?
  unify-flex-flex {Γ} M x M' y with M' ⑊? M
\end{code}
%</unify-flex-flex-proto>
%<*unify-flex-flex-same>
\begin{code}
  ... | ⊥ =
   let p , z = commonPositions x y in
   Γ [ M ∶ p ] ◄ M ↦-﹙ z ﹚
\end{code}
%</unify-flex-flex-same>
%<*unify-flex-flex-diff>
\begin{code}
  ... | ⌊ M' ⌋ =
   let p , l , r = commonValues x y in
   Γ ⑊ M [ M' ∶ p ] ◄ M ↦ (M' ∶ p) ﹙ l ﹚
                     , M' ↦-﹙ r ﹚
\end{code}
%</unify-flex-flex-diff>
\begin{code}

{- ----------------------

Non cyclic unification

-------------------------- -}
  unify-no-cycle : ∀ {Γ n} → Tm Γ n
      → ∀ {m} → m ⇒ n → Maybe (m ∷ Γ ⟶?)

  unify-no-cycle (App t u) x = do
            Δ₁ ◄ t' , σ₁ ← unify-no-cycle t x
            Δ₂ ◄ u' , σ₂ ← unify-no-cycle (u [ σ₁ ]t) x
            ⌊ Δ₂ ◄ App (t' [ σ₂ ]t) u' , σ₁ [ σ₂ ]s ⌋
  unify-no-cycle (Lam t) x = do
            Δ ◄ t' , σ ← unify-no-cycle t (x ↑)
            ⌊ Δ ◄ Lam t' , σ ⌋
  unify-no-cycle {Γ} (Var i) x = do
         Pre i' ←  i ｛ x ｝⁻¹
         ⌊ Γ ◄ Var i' , idₛ ⌋

  unify-no-cycle (M ﹙ y ﹚) x =
      ⌊ unify-flex-flex (1+ M) y Ο x ⌋

{- ----------------------

Unification

-------------------------- -}

\end{code}
%<*unify-flex-def>
\begin{code}
  unify-flex-* : ∀ {Γ m n} → m ∈ Γ → m ⇒ n → Tm Γ n → Maybe (Γ ⟶?)
  unify-flex-* M x (N ﹙ y ﹚) = ⌊ unify-flex-flex M x N y ⌋
  unify-flex-* M x u = do
      u' ← u ⑊?ₜ M
      Δ ◄ t , σ ← unify-no-cycle u' x
      ⌊ Δ ◄ M ↦ t , σ ⌋
\end{code}
%</unify-flex-def>
\begin{code}

\end{code}
%<*unifyprototype>
\begin{code}
  unify : ∀ {Γ n} → Tm Γ n → Tm Γ n → Maybe (Γ ⟶?)
\end{code}
%</unifyprototype>
%<*unify-flex>
\begin{code}
  unify u (M ﹙ x ﹚) = unify-flex-* M x u
  unify (M ﹙ x ﹚) u = unify-flex-* M x u
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
