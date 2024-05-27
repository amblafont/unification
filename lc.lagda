\begin{code}
module lc where

open import Data.Vec.Base as Vec using (Vec; []; _∷_)
open import Data.Vec.Membership.Propositional renaming (_∈_ to _∈̬_ )
open import Data.Vec.Membership.Propositional.Properties as VecProp
open import Data.Vec.Relation.Unary.Any as VecAny using (here ; there)
open import Data.Vec.Relation.Unary.Any.Properties as VecProp hiding (map-id)
open import Data.List as List using (List ; [] ; _∷_) 
open import Data.List.Membership.Propositional 
open import Data.List.Relation.Unary.Any renaming (_─_ to _⑊_ )
open import Data.Fin as Fin using (Fin)
open import Data.Nat using (ℕ; _≟_ ; _+_)
open import Data.Product as Product using (_,_; Σ; _×_)
open import Data.Maybe.Base using (Maybe) renaming (nothing to ⊥ ; just to ⌊_⌋)
open import Data.Bool.Base
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_ ) renaming (refl to 1ₑ)
import Relation.Unary
open import Relation.Nullary using (yes ; no ; does)

open import lib

\end{code}
%<*lc-renamings>
\begin{code}
hom : ℕ → ℕ → Set
hom m n = Vec (Fin n) m
\end{code}
%</lc-renamings>
\begin{code}


\end{code}
%<*compose-renamings>
\begin{code}
_∘_ : ∀ {p q r} → hom q r → hom p q → hom p r
xs ∘ ys = Vec.map (Vec.lookup xs) ys
\end{code}
%</compose-renamings>
%<*id-renaming>
\begin{code}
id : ∀{n} → hom n n
id {n} = Vec.allFin n
\end{code}
%</id-renaming>
%<*wk-renamings>
\begin{code}
_↑ : ∀ {p q} → hom p q → hom (1 + p) (1 + q)
_↑ {p}{q} x = Vec.insertAt (Vec.map Fin.inject₁ x)
                    (Fin.fromℕ p) (Fin.fromℕ q)
\end{code}
%</wk-renamings>
\begin{code}

_｛_｝ : ∀ {n p} → Fin n → hom n p → Fin p
i ｛ x ｝ = Vec.lookup x i

_｛_｝⁻¹ : ∀ {n p}(x : Fin p) → ∀ (f : hom n p) → Maybe (pre-image (_｛ f ｝) x)
i ｛ x ｝⁻¹ = MoreVec.lookup⁻¹ Fin._≟_ i x

{- ----------------------

Common positions

-------------------------- -}
\end{code}
%<*common-positions>
\begin{code}
commonPositions : ∀ {n} m → (x y : hom m n) → Σ ℕ (λ p → hom p m)
commonPositions m [] [] = 0 , []
commonPositions (ℕ.suc m) (x₀ ∷ x) (y₀ ∷ y) =
   let p , z = commonPositions m x y in
   let z' = Vec.map Fin.suc z in
   if does (x₀ Fin.≟ y₀) then
     1 + p , Fin.zero ∷ z'
   else
     p , z'
\end{code}
%</common-positions>
\begin{code}

-- sanity check: any common position must be in the vector of common positions 
commonPositions-property : ∀ {n m i} → (x y : hom m n) → Vec.lookup x i ≡ Vec.lookup y i →
        let (p , z) = commonPositions m x y in
        i ∈̬ z
commonPositions-property {i = i}(x ∷ xs) (y ∷ ys) e' with i | x Fin.≟ y
... | Fin.zero | no e = ⊥-elim (e e')
... | Fin.suc j | no e = VecProp.∈-map⁺ Fin.suc (commonPositions-property xs ys e')
... | Fin.zero | yes e = here 1ₑ
... | Fin.suc j | yes 1ₑ = there (∈-map⁺ Fin.suc (commonPositions-property xs ys e'))



{- ----------------------

Common values

-------------------------- -}


\end{code}
%<*common-values>
\begin{code}
commonValues : ∀ m {m' n} → (x : hom m n) → (y : hom m' n) → Σ ℕ (λ p → hom p m × hom p m')
commonValues m [] y = 0 , [] , []
commonValues (ℕ.suc m ) (x₀ ∷ x) y =
   let p , l , r = commonValues m x y in
   let indices = MoreVec.find-indices (λ x' → x' Fin.≟ x₀) y in
   -- count is at most 1 for injective renamings
   let count = List.length indices in
   count + p ,
       Vec.replicate _ Fin.zero Vec.++ Vec.map Fin.suc l ,
       Vec.fromList indices Vec.++ r
\end{code}
%</common-values>
\begin{code}

-- sanity check: any common value must be in the vectors of common value positions
module _ where
  open import Data.Vec.Properties using (lookup-zip ; lookup-replicate ; map-zip ; map-id)

  commonValues-property : ∀ {m m' n v} → (x : hom m n) (y : hom m' n) → (vx : v ∈̬ x) → (vy : v ∈̬ y) →
          let p , l , r = commonValues _ x y in
         (VecAny.index vx , VecAny.index vy) ∈̬ Vec.zip l r
  commonValues-property .(x ∷ xs) ys (here {x = x} {xs = xs} px) vy
      with p , l , r ← commonValues _ xs ys
      | indices ←  (MoreVec.find-indices (Fin._≟ x) ys)
      | indice∈ ← MoreVec.find-indices-∈ (Fin._≟ x) vy px
      = let count = List.length indices in
         let vindices = Vec.fromList indices in
         ≡.subst₂ (λ a → a ∈̬_ ) eq
           (≡.sym  (Data.Vec.Properties.zipWith-++ _,_ (Vec.replicate _ Fin.zero) (Vec.map Fin.suc l) vindices r))
         (
           ∈-++⁺ˡ {xs = Vec.zip (Vec.replicate _ Fin.zero) vindices}
              (VecProp.∈-lookup (VecAny.index (VecProp.∈-fromList⁺ indice∈)) _)
            )
            where
              eq : Vec.lookup (Vec.zip (Vec.replicate _ Fin.zero) (Vec.fromList indices) )
                    (VecAny.index (VecProp.∈-fromList⁺ indice∈))
                   ≡ (Fin.zero , VecAny.index vy)
              -- eq rewrite MoreVec.index-∈-fromList⁺ indice∈ =  ≡.trans
              eq =  ≡.trans
                     ( lookup-zip (VecAny.index (VecProp.∈-fromList⁺ indice∈)) (Vec.replicate _ Fin.zero) (Vec.fromList indices) )
                     (≡.cong₂ _,_
                     (≡.trans
                        ( ≡.cong (Vec.lookup (Vec.replicate _ Fin.zero)) (VecProp.index-∈-fromList⁺ indice∈) )
                        (lookup-replicate (index indice∈) Fin.zero))
                        (≡.sym (VecProp.lookup-index (VecProp.∈-fromList⁺ indice∈))))

  commonValues-property .(_ ∷ _) ys (there {x = x}{xs = xs} vx) vy with
        p , l , r ← commonValues _ xs ys
      | indices ←  MoreVec.find-indices (Fin._≟ x) ys 
      | rec ← commonValues-property xs ys vx vy
      rewrite Data.Vec.Properties.zipWith-++ _,_ (Vec.replicate _ Fin.zero) (Vec.map Fin.suc l) (Vec.fromList indices) r =
        ∈-++⁺ʳ (Vec.zip (Vec.replicate _ Fin.zero) (Vec.fromList indices))
         ( ≡.subst (_ ∈̬_)
           (≡.trans (map-zip Fin.suc (λ m → m) _ _) (≡.cong (Vec.zip _) (map-id r))) 
         (∈-map⁺ (Product.map Fin.suc (λ m → m)) rec) )


{- ----------------------

Syntax

-------------------------- -}

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
   _﹙_﹚ : ∀ {Γ n m} → m ∈ Γ → hom m n → Tm· Γ n
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
module Common = C ℕ hom id Tm
open Common.SubstitutionDef public

{- ----------------------

Renaming

-------------------------- -}

\end{code}
%<*lc-renaming>
\begin{code}
_❴_❵ : ∀ {Γ n p} → Tm Γ n → hom n p → Tm Γ p

(App· t u) ❴ x ❵ = App· (t ❴ x ❵) (u ❴ x ❵)
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
(App· t u) [ σ ]t = App (t [ σ ]t) (u [ σ ]t)
Lam· t [ σ ]t = Lam (t [ σ ]t)
Var· i [ σ ]t = Var i
M ﹙ x ﹚ [ σ ]t = nth σ M  ❴ x ❵ 
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
prune : ∀ {Γ m n} → Tm Γ n → hom m n → [ m ]∪ Γ ⟶?
\end{code}
%</lc-prune-proto>
%<*prune-app>
\begin{code}
prune (App· t u) x =
  let Δ₁ ◄ (t' , σ₁) = prune t x
      Δ₂ ◄ (u' , σ₂) = prune (u [ σ₁ ]t) x
  in  Δ₂ ◄ (App (t' [ σ₂ ]t) u' , σ₁ [ σ₂ ]s) 
\end{code}
%</prune-app>
%<*prune-lam>
\begin{code}
prune (Lam· t) x =
  let Δ ◄ (t' , σ) = prune t (x ↑)
  in  Δ ◄ (Lam t' , σ)
\end{code}
%</prune-lam>
%<*prune-var>
\begin{code}
prune {Γ} (Var· i) x with i ｛ x ｝⁻¹
... | ⊥ = ⊥ ◄ (! , !ₛ)
... | ⌊ PreImage j ⌋ = Γ ◄ (Var j , 1ₛ)
\end{code}
%</prune-var>
%<*lc-prune-flex>
\begin{code}
prune {⌊ Γ ⌋} (M ∶ m ﹙ x ﹚) y =
  let p , x' , y' = commonValues m x y
  in Γ [ M ∶ p ] ·◄ ((M ∶ p) ﹙ y' ﹚ , M ↦-﹙ x' ﹚)
\end{code}
%</lc-prune-flex>
%<*prune-fail>
\begin{code}
prune ! y = ⊥ ◄ (! , !ₛ)
\end{code}
%</prune-fail>

{- ----------------------

Unification

-------------------------- -}

\end{code}
%<*lc-unify-flex-proto>
\begin{code}
unify-flex-* : ∀ {Γ m n} → m ∈ Γ → hom m n → Tm· Γ n → Γ ·⟶?
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
  let Δ ◄ (u , σ) = prune t' x
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
%<*unify-bot>
\begin{code}
unify ! ! = ⊥ ◄ !ₛ
\end{code}
%</unify-bot>
%<*unify-last>
\begin{code}
unify _ _ = ⊥ ◄ !ₛ
\end{code}
%</unify-last>
