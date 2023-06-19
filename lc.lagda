\begin{code}
{-# OPTIONS --type-in-type --no-termination-check #-}
module lc where

open import Agda.Builtin.Unit
-- open import Agda.Builtin.Maybe
open import Agda.Builtin.Bool renaming (Bool to 𝔹)
open import Data.Nat using (ℕ; _≟_ ; _+_)
open import Data.Fin as Fin using (Fin)
open import Relation.Nullary
open import Data.List as List hiding (map)
open import Data.Vec.Base as Vec using (Vec; []; _∷_)
open import Data.Product using (_,_; Σ; _×_)
open import Data.Maybe.Base hiding (map)

open import Relation.Binary using (Rel; IsEquivalence; Setoid)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

open import lib

module A where
\end{code}
%<*renamings>
\begin{code}
  _⇒_ : ℕ → ℕ → Set
  p ⇒ q = Vec (Fin q) p
\end{code}
%</renamings>
\begin{code}

  wk-⇒ : ∀ {p}{q} → p ⇒ q → (1 + p) ⇒ (1 + q) 
  wk-⇒ {p}{q} l = Vec.insert (Vec.map Fin.inject₁ l) (Fin.fromℕ p) (Fin.fromℕ q)

  _∘_ : ∀ {p q r} → (q ⇒ r) → (p ⇒ q) → (p ⇒ r)
  xs ∘ [] = []
  xs ∘ (y ∷ ys) = Vec.lookup xs y ∷ (xs ∘ ys)

  id : ∀{n} → n ⇒ n
  id {n} = Vec.allFin n

module _ where
 open A

 record Equalizer {p q : ℕ} (f g : p ⇒ q) : Set where
  field
    obj : ℕ
    arr   : obj ⇒ p
 record Pullback {X Y Z : ℕ} (f : X ⇒ Z) (g : Y ⇒ Z) : Set where
  field
    P : ℕ
    p₁  : P ⇒ X
    p₂  : P ⇒ Y



 equalizers : ∀ {a b}(f g : a ⇒ b) → Equalizer f g
 equalizers [] [] = record { arr = [] }
 equalizers (x ∷ f) (y ∷ g) with equalizers f g
 ... | record { obj = obj ; arr = arr } with x Fin.≟ y
 ... | false because _ = record { obj = obj     ; arr = Vec.map Fin.suc arr }
 ... | true because  _ = record { obj = 1 + obj ; arr = Fin.zero ∷ Vec.map Fin.suc arr }



 pullbacks : {X Y Z : ℕ} (f : X ⇒ Z) (g : Y ⇒ Z) → Pullback f g
 pullbacks [] g = record { p₁ = [] ; p₂ = [] }
 pullbacks (x ∷ f) g with find-∈ Fin._≟_ x g
 ... | nothing =  record { P = P; p₁ = Vec.map Fin.suc p₁ ; p₂ = p₂ }
    where open Pullback (pullbacks f g)
 ... | just i  =  record { P = 1 + P; p₁ = Fin.zero ∷ Vec.map Fin.suc p₁ ; p₂ = i ∷ p₂ }
    where open Pullback (pullbacks f g)

 _｛_｝ : ∀ {n}{p} → Fin n → (n ⇒ p) → Fin p
 x ｛ f ｝ = Vec.lookup f x

 _｛_｝⁻¹ : ∀ {n}{p}(x : Fin p) → ∀ (f : n ⇒ p) → Maybe (PreImage (_｛ f ｝) x)
 x ｛ f ｝⁻¹ = find-PreImage-Vec Fin._≟_ x f

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
    open A
\end{code}
%<*syntax>
\begin{code}
    data Tm (Γ : MetaContext) (n : ℕ) : Set where
       Var : Fin n → Tm Γ n
       App : Tm Γ n → Tm Γ n → Tm Γ n
       Lam : Tm Γ (1 + n) → Tm Γ n
       Flexible : ∀ {m} → m ∈ Γ → m ⇒ n → Tm Γ n
\end{code}
%</syntax>
\begin{code}


{- ----------------------

Renaming

-------------------------- -}

    _❴_❵ : ∀ {Γ}{n}{p} → Tm Γ n → n ⇒ p → Tm Γ p

    App t u ❴ f ❵ = App (t ❴ f ❵) (u ❴ f ❵)
    Lam t ❴ f ❵ = Lam (t ❴ wk-⇒ f ❵)
    Var x ❴ f ❵ = Var (x ｛ f ｝)
    Flexible M xs ❴ f ❵ = Flexible M (f ∘ xs)


{- ----------------------

MetaSubstitution

-------------------------- -}

\end{code}
%<*substitution-def>
\begin{code}
   substitution : MetaContext → MetaContext → Set
   substitution Γ Δ = VecList.t (Tm Δ) Γ
\end{code}
%</substitution-def>
\begin{code}
   -- precedence below _∷_, which is 4
   infix 3 _⟶_
\end{code}
%<*substitution>
\begin{code}
   _⟶_ = substitution

   _[_]t : ∀ {Γ}{n} → Tm Γ n → ∀ {Δ} → (Γ ⟶ Δ) → Tm Δ n
   App t u [ σ ]t = App (t [ σ ]t) (u [ σ ]t)
   Lam t [ σ ]t = Lam (t [ σ ]t)
   Var x [ σ ]t = Var x
   Flexible M f [ σ ]t = VecList.nth M σ ❴ f ❵ 
\end{code}
%</substitution>
\begin{code}

   _↦_,_ : ∀ {Γ}{Δ}{m} → (M : m ∈ Γ) → Tm Δ m → (Γ without M ⟶ Δ) → (Γ ⟶ Δ)
   here _ ↦ t , σ = t , σ
   there M ↦ t , (u , σ) = u , (M ↦ t , σ)

{- ----------------------

Weakening

-------------------------- -}
   wk-Tm : ∀ {Γ}{n} m → Tm Γ n → Tm (m ∷ Γ) n

   wk-Tm m (App t u) = App (wk-Tm m t) (wk-Tm m u)
   wk-Tm m (Lam t) = Lam (wk-Tm m t)
   wk-Tm m (Var x) = Var x
   wk-Tm m (Flexible M f) = Flexible (there M) f


   wk-subst : ∀{Γ Δ} m → (Γ ⟶ Δ) → (Γ ⟶ m ∷ Δ)
   wk-subst m σ = VecList.map (λ x → wk-Tm m) σ


{- ----------------------

The category of metavariable contexts and substitutions

-------------------------- -}

\end{code}
%<*composesubst>
\begin{code}
   _[_]s : ∀ {Γ₁ Γ₂ Γ₃} → (Γ₁ ⟶ Γ₂) → (Γ₂ ⟶ Γ₃) → (Γ₁ ⟶ Γ₃)
   δ [ σ ]s = VecList.map (λ _ t → t [ σ ]t) δ 
\end{code}
%</composesubst>
\begin{code}

   module S where

      id : ∀ {Γ} → Γ ⟶ Γ

      wk-id : ∀ {Γ} m → Γ ⟶ m ∷ Γ
      wk-id m = wk-subst m id

      id {[]} = tt
      id {m ∷ Γ} = (Flexible (here _) A.id) , wk-id m


{- ----------------------

Occur check

-------------------------- -}

   occur-check : ∀ {Γ}{m}(M : m ∈ Γ) {n} → Tm Γ n
        → Maybe (Tm (Γ without M) n)
   occur-check M (App t u) = do
       t' ← occur-check M t
       u' ← occur-check M u
       just (App t' u') 
   occur-check M (Lam t) = do
       t' ← occur-check M t
       just (Lam t')
   occur-check M (Var x) = just (Var x)
   occur-check M (Flexible M' f) = do
       M'' ← restricts∈ M M'
       just (Flexible M'' f)

{- ----------------------

Unification of two metavariables

-------------------------- -}
module _ where
  open A
\end{code}
%<*substfrom>
\begin{code}
  Substitution-from : MetaContext → Set
  Substitution-from Γ = Σ MetaContext (λ Δ → (Γ ⟶ Δ))
\end{code}
%</substfrom>
\begin{code}

  wk-out : ∀ {x}{Γ : MetaContext} → Substitution-from Γ → Substitution-from (x ∷ Γ)
  wk-out {x}(Δ , σ) = x ∷ Δ , Flexible (here _) A.id , wk-subst x σ

-- outputs a substitution Γ → Γ[M : m ↦ P : p] by mapping M :m to the term P(f), where f : p → m
  replace-mvar : ∀ {Γ}{m} → m ∈ Γ → ∀ {p} → p A.⇒ m → Σ _ (λ Δ → p ∈ Δ × Γ ⟶ Δ)
  replace-mvar (here Γ) {p} f = (p ∷ Γ) , ((here _) , ((Flexible (here _) f) , S.wk-id p))
  replace-mvar (there {x = x} M) p₂ with replace-mvar M p₂
  ... | Δ , p∈ , σ = x ∷ Δ , there p∈ , Flexible (here _) A.id , wk-subst x σ

-- -- outputs a substitution m ∷ Γ → Γ[M' : m' ↦ P : p] using the pullback of m → a ← m'
  replace-mvar-cons : (Γ : MetaContext) → ∀ {m m' a} → m' ∈ Γ → m ⇒ a → m' ⇒ a
       → Substitution-from (m ∷ Γ)
  replace-mvar-cons Γ M' f f' =
     let module Pbk = Pullback (pullbacks f f') in
     let Δ , P , σ = replace-mvar M' Pbk.p₂ in
      Δ , Flexible P Pbk.p₁ , σ

-- unification of two metavariables
  unify-flex-flex : ∀ {Γ m m' a} → m ∈ Γ → m' ∈ Γ
      → m ⇒ a → m' ⇒ a → Substitution-from Γ

  unify-flex-flex (here Γ) (here _) f f' with equalizers f f'
  ... | record { obj = m'' ; arr = f'' } = (m'' ∷ Γ) , (Flexible (here _) f'') , (S.wk-id m'')

  unify-flex-flex (here Γ) (there M') f f' = replace-mvar-cons Γ M' f f'
  unify-flex-flex (there M) (here Γ) f f' = replace-mvar-cons Γ M f' f
  unify-flex-flex (there {x = x}{xs = Γ} M) (there M') f f' =
      wk-out (unify-flex-flex M M' f f')

{- ----------------------

Non cyclic unification

-------------------------- -}
  unify-no-cycle : ∀ {Γ}{n} → Tm Γ n
      → ∀ {m} → m ⇒ n → Maybe (Substitution-from (m ∷ Γ))

  unify-no-cycle (App t u) f = do
            Δ₁ , t' , σ₁ ← unify-no-cycle t f
            Δ₂ , u' , σ₂ ← unify-no-cycle (u [ σ₁ ]t) f
            just (Δ₂ , App (t' [ σ₂ ]t) u' , (σ₁ [ σ₂ ]s))
  unify-no-cycle (Lam t) f = do
            Δ , t' , σ ← unify-no-cycle t (wk-⇒ f)
            just (Δ , Lam t' , σ)
  unify-no-cycle {Γ} (Var x) f = do
         Pre x' ←  x ｛ f ｝⁻¹
         just (Γ , Var x' , S.id)

  unify-no-cycle (Flexible M x) f =
      let module Pbk = Pullback (pullbacks x f) in
      let Δ , P , σ = replace-mvar M Pbk.p₁ in
      just (Δ , Flexible P Pbk.p₂ , σ)

{- ----------------------

Unification

-------------------------- -}
  transition-unify-no-cycle : ∀ {Γ}{n}
     → Tm Γ n → ∀ {m} → m ∈ Γ → m A.⇒ n → Maybe (Substitution-from Γ)

  transition-unify-no-cycle t M f = do
      t' ← occur-check M t
      Δ , u , σ ← unify-no-cycle t' f
      just (Δ , M ↦ u , σ)


\end{code}
%<*unifyprototype>
\begin{code}
  unify : ∀ {Γ}{n} → Tm Γ n → Tm Γ n → Maybe (Substitution-from Γ)
\end{code}
%</unifyprototype>
\begin{code}
  unify (Flexible M f) t = transition-unify-no-cycle t M f
  unify t (Flexible M f) = transition-unify-no-cycle t M f
  unify (App t u) (App t' u') = do
           Δ₁ , σ₁ ← unify t t'
           Δ₂ , σ₂ ← unify (u [ σ₁ ]t) (u' [ σ₁ ]t)
           just (Δ₂ , σ₁ [ σ₂ ]s)
  unify (Lam t) (Lam t') = unify t t'
  unify {Γ}(Var x) (Var x') with x Fin.≟ x'
  ... | false because _ = nothing
  ... | true because _ = just (Γ , S.id)
  unify _ _ = nothing
\end{code}
