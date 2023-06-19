\begin{code}
{-# OPTIONS --type-in-type --no-termination-check #-}
module main where

open import Agda.Builtin.Unit
open import Data.Maybe.Base
open import Agda.Builtin.Bool renaming (Bool to 𝔹)
open import Data.Nat using (ℕ; _≟_)
open import Relation.Nullary
open import Data.List as List hiding (map)
open import Data.Vec.Base as Vec using (Vec; []; _∷_)
open import Data.Product using (_,_; Σ; _×_)

open import Relation.Binary using (Rel; IsEquivalence; Setoid)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

open import lib





-- Taken from the agda-category library, removing all the properties

\end{code}
%<*category>
\begin{code}
record Category : Set where
  field
    Obj : Set
    _⇒_ : Obj → Obj → Set

    id  : ∀ {A} → (A ⇒ A)
    _∘_ : ∀ {A B C} → (B ⇒ C) → (A ⇒ B) → (A ⇒ C)
\end{code}
%</category>
\begin{code}

module _ (𝓐 : Category) where

 open Category 𝓐
 private
  variable
    A B X Y Z : Obj

 record Equalizer (f g : A ⇒ B) : Set where
  field
    obj : Obj
    arr   : obj ⇒ A
 record Pullback (f : X ⇒ Z) (g : Y ⇒ Z) : Set where
  field
    P : Obj
    p₁  : P ⇒ X
    p₂  : P ⇒ Y

module VecMor (𝓐 : Category) where
  private
     module A = Category 𝓐
  _⇒_ : ∀ {n} → Vec A.Obj n → Vec A.Obj n → Set
  [] ⇒ [] = ⊤
  (x ∷ v) ⇒ (x' ∷ v') = x A.⇒ x' × v ⇒ v'

\end{code}
%<*signature>
\begin{code}
record Signature : Set where
   field
     𝓐 : Category

   module A = Category 𝓐
   module V = VecMor 𝓐

   field
     O : ℕ → A.Obj → Set
     α : ∀ {n a } → (o : O n a) → Vec A.Obj n
     -- The last two fields account for functoriality
     _｛_｝  : ∀ {n}{a} → O n a → ∀ {b} (f : a A.⇒ b) → O n b
     _^_ : ∀ {a}{b}(f : a A.⇒ b){n}(o : O n a) → (α o) V.⇒ (α (o ｛ f ｝ ))

\end{code}
%</signature>
%<*friendlysignature>
\begin{code}
record FriendlySignature : Set where
   field
     BaseSignature : Signature
   open Signature BaseSignature
   field
     equalizers : ∀ {a b}(f g : a A.⇒ b) → Equalizer 𝓐 f g
     pullbacks  : ∀ {a b c}(f : a A.⇒ b) (g : c A.⇒ b)→ Pullback 𝓐 f g
     _≟O_ : ∀ {n}{a}(o o' : O n a) → Dec (o ≡ o')
     -- _｛_｝⁻¹ : ∀ {n}{a}(o : O n a) → ∀ {b}(f : b A.⇒ a) → Maybe (Σ (O n b) (λ o' →  o' ｛ f ｝ ≡ o))
     _｛_｝⁻¹ : ∀ {n}{a}(o : O n a) → ∀ {b}(f : b A.⇒ a) → Maybe (PreImage (_｛ f ｝) o)


\end{code}
%</friendlysignature>
\begin{code}
module Tm (S : Signature) where
   open Signature S

\end{code}
%<*syntax>
\begin{code}
   MetaContext : Set
   MetaContext = List A.Obj

   Tms : MetaContext → ∀{n}(v : Vec A.Obj n) → Set

   data Tm (Γ : MetaContext) (a : A.Obj) : Set where
     Rigid : ∀ {n} (o : O n a) → Tms Γ (α o) → Tm Γ a
     Flexible : ∀ {m} (M : m ∈ Γ)(f : m A.⇒ a) → Tm Γ a


   Tms Γ as = VecList.t (Tm Γ) (Vec.toList as)
\end{code}
%</syntax>
\begin{code}



{- ----------------------

Renaming

-------------------------- -}
   _❴_❵ : ∀ {Γ}{a}{b} → Tm Γ a → a A.⇒ b → Tm Γ b
   _❴_❵s : ∀ {Γ}{n}{as : Vec _ n}{as' : Vec _ n} → Tms Γ as
         → as V.⇒ as' → Tms Γ as'

   Rigid o x ❴ f ❵ = Rigid (o ｛ f ｝) (x ❴ f ^ o ❵s)
   Flexible M g ❴ f ❵ = Flexible M (f A.∘ g)

   -- there is a way to design a map combinator (generalising VecList.map) to factor those two branches
   -- but I don't think it is worth the additional complexity 
   _❴_❵s {as = []} {[]} ts fs = tt
   _❴_❵s {as = a ∷ as} {a' ∷ as'} (t , ts) (f , fs) = (t ❴ f ❵) , (ts ❴ fs ❵s)

{- ----------------------

MetaSubstitution

-------------------------- -}
   substitution : MetaContext → MetaContext → Set
   substitution Γ Δ = VecList.t (Tm Δ) Γ

   -- precedence below _∷_, which is 4
   infix 3 _⟶_
   _⟶_ = substitution

   _[_]t : ∀ {Γ}{a} → Tm Γ a → ∀ {Δ} → (Γ ⟶ Δ) → Tm Δ a

   _[_]ts : ∀ {Γ}{n}{as : Vec A.Obj n} → Tms Γ as → ∀ {Δ} → Γ ⟶ Δ → Tms Δ as
   ts [ σ ]ts = VecList.map (λ a' t → t [ σ ]t ) ts

   Rigid o x [ σ ]t = Rigid o (x [ σ ]ts)
   Flexible M f [ σ ]t = VecList.nth M σ ❴ f ❵ 



   _↦_,_ : ∀ {Γ}{Δ}{m} → (M : m ∈ Γ) → Tm Δ m → (Γ without M ⟶ Δ) → (Γ ⟶ Δ)
   here _ ↦ t , σ = t , σ
   there M ↦ t , (u , σ) = u , (M ↦ t , σ) 


{- ----------------------

Weakening

-------------------------- -}
   wk-Tm : ∀ {Γ}{a} m → Tm Γ a → Tm (m ∷ Γ) a

   wk-Tm m (Rigid o x) = Rigid o (VecList.map (λ b → wk-Tm m) x)
   wk-Tm m (Flexible M f) = Flexible (there M) f


   wk-subst : ∀{Γ Δ} m → (Γ ⟶ Δ) → (Γ ⟶ m ∷ Δ)
   wk-subst m σ = VecList.map (λ x → wk-Tm m) σ


{- ----------------------

The category of metavariable contexts and substitutions

-------------------------- -}
   module S where
      Obj : Set
      Obj = MetaContext

      _⇒_ : Obj → Obj → Set
      _⇒_ = substitution

      id : {Γ : MetaContext} → substitution Γ Γ

      wk-id : ∀ {Γ} m → Γ ⟶ m ∷ Γ
      wk-id m = wk-subst m id

      id {[]} = tt
      id {m ∷ Γ} = (Flexible (here _) A.id) , wk-id m

      _∘_ : ∀ {Γ₁ Γ₂ Γ₃} → (Γ₂ ⇒ Γ₃) → (Γ₁ ⇒ Γ₂) → (Γ₁ ⇒ Γ₃)
      σ ∘ δ = VecList.map (λ a t → t [ σ ]t) δ 


   SubstitutionCategory : Category
   SubstitutionCategory = record { S }

module _ (Sig : FriendlySignature) where
  open FriendlySignature Sig
  open Signature BaseSignature
  open Tm BaseSignature

{- ----------------------

Occur check

-------------------------- -}

  occur-check : ∀ {Γ}{m}(M : m ∈ Γ) {a} → Tm Γ a
        → Maybe (Tm (Γ without M) a)
  occur-check-Vec : ∀ {Γ}{m}(M : m ∈ Γ){as} → VecList.t (Tm Γ) as →
                                    Maybe (VecList.t (Tm (Γ without M)) as)
  occur-check-Vec M {[]} l = just tt
  occur-check-Vec M {a ∷ as} (t , ts) = do
       ts' ← occur-check-Vec M ts
       t' ← occur-check M t
       just (t' , ts')
  occur-check M (Rigid o ts) = do
       ts' ← occur-check-Vec M ts
       just (Rigid o ts')
  occur-check M (Flexible M' f) = do
       M'' ← restricts∈ M M'
       just (Flexible M'' f)

{- ----------------------

Unification of two metavariables

-------------------------- -}
  Substitution-from : MetaContext → Set
  Substitution-from Γ = Σ MetaContext (λ Δ → (Γ ⟶ Δ))

  Substitution-from-Vec : MetaContext → ∀{n} → Vec A.Obj n → Set
  Substitution-from-Vec Γ as = Maybe (Σ MetaContext (λ Δ → Tms Δ as × Γ ⟶ Δ))

  wk-out : ∀ {x}{Γ : MetaContext} → Substitution-from Γ → Substitution-from (x ∷ Γ)
  wk-out {x}(Δ , σ) = x ∷ Δ , Flexible (here _) A.id , wk-subst x σ

-- outputs a substitution Γ → Γ[M : m ↦ P : p] by mapping M :m to the term P(f), where f : p → m
  replace-mvar : ∀ {Γ}{m} → m ∈ Γ → ∀ {p} → p A.⇒ m → Σ _ (λ Δ → p ∈ Δ × Γ ⟶ Δ)
  replace-mvar (here Γ) {p} f = (p ∷ Γ) , ((here _) , ((Flexible (here _) f) , S.wk-id p))
  replace-mvar (there {x = x} M) p₂ with replace-mvar M p₂
  ... | Δ , p∈ , σ = x ∷ Δ , there p∈ , Flexible (here _) A.id , wk-subst x σ

-- outputs a substitution m ∷ Γ → Γ[M' : m' ↦ P : p] using the pullback of m → a ← m'
  replace-mvar-cons : (Γ : MetaContext) → ∀ {m m' a} → m' ∈ Γ → m A.⇒ a → m' A.⇒ a
       → Substitution-from (m ∷ Γ)
  replace-mvar-cons Γ M' f f' =
     let module Pbk = Pullback (pullbacks f f') in
     let Δ , P , σ = replace-mvar M' Pbk.p₂ in
      Δ , Flexible P Pbk.p₁ , σ
  -- replace-mvar-cons Γ M' f f' with pullbacks f f'
  -- ... | record { P = P ; p₁ = p₁ ; p₂ = p₂ } with replace-mvar M' p₂
  -- ... | Δ , P , σ =  Δ , Flexible P p₁ , σ

-- unification of two metavariables
  unify-flex-flex : ∀ {Γ m m' a} → m ∈ Γ → m' ∈ Γ
      → m A.⇒ a → m' A.⇒ a → Substitution-from Γ

  unify-flex-flex (here Γ) (here _) f f' with equalizers f f'
  ... | record { obj = m'' ; arr = f'' } = (m'' ∷ Γ) , (Flexible (here _) f'') , (S.wk-id m'')

  unify-flex-flex (here Γ) (there M') f f' = replace-mvar-cons Γ M' f f'
  unify-flex-flex (there M) (here Γ) f f' = replace-mvar-cons Γ M f' f
  unify-flex-flex (there {x = x}{xs = Γ} M) (there M') f f' =
      wk-out (unify-flex-flex M M' f f')


{- ----------------------

Non cyclic unification

-------------------------- -}
  unify-no-cycle : ∀ {Γ}{a} → Tm Γ a
      → ∀ {m} → m A.⇒ a → Maybe (Substitution-from (m ∷ Γ))
  unify-no-cycle-Vec : ∀ {Γ}{n} {as : Vec A.Obj n} → Tms Γ as →
     ∀ {ms} → ms V.⇒ as → Substitution-from-Vec Γ ms

  unify-no-cycle (Rigid o ts) f = do
       Pre o' ←  o ｛ f ｝⁻¹
       (Δ , us , σ) ← unify-no-cycle-Vec {as = α o} ts (f ^ o')
       just (Δ , (Rigid o' us) , σ)

  unify-no-cycle (Flexible M x) f =
      let module Pbk = Pullback (pullbacks x f) in
      let Δ , P , σ = replace-mvar M Pbk.p₁ in
      just (Δ , Flexible P Pbk.p₂ , σ)

  unify-no-cycle-Vec {Γ} {as = []} ts {[]} xs = just (Γ , tt , S.id)
  unify-no-cycle-Vec {Γ} {as = a ∷ as} (t , ts) {m ∷ ms} (x , xs) = do
      Δ₁ , u₁ , σ₁ ← unify-no-cycle t x
      Δ₂ , us , σ₂ ← unify-no-cycle-Vec (ts [ σ₁ ]ts) xs
      just (Δ₂ , (u₁ [ σ₂ ]t , us) , σ₂ S.∘ σ₁)

{- ----------------------

Unification

-------------------------- -}
  transition-unify-no-cycle : ∀ {Γ}{a}
     → Tm Γ a → ∀ {m} → m ∈ Γ → m A.⇒ a → Maybe (Substitution-from Γ)

  transition-unify-no-cycle t M f = do
      t' ← occur-check M t
      Δ , u , σ ← unify-no-cycle t' f
      just (Δ , M ↦ u , σ)


  unify : ∀ {Γ}{a} → Tm Γ a → Tm Γ a → Maybe (Substitution-from Γ)
  unify-Vec : ∀ {Γ}{n}{as : Vec A.Obj n} → Tms Γ as → Tms Γ as  → Maybe (Substitution-from Γ)

  unify-Vec {Γ} {as = []} t u = just (Γ , S.id)
  unify-Vec {as = a ∷ as} (t , ts) (u , us) = do
      Δ  , σ  ← unify t u
      Δ' , σ' ← unify-Vec (ts [ σ ]ts) (us [ σ ]ts)
      just (Δ' , σ' S.∘ σ )


-- equivalence between Kleisli et category of pointed sets (implementation vs proof)
  unify (Rigid {n = n} o x) (Rigid {n = n'} o' x') with n ≟ n'
  ... | .false because ofⁿ _ = nothing
  ... | yes ≡.refl with o ≟O o'
  ... | .false because ofⁿ _ = nothing
  ... | yes ≡.refl = unify-Vec x x'
  unify (Rigid o x) (Flexible M f) = transition-unify-no-cycle (Rigid o x) M f
  unify (Flexible M f) (Rigid o x) = transition-unify-no-cycle (Rigid o x) M f
  unify (Flexible M f) (Flexible m'∈ f') = just (unify-flex-flex M m'∈ f f')

\end{code}
