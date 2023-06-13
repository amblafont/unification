\begin{code}
{-# OPTIONS --type-in-type --no-termination-check #-}
module main where

open import Agda.Builtin.Unit
open import Agda.Builtin.Maybe
open import Agda.Builtin.Bool renaming (Bool to 𝔹)
open import Data.Nat using (ℕ; _≟_)
open import Relation.Nullary
open import Data.List as List hiding (map)
open import Data.Vec.Base as Vec using (Vec; []; _∷_)
open import Data.Product using (_,_; Σ; _×_)

open import Relation.Binary using (Rel; IsEquivalence; Setoid)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

data _∈_ {A : Set} (a : A) : List A → Set where
  here  : ∀ xs   → a ∈ (a ∷ xs)
  there : ∀ {x xs}  → a ∈ xs → a ∈ (x ∷ xs)

_without_ : ∀ {A}(l : List A){a}(a∈ : a ∈ l) → List A
.(_ ∷ _) without (here l) = l
.(_ ∷ _) without (there {x = x}{xs = l} a∈) = x ∷ l without a∈

restricts∈ : ∀ {A}(l : List A) {a}(t : a ∈ l){a'}(t' : a' ∈ l) → Maybe (a' ∈ (l without t))
restricts∈ {A} .(_ ∷ _) (here px) (here px₁) = nothing
restricts∈ {A} .(_ ∷ _) (here px) (there t') = just t'
restricts∈ {A} .(_ ∷ _) (there t) (here px) = just (here _)
restricts∈ {A} .(_ ∷ _) (there t) (there t') with restricts∈ _ t t'
... | nothing = nothing
... | just i = just (there i)

module VecList where

  -- VecList.t B [l₀ ; .. ; lₙ] ≃ B l₀ × .. × B lₙ
  t : ∀ {A : Set}(B : A → Set)(l : List A)  → Set
  t B [] = ⊤
  t B (x ∷ l) = B x × t B l


  map : ∀ {A : Set}{B B' : A → Set}{l : List A} → (∀ a → B a → B' a) → t B l → t B' l
  map {A} {B} {B'}  {[]} f xs = tt
  map {A} {B} {B'}  {a ∷ l} f (x , xs) = f a x  , map f xs


  nth : ∀ {A : Set}{B : A → Set}{l : List A}{a} → a ∈ l → t B l →  B a
  nth {l = .(_ ∷ xs)} (here xs) (t , _) = t
  nth {l = .(_ ∷ _)} (there a∈) (t , ts) = nth a∈ ts



-- Taken from the agda-category library, removing all the properties

\end{code}
%<*category>
\begin{code}
record Category : Set where
  eta-equality
  infix  4 _⇒_
  infixr 9 _∘_

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
    {obj} : Obj
    arr   : obj ⇒ A
 record Pullback (f : X ⇒ Z) (g : Y ⇒ Z) : Set where
  field
    {P} : Obj
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
     _❴_❵  : ∀ {n}{a} → O n a → ∀ {b} (f : a A.⇒ b) → O n b
     _^_ : ∀ {a}{b}(f : a A.⇒ b){n}(o : O n a) → (α o) V.⇒ (α (o ❴ f ❵ ))

\end{code}
%</signature>
%<*friendlysignature>
\begin{code}
record FriendlySignature : Set where
   field
     BaseSignature : Signature
   open Signature BaseSignature
   field
     𝓐-equalizers : ∀ {a b}(f g : a A.⇒ b) → Equalizer 𝓐 f g
     𝓐-pullbacks  : ∀ {a b c}(f : a A.⇒ b) (g : c A.⇒ b)→ Pullback 𝓐 f g
     _≟O_ : ∀ {n}{a}(o o' : O n a) → Dec (o ≡ o')
     _❴_❵⁻¹ : ∀ {n}{a}(o : O n a) → ∀ {b}(f : b A.⇒ a) → Maybe (Σ (O n b) (λ o' →  o' ❴ f ❵ ≡ o))


\end{code}
%</friendlysignature>
\begin{code}
module Term (S : Signature) where
   open Signature S

\end{code}
%<*syntax>
\begin{code}
   MetaContext : Set
   MetaContext = List A.Obj

   VecTerm : MetaContext → ∀{n}(v : Vec A.Obj n) → Set

   data Term (Γ : MetaContext) (a : A.Obj) : Set where
     Rigid : ∀ {n} (o : O n a) → VecTerm Γ (α o) → Term Γ a
     Flexible : ∀ {m} (M : m ∈ Γ)(f : m A.⇒ a) → Term Γ a


   VecTerm Γ as = VecList.t (Term Γ) (Vec.toList as)
\end{code}
%</syntax>
\begin{code}



{- ----------------------

Renaming

-------------------------- -}
   _⟦_⟧ : ∀ {Γ}{a}{b} → Term Γ a → a A.⇒ b → Term Γ b
   _⟦_⟧s : ∀ {Γ}{n}{as : Vec _ n}{as' : Vec _ n} → VecTerm Γ as
         → as V.⇒ as' → VecTerm Γ as'

   _⟦_⟧ (Rigid o x) f = Rigid (o ❴ f ❵) (x ⟦ f ^ o ⟧s)
   _⟦_⟧ (Flexible M g) f = Flexible M (f A.∘ g)

   -- there is a way to design a map combinator (generalising VecList.map) to factor those two branches
   -- but I don't think it is worth the additional complexity 
   _⟦_⟧s {as = []} {[]} ts fs = tt
   _⟦_⟧s {as = a ∷ as} {a' ∷ as'} (t , ts) (f , fs) = (t ⟦ f ⟧) , (ts ⟦ fs ⟧s)

{- ----------------------

MetaSubstitution

-------------------------- -}
   substitution : MetaContext → MetaContext → Set
   substitution Γ Δ = VecList.t (Term Δ) Γ

   _[_]t : ∀ {Γ}{a}(t : Term Γ a){Δ}(σ : substitution Γ Δ) → Term Δ a

   _[_]ts : ∀ {Γ}{n}{as : Vec A.Obj n}(ts : VecTerm Γ as){Δ}(σ : substitution Γ Δ) → VecTerm Δ as
   _[_]ts {Γ}{as}ts {Δ}σ = VecList.map (λ a' t → t [ σ ]t ) ts

   _[_]t {Γ} {a} (Rigid o x) {Δ} σ = Rigid o (x [ σ ]ts)
   _[_]t {Γ} {a} (Flexible M f) {Δ} σ = VecList.nth M σ ⟦ f ⟧ 

   subst-extend : ∀ {Γ}{Δ} → ∀ {m}(m∈ : m ∈ Γ)(t : Term Δ m) → substitution (Γ without m∈) Δ → substitution Γ Δ
   subst-extend {.(m ∷ _)} {Δ} {m} (here _) t σ = t , σ
   subst-extend {.(_ ∷ _)} {Δ} {m} (there m∈) t (u , σ) = u , (subst-extend m∈ t σ)

{- ----------------------

Weakening

-------------------------- -}
   wk-tm : ∀ {Γ}{a} m → Term Γ a → Term (m ∷ Γ) a

   wk-tm {Γ} {a} m (Rigid o x) = Rigid o (VecList.map (λ b → wk-tm m) x)
   wk-tm {Γ} {a} m (Flexible M f) = Flexible (there M) f


   wk-subst : ∀{Γ Δ} m → substitution Γ Δ → substitution Γ (m ∷ Δ)
   wk-subst m σ = VecList.map (λ x → wk-tm m) σ


{- ----------------------

The category of metavariable contexts and substitutions

-------------------------- -}
   id-subst : (Γ : MetaContext) → substitution Γ Γ
 
   wk-id : (Γ : MetaContext) → (m : A.Obj) → substitution Γ (m ∷ Γ)
   wk-id Γ m = wk-subst m (id-subst Γ)
 
   id-subst [] = tt
   id-subst (m ∷ Γ) = (Flexible (here _) A.id) , wk-id Γ m
 
   SubstitutionCategory : Category
   SubstitutionCategory = record
      { Obj = MetaContext ;
        _⇒_ = substitution ;
        id = id-subst _ ;
        _∘_ = λ σ δ → VecList.map (λ a t → t [ σ ]t) δ }

module _ (Sig : FriendlySignature) where
  open FriendlySignature Sig
  open Signature BaseSignature
  open Term BaseSignature
  module S = Category SubstitutionCategory

{- ----------------------

Occur check

-------------------------- -}

  occur-check : ∀ {Γ}{m}(m∈ : m ∈ Γ) {a} → Term Γ a
        → Maybe (Term (Γ without m∈) a)
  occur-check-Vec : ∀ {Γ}{m}(m∈ : m ∈ Γ){as} → VecList.t (Term Γ) as →
                                    Maybe (VecList.t (Term (Γ without m∈)) as)
  occur-check-Vec {Γ} {m} M {[]} l = just tt
  occur-check-Vec {Γ} {m} M {a ∷ as} (t , ts) with occur-check-Vec M ts | occur-check M t
  ... | nothing | _ = nothing
  ... | just _ | nothing = nothing
  ... | just ts' | just t' = just (t' , ts')
  occur-check {Γ} {m} M {a} (Rigid o ts) with occur-check-Vec M ts
  ... | nothing = nothing
  ... | just ts' = just (Rigid o ts')
  occur-check {Γ} {m} M {a} (Flexible M' f) with restricts∈ Γ M M'
  ... | nothing = nothing
  ... | just i = just (Flexible i f)

{- ----------------------

Unification of two metavariables

-------------------------- -}
  Substitution-from : MetaContext → Set
  Substitution-from Γ = Σ _ (substitution Γ)

  Substitution-from-Vec : MetaContext → ∀{n} → Vec A.Obj n → Set
  Substitution-from-Vec Γ as = Maybe (Σ MetaContext (λ Δ → VecTerm Δ as × substitution Γ Δ))

  wk-out : ∀ {x}{Γ : MetaContext} → Substitution-from Γ → Substitution-from (x ∷ Γ)
  wk-out {x}(Δ , σ) = x ∷ Δ , (Flexible (here _) A.id) , wk-subst x σ

-- outputs a substitution Γ → Γ[M : m ↦ P : p] by mapping M :m to the term P(f), where f : p → m
  replace-mvar : (Γ : MetaContext) → ∀ {p m} → m ∈ Γ → p A.⇒ m → Σ _ (λ Δ → p ∈ Δ × substitution Γ Δ)
  replace-mvar .(_ ∷ _) {p} {m} (here Γ) f = (p ∷ Γ) , ((here _) , ((Flexible (here _) f) , wk-id Γ p))
  replace-mvar .(_ ∷ _) {p} {m} (there {x = x}{xs = Γ} m∈) p₂ with replace-mvar Γ m∈ p₂
  ... | Δ , (p∈ , σ) = (x ∷ Δ) , ((there p∈) , ((Flexible (here _) A.id) , wk-subst x σ))

-- outputs a substitution m ∷ Γ → Γ[M' : m' ↦ P : p] using the pullback of m → a ← m'
  replace-mvar-cons : (Γ : MetaContext) → ∀ {m m' a} → m' ∈ Γ → m A.⇒ a → m' A.⇒ a
       → Substitution-from (m ∷ Γ)
  replace-mvar-cons Γ {m}{m'}{a} m'∈ f f' with 𝓐-pullbacks f f'
  ... | record { P = P ; p₁ = p₁ ; p₂ = p₂ } with replace-mvar Γ m'∈ p₂
  ... | Δ , (P∈ , σ) =  Δ , (Flexible P∈ p₁) , σ

-- unification of two metavariables
  unify-flex-flex : (Γ : MetaContext) → ∀ {m m' a} → m ∈ Γ → m' ∈ Γ
      → m A.⇒ a → m' A.⇒ a → Substitution-from Γ

  unify-flex-flex .(m ∷ _) {m} {.m} (here Γ) (here _) f f' with 𝓐-equalizers f f'
  ... | record { obj = m'' ; arr = f'' } = (m'' ∷ Γ) , (Flexible (here _) f'') , (wk-id Γ m'')

  unify-flex-flex .(_ ∷ _) {m} {m'} {a} (here Γ) (there M') f f' = replace-mvar-cons Γ M' f f'
  unify-flex-flex .(_ ∷ _) {m} {m'} {a} (there M) (here Γ) f f' = replace-mvar-cons Γ M f' f
  unify-flex-flex .(_ ∷ _) {m} {m'} (there {x = x}{xs = Γ} M) (there M') f f' =
      wk-out (unify-flex-flex Γ M M' f f')


{- ----------------------

Non cyclic unification

-------------------------- -}
  unify-no-cycle : {Γ : MetaContext} → {a : A.Obj} → (t : Term Γ a)
      → ∀ {m} → m A.⇒ a → Maybe (Substitution-from (m ∷ Γ))
  unify-no-cycle-Vec : {Γ : MetaContext} → {n : ℕ} → ∀{as}{ms} → ∀ (t : VecTerm Γ {n} as) →
     ms V.⇒ as → Substitution-from-Vec Γ ms

  unify-no-cycle {Γ} {a} (Rigid {n = n}o ts) {m} f with o ❴ f ❵⁻¹
  ... | nothing = nothing
  ... | just (o' , ≡.refl) with unify-no-cycle-Vec {as = α o} ts (f ^ o')
  ... | nothing = nothing
  ... | just (Δ , us , σ) = just (Δ , (Rigid o' us) , σ)

  unify-no-cycle {Γ} {a} (Flexible {m = m} M x) {m'} f with 𝓐-pullbacks x f
  ... | record { P = P ; p₁ = p₁ ; p₂ = p₂ } with replace-mvar Γ M p₁
  ... | Δ , (inP , σ) = just (Δ , ((Flexible inP p₂) , σ))

  unify-no-cycle-Vec {Γ} {.ℕ.zero} {[]} {[]} ts xs = just (Γ , tt , id-subst Γ)
  unify-no-cycle-Vec {Γ} {.(ℕ.suc _)} {a ∷ as} {m ∷ ms} (t , ts) (x , xs) with unify-no-cycle t x
  ... | nothing = nothing
  ... | just (Δ₁ , u₁ , σ₁) with unify-no-cycle-Vec (ts [ σ₁ ]ts) xs
  ... | just (Δ₂ , us , σ₂) = just (Δ₂ , (((u₁ [ σ₂ ]t) , us) , (σ₂ S.∘ σ₁)))
  ... | nothing = nothing

{- ----------------------

Unification

-------------------------- -}
  transition-unify-no-cycle : {Γ : MetaContext} → {a : A.Obj}
     → Term Γ a → ∀ {m} → m ∈ Γ → m A.⇒ a → Maybe (Substitution-from Γ)

  transition-unify-no-cycle {Γ}{a} t {m} m∈ f with occur-check m∈ t
  ... | nothing = nothing
  ... | just t' with unify-no-cycle t' f
  ... | nothing = nothing
  ... | just (Δ , u , σ) = just (Δ , subst-extend m∈ u σ)


  unify : {Γ : MetaContext} → {a : A.Obj} → ∀ (t u : Term Γ a) → Maybe (Substitution-from Γ)
  unify-Vec : {Γ : MetaContext} → {n : ℕ} → ∀{as} → ∀ (t u : VecTerm Γ {n} as) → Maybe (Substitution-from Γ)

  unify-Vec {Γ} {.ℕ.zero} {[]} t u = just (Γ , S.id)
  unify-Vec {Γ} {.(ℕ.suc _)} {a ∷ as} (t , ts) (u , us) with unify t u
  ... | nothing = nothing
  ... | just (Δ , σ) with unify-Vec {Δ} (ts [ σ ]ts) (us [ σ ]ts)
  ... | just (Δ' , σ') = just (Δ' , (σ' S.∘ σ ))
  ... | nothing = nothing


-- equivalence between Kleisli et category of pointed sets (implementation vs proof)
  unify {Γ} {a} (Rigid {n = n} o x) (Rigid {n = n'} o' x') with n ≟ n'
  ... | .false because ofⁿ ¬p = nothing
  ... | .true because ofʸ ≡.refl with o ≟O o'
  ... | .false because ofⁿ ¬p = nothing
  ... | .true because ofʸ ≡.refl = unify-Vec x x'
  unify {Γ} {a} (Rigid o x) (Flexible m∈ f) = transition-unify-no-cycle (Rigid o x) m∈ f
  unify {Γ} {a} (Flexible m∈ f) (Rigid o x) = transition-unify-no-cycle (Rigid o x) m∈ f
  unify {Γ} {a} (Flexible m∈ f) (Flexible m'∈ f') = just (unify-flex-flex Γ m∈ m'∈ f f')

\end{code}
