{-# OPTIONS --type-in-type --no-termination-check #-}
module main where

open import Agda.Builtin.Unit
open import Data.Empty renaming (⊥ to Empty)
open import Agda.Builtin.Maybe
open import Agda.Builtin.Bool renaming (Bool to 𝔹)
open import Data.Nat using (ℕ; _≟_)
open import Data.Bool using (_∨_)
open import Relation.Nullary
open import Data.List as List hiding (map)
open import Data.Vec.Base as Vec using (Vec; []; _∷_)
open import Data.Product using (_,_; Σ; _×_)

open import Level

open import Relation.Binary using (Rel; IsEquivalence; Setoid)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
import Relation.Binary.Reasoning.Setoid as SetoidR

data _∈_ {l : Level.Level}{A : Set l} (a : A) : List A → Set l where
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

  -- VecList.t B [l₀, .. , lₙ] is the type B l₀ × .. × B lₙ
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
-- Basic definition of a |Category| with a Hom setoid.
record Category (ℓₒ ℓ : Level) : Set (suc (ℓₒ ⊔ ℓ)) where
  eta-equality
  infix  4 _⇒_
  infixr 9 _∘_

  field
    Obj : Set ℓₒ
    _⇒_ : Rel Obj ℓ

    id  : ∀ {A} → (A ⇒ A)
    _∘_ : ∀ {A B C} → (B ⇒ C) → (A ⇒ B) → (A ⇒ C)


module _ {o ℓ : Level}(𝓐 : Category o ℓ) where

 open Category 𝓐
 private
  variable
    A B X Y Z : Obj

 record Equalizer (f g : A ⇒ B) : Set (o ⊔ ℓ) where
  field
    {obj} : Obj
    arr   : obj ⇒ A
 record Pullback (f : X ⇒ Z) (g : Y ⇒ Z) : Set (o ⊔ ℓ) where
  field
    {P} : Obj
    p₁  : P ⇒ X
    p₂  : P ⇒ Y

module VecMor {ℓₒ ℓ : Level}(𝓐 : Category ℓₒ ℓ) where
  private
     module A = Category 𝓐
  _⇒_ : ∀ {n} → Vec A.Obj n → Vec A.Obj n → Set
  [] ⇒ [] = ⊤
  (x ∷ v) ⇒ (x' ∷ v') = x A.⇒ x' × v ⇒ v'

record Signature (ℓₒ ℓ : Level) : Set where
   open Category
   field
     𝓐 : Category ℓₒ ℓ
   private
     module A = Category 𝓐
     module V = VecMor 𝓐
   field
     𝓐-equalizers : ∀ {a b}(f g : a A.⇒ b) → Equalizer 𝓐 f g
     𝓐-pullbacks  : ∀ {a b c}(f : a A.⇒ b) (g : c A.⇒ b)→ Pullback 𝓐 f g
     O : ℕ → A.Obj → Set
     _≟O_ : ∀ {n}{a}(o o' : O n a) → Dec (o ≡ o')
     α : ∀ {n a } → (o : O n a) → Vec A.Obj n
     _〚_〛  : ∀ {n}{a} → O n a → ∀ {b} (f : a A.⇒ b) → O n b
     αf : ∀ {n}{a} (o : O n a) → ∀ {b}(f : a A.⇒ b) → (α o) V.⇒ (α (o 〚 f 〛 ))
     _〚_〛⁻¹ : ∀ {n}{a}(o : O n a) → ∀ {b}(f : b A.⇒ a) → Maybe (Σ (O n b) (λ o' →  o' 〚 f 〛 ≡ o))


module _ {ℓₒ ℓ : Level}(S : Signature ℓₒ ℓ) where
  open Signature S
  private
    module A = Category 𝓐
    module V = VecMor 𝓐

  MetaContext : Set
  MetaContext = List A.Obj

  VariableContext : Set
  VariableContext = A.Obj

  VecSyntax : MetaContext → ∀{n}(v : Vec VariableContext n) → Set

  data Syntax (Γ : MetaContext) (a : VariableContext) : Set where
    Rigid : ∀ {n} (o : O n a) → VecSyntax Γ (α o) → Syntax Γ a
    Flexible : ∀ {m} (M : m ∈ Γ)(f : m A.⇒ a) → Syntax Γ a


  VecSyntax Γ as = VecList.t (Syntax Γ) (Vec.toList as)



{- ----------------------

Renaming

-------------------------- -}
  _⟦_⟧ : ∀ {Γ}{a}(t : Syntax Γ a){b}(f : a A.⇒ b) → Syntax Γ b
  _⟦_⟧s : ∀ {Γ}{n}{as : Vec _ n}{as' : Vec _ n}(ts : VecSyntax Γ as)(fs : as V.⇒ as') → VecSyntax Γ as'

  _⟦_⟧ {Γ} {a} (Rigid o x) {b} f = Rigid (o 〚 f 〛) (x ⟦ αf o f ⟧s) 
  _⟦_⟧ {Γ} {a} (Flexible M g) {b} f = Flexible M (f A.∘ g) 

  -- there is a way to design a map combinator (generalising VecListMap) to factor those two branches
  -- but I don't think it is worth the additional complexity 
  _⟦_⟧s {as = []} {[]} ts fs = tt
  _⟦_⟧s {as = a ∷ as} {a' ∷ as'} (t , ts) (f , fs) = (t ⟦ f ⟧) , (ts ⟦ fs ⟧s)

{- ----------------------

Substitution

-------------------------- -}
  substitution : MetaContext → MetaContext → Set
  substitution Γ Δ = VecList.t (Syntax Δ) Γ

  _[_]t : ∀ {Γ}{a}(t : Syntax Γ a){Δ}(σ : substitution Γ Δ) → Syntax Δ a

  _[_]ts : ∀ {Γ}{n}{as : Vec VariableContext n}(ts : VecSyntax Γ as){Δ}(σ : substitution Γ Δ) → VecSyntax Δ as
  _[_]ts {Γ}{as}ts {Δ}σ = VecList.map (λ a' t → t [ σ ]t ) ts

  _[_]t {Γ} {a} (Rigid o x) {Δ} σ = Rigid o (x [ σ ]ts)
  _[_]t {Γ} {a} (Flexible M f) {Δ} σ = VecList.nth M σ ⟦ f ⟧ 

  subst-extend : ∀ {Γ}{Δ} → ∀ {m}(m∈ : m ∈ Γ)(t : Syntax Δ m) → substitution (Γ without m∈) Δ → substitution Γ Δ
  subst-extend {.(m ∷ _)} {Δ} {m} (here _) t σ = t , σ
  subst-extend {.(_ ∷ _)} {Δ} {m} (there m∈) t (u , σ) = u , (subst-extend m∈ t σ)

{- ----------------------

Weakening

-------------------------- -}
  wk-tm : ∀ {Γ}{a} m → Syntax Γ a → Syntax (m ∷ Γ) a

  wk-tm {Γ} {a} m (Rigid o x) = Rigid o (VecList.map (λ b → wk-tm m) x)
  wk-tm {Γ} {a} m (Flexible M f) = Flexible (there M) f


  wk-subst : ∀{Γ Δ} m → substitution Γ Δ → substitution Γ (m ∷ Δ)
  wk-subst m σ = VecList.map (λ x → wk-tm m) σ


{- ----------------------

The category of substitutions

-------------------------- -}
  id-subst : (Γ : MetaContext) → substitution Γ Γ

  wk-id : (Γ : MetaContext) → (m : A.Obj) → substitution Γ (m ∷ Γ)
  wk-id Γ m = wk-subst m (id-subst Γ)

  id-subst [] = tt
  id-subst (m ∷ Γ) = (Flexible (here _) A.id) , wk-id Γ m

  SubstitutionCategory : Category zero zero
  SubstitutionCategory = record
     { Obj = MetaContext ;
       _⇒_ = substitution ;
       id = id-subst _ ;
       _∘_ = λ σ δ → VecList.map (λ a t → t [ σ ]t) δ }

  module S = Category SubstitutionCategory

{- ----------------------

Occur-check

-------------------------- -}

  occur-check : ∀ {Γ}{m}(M : m ∈ Γ) {a} → Syntax Γ a → Maybe (Syntax (Γ without M) a)
  occur-check-Vec : ∀ {Γ}{m}(M : m ∈ Γ){as} → VecList.t (Syntax Γ) as → Maybe (VecList.t (Syntax (Γ without M)) as)
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

Unification

-------------------------- -}
  Substitution-from : MetaContext → Set
  Substitution-from Γ = Σ _ (substitution Γ)

  Substitution-from-Vec : MetaContext → ∀{n} → Vec A.Obj n → Set
  Substitution-from-Vec Γ as = Maybe (Σ MetaContext (λ Δ → VecSyntax Δ as × substitution Γ Δ))

  wk-out : ∀ {x}{Γ : MetaContext} → Substitution-from Γ → Substitution-from (x ∷ Γ)
  wk-out {x}(Δ , σ) = x ∷ Δ , (Flexible (here _) A.id) , wk-subst x σ

  unifyPbks : (Γ : MetaContext) → ∀ {P m'} → (M' : m' ∈ Γ) → (p₂ : P A.⇒ m') → Σ _ (λ Δ → P ∈ Δ × substitution Γ Δ)
  unifyPbks .(_ ∷ _) {P} {m'} (here Γ) p₂ = (P ∷ Γ) , ((here _) , ((Flexible (here _) p₂) , wk-id Γ P))
  unifyPbks .(_ ∷ _) {P} {m'} (there {x = x}{xs = Γ} M') p₂ with unifyPbks Γ M' p₂
  ... | Δ , (inP , σ) = (x ∷ Δ) , ((there inP) , ((Flexible (here _) A.id) , wk-subst x σ))

  unifyPbksTop : (Γ : MetaContext)→ ∀ {m m' a} → (M' : m' ∈ Γ) → (f : m A.⇒ a)(f' : m' A.⇒ a) → Substitution-from (m ∷ Γ)
  unifyPbksTop Γ {m}{m'}{a} M' f f' with 𝓐-pullbacks f f'
  ... | record { P = P ; p₁ = p₁ ; p₂ = p₂ } with unifyPbks Γ M' p₂
  ... | Δ , (inP , σ) =  Δ , (Flexible inP p₁) , σ



  unify-flex-flex : (Γ : MetaContext) → ∀ {m m' a} → (M : m ∈ Γ) → (M' : m' ∈ Γ) → (f : m A.⇒ a)(f' : m' A.⇒ a) → Substitution-from Γ

  unify-flex-flex .(m ∷ _) {m} {.m} (here Γ) (here _) f f' with 𝓐-equalizers f f'
  ... | record { obj = m'' ; arr = f'' } = (m'' ∷ Γ) , (Flexible (here _) f'') , (wk-id Γ m'')

  unify-flex-flex .(_ ∷ _) {m} {m'} {a} (here Γ) (there M') f f' = unifyPbksTop Γ M' f f'
  unify-flex-flex .(_ ∷ _) {m} {m'} {a} (there M) (here Γ) f f' = unifyPbksTop Γ M f' f
  unify-flex-flex .(_ ∷ _) {m} {m'} (there {x = x}{xs = Γ} M) (there M') f f' = wk-out (unify-flex-flex Γ M M' f f')




  unify-no-cycle : {Γ : MetaContext} → {a : VariableContext} → (t : Syntax Γ a) → ∀ {m} → m A.⇒ a → Maybe (Substitution-from (m ∷ Γ))
  unify-no-cycle-Vec : {Γ : MetaContext} → {n : ℕ} → ∀{as}{ms} → ∀ (t : VecSyntax Γ {n} as) →
     ms V.⇒ as → Substitution-from-Vec Γ ms

  unify-no-cycle {Γ} {a} (Rigid {n = n}o ts) {m} f with o 〚 f 〛⁻¹
  ... | nothing = nothing
  ... | just (o' , ≡.refl) with unify-no-cycle-Vec {as = α o} ts (αf o' f)
  ... | nothing = nothing
  ... | just (Δ , us , σ) = just (Δ , (Rigid o' us) , σ)

  unify-no-cycle {Γ} {a} (Flexible {m = m} M x) {m'} f with 𝓐-pullbacks x f
  ... | record { P = P ; p₁ = p₁ ; p₂ = p₂ } with unifyPbks Γ M p₁
  ... | Δ , (inP , σ) = just (Δ , ((Flexible inP p₂) , σ))

  unify-no-cycle-Vec {Γ} {.ℕ.zero} {[]} {[]} ts xs = just (Γ , tt , id-subst Γ)
  unify-no-cycle-Vec {Γ} {.(ℕ.suc _)} {a ∷ as} {m ∷ ms} (t , ts) (x , xs) with unify-no-cycle t x
  ... | nothing = nothing
  ... | just (Δ₁ , u₁ , σ₁) with unify-no-cycle-Vec (ts [ σ₁ ]ts) xs
  ... | just (Δ₂ , us , σ₂) = just (Δ₂ , (((u₁ [ σ₂ ]t) , us) , (σ₂ S.∘ σ₁)))
  ... | nothing = nothing

  transition-unify-no-cycle : {Γ : MetaContext} → {a : VariableContext} → (t : Syntax Γ a) → ∀ {m} → m ∈ Γ → m A.⇒ a → Maybe (Substitution-from Γ)


  transition-unify-no-cycle {Γ}{a} t {m} inM f with occur-check inM t
  ... | nothing = nothing
  ... | just t' with unify-no-cycle t' f
  ... | nothing = nothing
  ... | just (Δ , u , σ) = just (Δ , subst-extend inM u σ)


  unify : {Γ : MetaContext} → {a : VariableContext} → ∀ (t u : Syntax Γ a) → Maybe (Substitution-from Γ)
  unify-Vec : {Γ : MetaContext} → {n : ℕ} → ∀{as} → ∀ (t u : VecSyntax Γ {n} as) → Maybe (Substitution-from Γ)

  unify-Vec {Γ} {.ℕ.zero} {[]} t u = just (Γ , S.id)
  unify-Vec {Γ} {.(ℕ.suc _)} {a ∷ as} (t , ts) (u , us) with unify t u
  ... | nothing = nothing
  ... | just (Δ , σ) with unify-Vec {Δ} (ts [ σ ]ts) (us [ σ ]ts)
  ... | just (Δ' , σ') = just (Δ' , (σ' S.∘ σ ))
  ... | nothing = nothing


  unify {Γ} {a} (Rigid {n = n} o x) (Rigid {n = n'} o' x') with n ≟ n'
  ... | .false because ofⁿ ¬p = nothing
  ... | .true because ofʸ ≡.refl with o ≟O o'
  ... | .false because ofⁿ ¬p = nothing
  ... | .true because ofʸ ≡.refl = unify-Vec x x'
  unify {Γ} {a} (Rigid o x) (Flexible M f) = transition-unify-no-cycle (Rigid o x) M f
  unify {Γ} {a} (Flexible M f) (Rigid o x) = transition-unify-no-cycle (Rigid o x) M f
  unify {Γ} {a} (Flexible M f) (Flexible M' f') = just (unify-flex-flex Γ M M' f f')
