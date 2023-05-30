{-# OPTIONS --type-in-type --no-termination-check #-}
module main where


open import Agda.Builtin.Unit
open import Data.Empty renaming (⊥ to Empty)
open import Agda.Builtin.Maybe
open import Agda.Builtin.Bool renaming (Bool to 𝔹)
open import Data.Nat using (ℕ; _≟_)
open import Data.Bool using (_∨_)
open import Relation.Nullary
open import Data.List.Relation.Unary.Any
open import Data.List as List
-- open import Data.List.Membership.Propositional
open import Data.Vec.Base as Vec using (Vec; []; _∷_)
open import Data.Product using (_,_; Σ; _×_)

-- Taken from the agda-category library, removing all the lemmas
open import Level
open import Function.Base using (flip)

open import Relation.Binary using (Rel; IsEquivalence; Setoid)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
import Relation.Binary.Reasoning.Setoid as SetoidR


VecList : ∀ {A : Set}(B : A → Set)(l : List A)  → Set
VecList B [] = ⊤
VecList B (x ∷ l) = B x × VecList B l


VecListMap : ∀ {A : Set}{B B' : A → Set}{l : List A} → (∀ a → B a → B' a) → VecList B l → VecList B' l
VecListMap {A} {B} {B'}  {[]} f xs = tt
VecListMap {A} {B} {B'}  {a ∷ l} f (x , xs) = f a x  , VecListMap f xs

data _∈_ {l : Level.Level}{A : Set l} (a : A) : List A → Set l where
  here  : ∀ xs   → a ∈ (a ∷ xs)
  there : ∀ {x xs}  → a ∈ xs → a ∈ (x ∷ xs)


VecListNth : ∀ {A : Set}{B : A → Set}{l : List A}{a} → a ∈ l → VecList B l →  B a
VecListNth {l = .(_ ∷ xs)} (here xs) (t , _) = t
VecListNth {l = .(_ ∷ _)} (there a∈) (t , ts) = VecListNth a∈ ts

remove-∈ : ∀ {A}(l : List A){a}(a∈ : a ∈ l) → List A
remove-∈ .(_ ∷ _) (here l) = l
remove-∈ .(_ ∷ _) (there {x = x}{xs = l} a∈) = x ∷ remove-∈ l a∈

eq2-∈ : ∀ {A}(l : List A) {a}(t : a ∈ l){a'}(t' : a' ∈ l) → Maybe (a' ∈ remove-∈ l t)
eq2-∈ {A} .(_ ∷ _) (here px) (here px₁) = nothing
eq2-∈ {A} .(_ ∷ _) (here px) (there t') = just t'
eq2-∈ {A} .(_ ∷ _) (there t) (here px) = just (here _)
eq2-∈ {A} .(_ ∷ _) (there t) (there t') with eq2-∈ _ t t'
... | nothing = nothing
... | just i = just (there i)

-- Basic definition of a |Category| with a Hom setoid.
-- Taken from the agda category library, removing properties
record Category (ℓₒ ℓ : Level) : Set (suc (ℓₒ ⊔ ℓ)) where
  eta-equality
  infix  4 _⇒_
  infixr 9 _∘_

  field
    Obj : Set ℓₒ
    _⇒_ : Rel Obj ℓ
    -- _≈_ : ∀ {A B} → Rel (A ⇒ B) e

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
     -- Of : ∀ n → ∀ {a a'} (f : Category._⇒_ 𝓐 a a') → O n a → O n a'
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


  data MetaContext⊥ : Set where
    Some : MetaContext → MetaContext⊥
    ⊥ : MetaContext⊥
  -- MetaContext⊥ = Maybe MetaContext

  VariableContext : Set
  VariableContext = A.Obj

  VecSyntax : MetaContext → ∀{n}(v : Vec VariableContext n) → Set

  data Syntax (Γ : MetaContext) (a : VariableContext) : Set where
    Rigid : ∀ {n} (o : O n a) → VecSyntax Γ (α o) → Syntax Γ a
    Flexible : ∀ {m} (M : m ∈ Γ)(f : m A.⇒ a) → Syntax Γ a

  Syntax⊥ : MetaContext⊥ → VariableContext → Set
  Syntax⊥ (Some Γ) a = Syntax Γ a
  Syntax⊥ ⊥ a = ⊤

  VecSyntax Γ as = VecList (Syntax Γ) (Vec.toList as)

  VecSyntax⊥ : MetaContext⊥ → ∀{n} → Vec A.Obj n → Set
  VecSyntax⊥ (Some Γ) as = VecSyntax Γ as
  VecSyntax⊥ ⊥ as = ⊤

  substitution : MetaContext → MetaContext → Set
  substitution Γ Δ = VecList (Syntax Δ) Γ

  wk-tm : ∀ {Γ}{a} m → Syntax Γ a → Syntax (m ∷ Γ) a

  wk-tm {Γ} {a} m (Rigid o x) = Rigid o ( VecListMap (λ b → wk-tm m) x)
  wk-tm {Γ} {a} m (Flexible M f) = Flexible (there M) f


  wk-subst-gen : ∀{Γ Δ} m → substitution Γ Δ → substitution Γ (m ∷ Δ)
  wk-subst-gen m σ = VecListMap (λ x → wk-tm m) σ


  id-subst : (Γ : MetaContext) → substitution Γ Γ

  wk-subst : (Γ : MetaContext) → (m : A.Obj) → substitution Γ (m ∷ Γ)
  wk-subst Γ m = wk-subst-gen m (id-subst Γ)

  id-subst [] = tt
  id-subst (m ∷ Γ) = (Flexible (here _) A.id) , wk-subst Γ m

  _⟦_⟧ : ∀ {Γ}{a}(t : Syntax Γ a){b}(f : a A.⇒ b) → Syntax Γ b
  _⟦_⟧s : ∀ {Γ}{n}{as : Vec _ n}{as' : Vec _ n}(ts : VecSyntax Γ as)(fs : as V.⇒ as') → VecSyntax Γ as'

  _⟦_⟧ {Γ} {a} (Rigid o x) {b} f = Rigid (o 〚 f 〛) (x ⟦ αf o f ⟧s) 
  _⟦_⟧ {Γ} {a} (Flexible M g) {b} f = Flexible M (f A.∘ g) 

  -- there is a way to design a map combinator (generalising VecListMap) to factor those two branches
  -- but I don't think it is worth the additional complexity 
  _⟦_⟧s {as = []} {[]} ts fs = tt
  _⟦_⟧s {as = a ∷ as} {a' ∷ as'} (t , ts) (f , fs) = (t ⟦ f ⟧) , (ts ⟦ fs ⟧s)

  _[_]t : ∀ {Γ}{a}(t : Syntax Γ a){Δ}(σ : substitution Γ Δ) → Syntax Δ a

  _[_]ts : ∀ {Γ}{n}{as : Vec VariableContext n}(ts : VecSyntax Γ as){Δ}(σ : substitution Γ Δ) → VecSyntax Δ as
  _[_]ts {Γ}{as}ts {Δ}σ = VecListMap (λ a' t → t [ σ ]t ) ts

  _[_]t {Γ} {a} (Rigid o x) {Δ} σ = Rigid o (x [ σ ]ts)
  _[_]t {Γ} {a} (Flexible M f) {Δ} σ = VecListNth M σ ⟦ f ⟧ 



  substitution-⊥ : MetaContext → MetaContext⊥ → Set
  substitution-⊥ Γ ⊥ = ⊤
  substitution-⊥ Γ (Some Δ) = substitution Γ Δ

  _∘σ_ : ∀ {Γ₁ Γ₂ Γ₃} (σ : substitution Γ₁ Γ₂)(δ : substitution-⊥ Γ₂ Γ₃) → substitution-⊥ Γ₁ Γ₃
  _∘σ_ {Γ₃ = ⊥} σ δ = tt
  _∘σ_ {Γ₃ = Some Γ₃} σ δ = VecListMap (λ a t → t [ δ ]t) σ

  outSubstitution-⊥ : MetaContext → Set
  outSubstitution-⊥ Γ = Σ _ (substitution-⊥ Γ)

  outSubstitution : MetaContext → Set
  outSubstitution Γ = Σ _ (substitution Γ)

  outPruning : MetaContext → A.Obj → Set
  outPruning Γ m = Σ MetaContext⊥ (λ Δ → Syntax⊥ Δ m × substitution-⊥ Γ Δ)

  outPrunings : MetaContext → ∀{n} → Vec A.Obj n → Set
  outPrunings Γ as = Σ MetaContext⊥ (λ Δ → VecSyntax⊥ Δ as × substitution-⊥ Γ Δ)

  out-bottomise : ∀ {Γ} → outSubstitution Γ → outSubstitution-⊥ Γ
  out-bottomise (Δ , σ) = (Some Δ , σ)

  out-⊥ : (Γ : MetaContext) → outSubstitution-⊥ Γ
  out-⊥ Γ = ⊥ , tt

  out-pruning-⊥ : (Γ : MetaContext) → (a : A.Obj) → outPruning Γ a
  out-pruning-⊥ Γ a = ⊥ , tt , tt

  out-id : (Γ : MetaContext) → outSubstitution-⊥ Γ
  out-id Γ = (Some Γ) , (id-subst Γ)


  wk-out : ∀ {x}{Γ : MetaContext} → outSubstitution Γ → outSubstitution (x ∷ Γ)
  wk-out {x}(Δ , σ) = x ∷ Δ , (Flexible (here _) A.id) , (σ ∘σ wk-subst Δ x)


  unify : {Γ : MetaContext} → {a : VariableContext} → ∀ (t u : Syntax Γ a) → outSubstitution-⊥ Γ
  prune : {Γ : MetaContext} → {a : VariableContext} → (t : Syntax Γ a) → ∀ {m} → m A.⇒ a → outPruning Γ m
  transition-prune : {Γ : MetaContext} → {a : VariableContext} → (t : Syntax Γ a) → ∀ {m} → m ∈ Γ → m A.⇒ a → outSubstitution-⊥ Γ
  unifyPbks : (Γ : MetaContext)→ ∀ {P m'} → (M' : m' ∈ Γ) → (p₂ : P A.⇒ m') → Σ _ (λ Δ → P ∈ Δ × substitution Γ Δ)
  unifyPbksTop : (Γ : MetaContext)→ ∀ {m m' a} → (M' : m' ∈ Γ) → (f : m A.⇒ a)(f' : m' A.⇒ a) → outSubstitution (m ∷ Γ)
  pruneVec : {Γ : MetaContext} → {n : ℕ} → ∀{as}{ms} → ∀ (t : VecSyntax Γ {n} as) →
     ms V.⇒ as → outPrunings Γ ms


  extend-subst2 : ∀ {Γ}{Δ} → ∀ {m}(m∈ : m ∈ Γ)(t : Syntax Δ m) → substitution (remove-∈ Γ m∈) Δ → substitution Γ Δ
  extend-subst2 {.(m ∷ _)} {Δ} {m} (here _) t σ = t , σ
  extend-subst2 {.(_ ∷ _)} {Δ} {m} (there m∈) t (u , σ) = u , (extend-subst2 m∈ t σ)

  occur-check2 : ∀ {Γ}{m}(M : m ∈ Γ) {a} → Syntax Γ a → Maybe (Syntax (remove-∈ Γ M) a)
  occur-check2Vec : ∀ {Γ}{m}(M : m ∈ Γ) {n}{as} → VecSyntax Γ {n = n} as → Maybe (VecSyntax (remove-∈ Γ M) as)
  occur-check2 {Γ} {m} M {a} (Rigid o ts) with occur-check2Vec M ts
  ... | nothing = nothing
  ... | just ts' = just (Rigid o ts')
  occur-check2 {Γ} {m} M {a} (Flexible M' f) with eq2-∈ Γ M M'
  ... | nothing = nothing
  ... | just i = just (Flexible i f)
 
  occur-check2Vec {Γ} {m} M {.ℕ.zero} {[]} ts = just tt
  occur-check2Vec {Γ} {m} M {.(ℕ.suc _)} {a ∷ as} (t , ts) with occur-check2Vec M ts | occur-check2 M t
  ... | _ | nothing = nothing
  ... | nothing | _ = nothing
  ... | just ts' | just t' = just (t' , ts')

  

  transition-prune {Γ}{a} t {m} inM f with occur-check2 inM t
  ... | nothing = out-⊥ Γ
  ... | just t' with prune t' f
  ... | ⊥ , u , σ = out-⊥ Γ
  ... | Some Δ , u , σ = Some Δ , extend-subst2 inM u σ

  prune {Γ} {a} (Rigid {n = n}o ts) {m} f with o 〚 f 〛⁻¹
  ... | nothing = out-pruning-⊥ Γ m
  ... | just (o' , ≡.refl) with pruneVec {as = α o} ts (αf o' f)
  ... | ⊥ , us , σ = out-pruning-⊥ Γ m
  ... | Some Δ , us , σ = Some Δ , (Rigid o' us) , σ

  prune {Γ} {a} (Flexible {m = m} M x) {m'} f with 𝓐-pullbacks x f
  ... | record { P = P ; p₁ = p₁ ; p₂ = p₂ } with unifyPbks Γ M p₁
  ... | Δ , (inP , σ) = (Some Δ) , ((Flexible inP p₂) , σ)

  pruneVec {Γ} {.ℕ.zero} {[]} {[]} ts xs = Some Γ , tt , id-subst Γ
  pruneVec {Γ} {.(ℕ.suc _)} {a ∷ as} {m ∷ ms} (t , ts) (x , xs) with prune t x
  ... | ⊥ , out = ⊥ , tt , tt
  ... | Some Δ₁ , u₁ , σ₁ with pruneVec (ts [ σ₁ ]ts) xs
  ... | Some Δ₂ , us , σ₂ = (Some Δ₂) , (((u₁ [ σ₂ ]t) , us) , (σ₁ ∘σ σ₂))
  ... | ⊥ , out = ⊥ , tt , tt

  unifyVec : {Γ : MetaContext} → {n : ℕ} → ∀{as} → ∀ (t u : VecSyntax Γ {n} as) → outSubstitution-⊥ Γ
  unifyVec {Γ} {.ℕ.zero} {[]} t u = out-id Γ
  unifyVec {Γ} {.(ℕ.suc _)} {a ∷ as} (t , ts) (u , us) with unify t u
  ... | ⊥ , σ = out-⊥ Γ
  ... | Some Δ , σ with unifyVec {Δ} (ts [ σ ]ts) (us [ σ ]ts)
  --                      One day I wish I understand why Agda's unification
  ... | (Δ' , σ') = Δ' , (σ ∘σ σ' )

  unifyFlexible : (Γ : MetaContext) → ∀ {m m' a} → (M : m ∈ Γ) → (M' : m' ∈ Γ) → (f : m A.⇒ a)(f' : m' A.⇒ a) → outSubstitution Γ

  unify {Γ} {a} (Rigid {n = n} o x) (Rigid {n = n'} o' x') with n ≟ n'
  ... | .false because ofⁿ ¬p = out-⊥ Γ
  ... | .true because ofʸ ≡.refl with o ≟O o'
  ... | .false because ofⁿ ¬p = out-⊥ Γ
  ... | .true because ofʸ ≡.refl = unifyVec x x'
  unify {Γ} {a} (Rigid o x) (Flexible M f) = transition-prune (Rigid o x) M f
  unify {Γ} {a} (Flexible M f) (Rigid o x) = transition-prune (Rigid o x) M f
  unify {Γ} {a} (Flexible M f) (Flexible M' f') = out-bottomise (unifyFlexible Γ M M' f f')


  unifyFlexible .(m ∷ _) {m} {.m} (here Γ) (here _) f f' with 𝓐-equalizers f f'
  ... | record { obj = m'' ; arr = f'' } = (m'' ∷ Γ) , (Flexible (here _) f'') , (wk-subst Γ m'')

  unifyFlexible .(_ ∷ _) {m} {m'} {a} (here Γ) (there M') f f' = unifyPbksTop Γ M' f f'
  unifyFlexible .(_ ∷ _) {m} {m'} {a} (there M) (here Γ) f f' = unifyPbksTop Γ M f' f
  unifyFlexible .(_ ∷ _) {m} {m'} (there {x = x}{xs = Γ} M) (there M') f f' =  wk-out (unifyFlexible Γ M M' f f') 


  unifyPbksTop Γ {m}{m'}{a} M' f f' with 𝓐-pullbacks f f'
  ... | record { P = P ; p₁ = p₁ ; p₂ = p₂ } with unifyPbks Γ M' p₂
  ... | Δ , (inP , σ) =  Δ , (Flexible inP p₁) , σ

  unifyPbks .(_ ∷ _) {P} {m'} (here Γ) p₂ = (P ∷ Γ) , ((here _) , ((Flexible (here _) p₂) , wk-subst Γ P))
  unifyPbks .(_ ∷ _) {P} {m'} (there {x = x}{xs = Γ} M') p₂ with unifyPbks Γ M' p₂
  ... | Δ , (inP , σ) = (x ∷ Δ) , ((there inP) , ((Flexible (here _) A.id) , (σ ∘σ wk-subst Δ x)))


