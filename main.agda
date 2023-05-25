{-# OPTIONS --type-in-type --no-termination-check #-}
module main-old where

open import Agda.Builtin.Unit
open import Data.Empty renaming (⊥ to Empty)
open import Agda.Builtin.Maybe
open import Agda.Builtin.Bool renaming (Bool to 𝔹)
open import Data.Nat using (ℕ; _≟_)
open import Data.Bool using (_∨_)
open import Relation.Nullary
open import Data.List.Relation.Unary.Any
open import Data.List as List
open import Data.List.Membership.Propositional
open import Data.Vec.Base as Vec using (Vec; []; _∷_)
open import Data.Product using (_,_; Σ; _×_)

-- Taken from the agda-category library, removing all the lemmas
open import Level
open import Function.Base using (flip)

open import Relation.Binary using (Rel; IsEquivalence; Setoid)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
import Relation.Binary.Reasoning.Setoid as SetoidR

eq-∈ : ∀ {A}(l : List A) {a}(t : a ∈ l){a'}(t : a' ∈ l) → 𝔹
eq-∈ {A} .(_ ∷ _) {a} (here px) (here px₁) = true
eq-∈ {A} .(_ ∷ _) {a} (here px) (there t') = false
eq-∈ {A} .(_ ∷ _) {a} (there t) (here px) = false
eq-∈ {A} .(_ ∷ _) {a} (there t) (there t') = eq-∈ _ t t'

-- Basic definition of a |Category| with a Hom setoid.
-- Also comes with some reasoning combinators (see HomReasoning)
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


  -- When a category is quantified, it is convenient to refer to the levels from a module,
  -- so we do not have to explicitly quantify over a category when universe levels do not
  -- play a big part in a proof (which is the case probably all the time).
  o-level : Level
  o-level = ℓₒ

  ℓ-level : Level
  ℓ-level = ℓ


  -- Reasoning combinators.  _≈⟨_⟩_ and _≈˘⟨_⟩_ from SetoidR.
  -- Also some useful combinators for doing reasoning on _∘_ chains

  op : Category ℓₒ ℓ
  op = record
    { Obj       = Obj
    ; _⇒_       = flip _⇒_
    ; _∘_       = flip _∘_
    ; id        = id
    }

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

  -- Syntax⊥ : MetaContext⊥ → VariableContext → Set
  -- Syntax⊥ (Some Γ) a = Syntax Γ a
  -- Syntax⊥ ⊥ a = ⊤

  VecSyntax Γ [] = ⊤
  VecSyntax Γ (x ∷ v) = Syntax Γ x × VecSyntax Γ v 

  substitution : MetaContext → MetaContext → Set
  substitution [] Δ = ⊤
  substitution (m ∷ Γ) Δ = Syntax Δ m × substitution Γ Δ

  id-subst : (Γ : MetaContext) → substitution Γ Γ
  id-subst [] = tt
  id-subst (m ∷ Γ) = {!!}

  substitution⊥ : MetaContext⊥ → MetaContext⊥ → Set
  substitution⊥ Γ ⊥ = ⊤
  substitution⊥ (Some Γ) (Some Δ) = substitution Γ Δ
  substitution⊥ ⊥ (Some Δ) = Empty

  _[_]t : ∀ {Γ}{a}(t : Syntax Γ a){Δ}(σ : substitution Γ Δ) → Syntax Δ a
  _[_]ts : ∀ {Γ}{n}{as : Vec VariableContext n}(ts : VecSyntax Γ as){Δ}(σ : substitution Γ Δ) → VecSyntax Δ as

  _[_]t {Γ}{a}t{Δ}σ = {!!}
  _[_]ts {Γ}{as}ts {Δ}σ = {!!}


  substitution-⊥ : MetaContext → MetaContext⊥ → Set
  substitution-⊥ Γ ⊥ = ⊤
  substitution-⊥ Γ (Some Δ) = substitution Γ Δ

  _∘σ_ : ∀ {Γ₁ Γ₂ Γ₃} (σ : substitution Γ₁ Γ₂)(δ : substitution-⊥ Γ₂ Γ₃) → substitution-⊥ Γ₁ Γ₃
  σ ∘σ δ = {!!}

  -- VecSyntax⊥ : MetaContext⊥ → ∀{n}(v : Vec VariableContext n) → Set
  -- VecSyntax⊥ (just Γ) v = {!VecSyna!}
  -- VecSyntax⊥ nothing v = {!!}
  outSubstitution-⊥ : MetaContext → Set
  outSubstitution-⊥ Γ = Σ _ (substitution-⊥ Γ)

  outSubstitution : MetaContext → Set
  outSubstitution Γ = Σ _ (substitution Γ)

  out-bottomise : ∀ {Γ} → outSubstitution Γ → outSubstitution-⊥ Γ
  out-bottomise (Δ , σ) = (Some Δ , σ)

  out-⊥ : (Γ : MetaContext) → outSubstitution-⊥ Γ
  out-⊥ Γ = ⊥ , tt

  out-id : (Γ : MetaContext) → outSubstitution-⊥ Γ
  out-id Γ = (Some Γ) , (id-subst Γ)

  wk-subst : (Γ : MetaContext) → (m : A.Obj) → substitution Γ (m ∷ Γ)
  wk-subst Γ m = {!σ ∘σ ?!}

  wk-out : ∀ {x}{Γ : MetaContext} → outSubstitution Γ → outSubstitution (x ∷ Γ)
  wk-out {x}(Δ , σ) = x ∷ Δ , (Flexible (here ≡.refl) A.id) , (σ ∘σ wk-subst Δ x)

  -- wk-out : (Γ : MetaContext) → (m : A.Obj) → Syntax (m ∷ Γ) m → substitution Γ (m ∷ Γ)
  -- wk-out Γ m = {!σ ∘σ ?!}

  unify : {Γ : MetaContext} → {a : VariableContext} → ∀ (t u : Syntax Γ a) → outSubstitution-⊥ Γ
  prune : {Γ : MetaContext} → {a : VariableContext} → (t : Syntax Γ a) → ∀ {m} → m A.⇒ a → outSubstitution-⊥ Γ
  transition-prune : {Γ : MetaContext} → {a : VariableContext} → (t : Syntax Γ a) → ∀ {m} → m ∈ Γ → m A.⇒ a → outSubstitution-⊥ Γ
  unifyPbks : (Γ : MetaContext)→ ∀ {P m'} → (M' : m' ∈ Γ) → (p₂ : P A.⇒ m') → Σ _ (λ Δ → P ∈ Δ × substitution Γ Δ)
  unifyPbksTop : (Γ : MetaContext)→ ∀ {m m' a} → (M' : m' ∈ Γ) → (f : m A.⇒ a)(f' : m' A.⇒ a) → outSubstitution (m ∷ Γ)
  pruneVec : {Γ : MetaContext} → {n : ℕ} → ∀{as}{ms} → ∀ (t : VecSyntax Γ {n} as) →
     ms V.⇒ as → outSubstitution-⊥ Γ

  occur-check : ∀ {Γ}{m}(M : m ∈ Γ) {a} → Syntax Γ a → 𝔹
  occur-checkVec : ∀ {Γ}{m}(M : m ∈ Γ) {n}{as} → VecSyntax Γ {n = n} as → 𝔹
  occur-check {Γ} {m} M {a} (Rigid o x) = occur-checkVec M x
  occur-check {Γ} {m} M {a} (Flexible M' f) = eq-∈ _ M M'
  
  occur-checkVec {Γ} {m} M {.ℕ.zero} {[]} ts = false
  occur-checkVec {Γ} {m} M {.(ℕ.suc _)} {a ∷ as} (t , ts) = occur-check M t ∨ occur-checkVec M ts
  

  transition-prune {Γ}{a} t {m} inM f with occur-check inM t
  ... | true = out-⊥ Γ
  ... | false = prune t f

  prune {Γ} {a} (Rigid {n = n}o ts) {m} f with o 〚 f 〛⁻¹
  ... | nothing = out-⊥ Γ
  ... | just (o' , ≡.refl) = pruneVec {as = α o} ts (αf o' f)

  prune {Γ} {a} (Flexible {m = m} M x) {m'} f with 𝓐-pullbacks x f
  ... | record { P = P ; p₁ = p₁ ; p₂ = p₂ } with unifyPbks Γ M p₁
  ... | Δ , (inP , σ) = out-bottomise (Δ , σ)

  pruneVec {Γ} {.ℕ.zero} {[]} {ms} ts xs = out-id Γ
  pruneVec {Γ} {.(ℕ.suc _)} {a ∷ as} {m ∷ ms} (t , ts) (x , xs) with prune t x
  ... | ⊥ , σ = out-⊥ Γ
  ... | Some Δ , σ with pruneVec (ts [ σ ]ts) xs
  ... | (Δ' , σ') = Δ' , {!σ ∘σ σ'!}

  unifyVec : {Γ : MetaContext} → {n : ℕ} → ∀{as} → ∀ (t u : VecSyntax Γ {n} as) → outSubstitution-⊥ Γ
  unifyVec {Γ} {.ℕ.zero} {[]} t u = out-id Γ
  unifyVec {Γ} {.(ℕ.suc _)} {a ∷ as} (t , ts) (u , us) with unify t u
  ... | ⊥ , σ = out-⊥ Γ
  ... | Some Δ , σ with unifyVec {Δ} (ts [ σ ]ts) (us [ σ ]ts)
  ... | (Δ' , σ') = Δ' , {!σ ∘σ σ' !}

  unifyFlexible : (Γ : MetaContext) → ∀ {m m' a} → (M : m ∈ Γ) → (M' : m' ∈ Γ) → (f : m A.⇒ a)(f' : m' A.⇒ a) → outSubstitution Γ

  unify {Γ} {a} (Rigid {n = n} o x) (Rigid {n = n'} o' x') with n ≟ n'
  ... | .false because ofⁿ ¬p = out-⊥ Γ
  ... | .true because ofʸ ≡.refl with o ≟O o'
  ... | .false because ofⁿ ¬p = out-⊥ Γ
  ... | .true because ofʸ ≡.refl = unifyVec x x'
  unify {Γ} {a} (Rigid o x) (Flexible M f) = transition-prune (Rigid o x) M f
  unify {Γ} {a} (Flexible M f) (Rigid o x) = transition-prune (Rigid o x) M f
  unify {Γ} {a} (Flexible M f) (Flexible M' f') = out-bottomise (unifyFlexible Γ M M' f f')


  unifyFlexible .(m ∷ _) {m} {.m} (here {xs = Γ} ≡.refl) (here ≡.refl) f f' with 𝓐-equalizers f f'
  ... | record { obj = m'' ; arr = f'' } = (m'' ∷ Γ) , (Flexible (here ≡.refl) f'') , (wk-subst Γ m'')

  unifyFlexible .(_ ∷ _) {m} {m'} {a} (here {xs = Γ}≡.refl) (there M') f f' = unifyPbksTop Γ M' f f'
  unifyFlexible .(_ ∷ _) {m} {m'} {a} (there M) (here {xs = Γ} ≡.refl) f f' = unifyPbksTop Γ M f' f
  unifyFlexible .(_ ∷ _) {m} {m'} (there {x = x}{xs = Γ} M) (there M') f f' =  wk-out (unifyFlexible Γ M M' f f') 


  unifyPbksTop Γ {m}{m'}{a} M' f f' with 𝓐-pullbacks f f'
  ... | record { P = P ; p₁ = p₁ ; p₂ = p₂ } with unifyPbks Γ M' p₂
  ... | Δ , (inP , σ) =  Δ , (Flexible inP p₁) , σ

  unifyPbks .(_ ∷ _) {P} {m'} (here {xs = Γ} ≡.refl) p₂ = (P ∷ Γ) , ((here ≡.refl) , ((Flexible (here ≡.refl) p₂) , wk-subst Γ P))
  unifyPbks .(_ ∷ _) {P} {m'} (there {x = x}{xs = Γ} M') p₂ with unifyPbks Γ M' p₂
  ... | Δ , (inP , σ) = (x ∷ Δ) , ((there inP) , ((Flexible (here ≡.refl) A.id) , (σ ∘σ wk-subst Δ x)))


