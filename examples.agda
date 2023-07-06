{-# OPTIONS --no-termination-check --type-in-type #-}
module examples where

open import Relation.Nullary using (Dec ; yes ; no)
open import Data.List as List hiding (map ; [_])
open import Data.List.Relation.Binary.Pointwise using (Pointwise ; [] ; _∷_)
open import Data.Product using (_,_; Σ; _×_ )
open import Data.Maybe.Base using (Maybe) renaming (nothing to ⊥ ; just to ⌊_⌋)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_) renaming (refl to 1ₑ)
open import Agda.Primitive
open import Relation.Binary hiding (_⇒_)
open import Data.List.Membership.Propositional 
open import Data.List.Membership.Propositional.Properties using (∈-map⁺)
-- open import Data.List.Relation.Unary.Any.Properties using (gmap)
import Data.List.Relation.Unary.Any as Any

open import Agda.Builtin.Unit
open import lib
open import main
open import Data.Fin as Fin using (Fin)
open import Data.Nat as ℕ using (ℕ; _+_) 
open import Data.Vec.Base as Vec using (Vec; []; _∷_)
open import Data.Sum.Base hiding (map)


-- ∈-map' : ∀ {i j}{A : Set i}{B : Set j}{a l} → (f : A → B) → a ∈ l → f a ∈ List.map f l
-- ∈-map' f a∈ = ∈-map⁺ f a∈
-- gmap (λ {1ₑ → 1ₑ}) a∈  
-- ∈-map⁺

module VecList where

  -- VecList B [l₀ ; .. ; lₙ] ≃ B l₀ × .. × B lₙ
  data VecList {A : Set}(B : A → Set) : List A  → Set where
    [] : VecList B []
    _,_ : ∀ {a as} → B a → VecList B as → VecList B (a ∷ as)

  [_] : ∀ {A}{B : A → Set}{a : A} → B a → VecList B (a ∷ []) 
  [ b ] = b , []

  map : ∀ {A : Set}{B B' : A → Set}{l : List A} → (∀ a → B a → B' a) → VecList B l → VecList B' l
  map f [] = []
  map f (x , xs) = f _ x , map f xs

  nth : ∀ {A : Set}{B : A → Set}{l : List A}{a} → a ∈ l → VecList B l →  B a
  nth Ο (t , _) = t
  nth (1+ a∈) (_ , ts) = nth a∈ ts

  init : ∀ {A : Set}{B : A → Set} → (∀ a → B a) → (ℓ : List A) → VecList B ℓ
  init f [] = []
  init f (x ∷ ℓ) = f x , init f ℓ

open VecList using (VecList ; [] ; _,_)
module System-F where

 infixr 19 _⇒T_
 data Ty n : Set where
   Var : Fin n → Ty n
   _⇒T_ : Ty n → Ty n → Ty n
   ∀T : Ty (1 + n) → Ty n


 -- renaming, copied from lc.lagda
 _⇒ᵣ_ : ℕ → ℕ → Set
 n ⇒ᵣ m = Vec (Fin m) n

 _∘ᵣ_ : ∀ {p q r} → (q ⇒ᵣ r) → (p ⇒ᵣ q) → (p ⇒ᵣ r)
 xs ∘ᵣ [] = []
 xs ∘ᵣ (y ∷ ys) = Vec.lookup xs y ∷ (xs ∘ᵣ ys)

 _↑ : ∀ {p q} → p ⇒ᵣ q → (1 + p) ⇒ᵣ (1 + q)
 _↑ {p}{q} x = Vec.insert (Vec.map Fin.inject₁ x)
                    (Fin.fromℕ p) (Fin.fromℕ q)

 idᵣ : ∀ {n} → n ⇒ᵣ n
 idᵣ {n} = Vec.allFin n
 -- end of copying

 wkᵣ : ∀ {n} → n ⇒ᵣ (1 + n)
 wkᵣ {n} = Vec.map Fin.inject₁ idᵣ
 -- wkᵣ {ℕ.zero} = []
 -- wkᵣ {ℕ.suc n} = Fin.zero ∷ {!!}


 _❴_❵ : ∀ {n m} → Ty n → n ⇒ᵣ m → Ty m
 Var x ❴ r ❵ = Var (Vec.lookup r x)
 (T ⇒T T') ❴ r ❵ = T ❴ r ❵ ⇒T (T' ❴ r ❵)
 ∀T T ❴ r ❵ = ∀T (T ❴ r ↑ ❵)

 _❴_❵s : ∀ {n m} → List (Ty n) → n ⇒ᵣ m → List (Ty m)
 σ ❴ r ❵s = List.map (_❴ r ❵) σ

-- prop
 _❴idᵣ❵ : ∀ {n} → (A : Ty n) → A ❴ idᵣ ❵ ≡ A
 Var x ❴idᵣ❵ = {!!}
 (A ⇒T B) ❴idᵣ❵ rewrite A ❴idᵣ❵ | B ❴idᵣ❵ = 1ₑ
 -- rewrite A ❴idᵣ❵ | B ❴idᵣ❵ = {!1ₑ!}
 ∀T A ❴idᵣ❵ = {!!}

 _❴idᵣ❵s : ∀ {n} → (l : List (Ty n)) → l ❴ idᵣ ❵s ≡ l 
 [] ❴idᵣ❵s = 1ₑ
 (x ∷ l) ❴idᵣ❵s rewrite x ❴idᵣ❵ | l ❴idᵣ❵s = 1ₑ

-- weakening
 wkT : ∀ {n} → Ty n → Ty (1 + n)
 wkT T = T ❴ wkᵣ ❵

 wkC : ∀ {n} → List (Ty n) → List (Ty (1 + n))
 wkC = List.map wkT
 -- wkT (Var x) = Var (Fin.inject₁ x)
 -- wkT (T ⇒T U) = wkT T ⇒T wkT U
 -- wkT (∀T T) = {!∀T!}

-- unary substitution
 _[_↦_] : ∀ {n} → Ty (1 + n) → Fin (1 + n) → Ty n → Ty n
 Var j [ i ↦ T' ] with i Fin.≟ j
 ... | yes _ = T'
 ... | no e = Var (Fin.punchOut e)
 (T ⇒T U) [ n ↦ T' ] = T [ n ↦ T' ] ⇒T U [ n ↦ T' ]
 ∀T T [ n ↦ T' ] = ∀T (T [ Fin.inject₁ n ↦ wkT T' ])

 _[_] : ∀ {n} → Ty (1 + n) → Ty n → Ty n
 t [ u ] = t [ Fin.fromℕ _ ↦ u ]
 -- Var x [ u ] = {!!}
 -- (t ⇒T t') [ u ] = (t [ u ]) ⇒T (t' [ u ])
 -- ∀T t [ u ] = ∀T (t [ {!!} ])

 infix 19 _∣_⟶_
 record A : Set where
   constructor _∣_⟶_
   eta-equality
   field
     n : ℕ
     σ : List (Ty n)
     τ : Ty n

 infixr 19 _⇒ₗ_
 _⇒ₗ_ : ∀ {B : Set } → List B → List B → Set
 l1 ⇒ₗ l2 = VecList (_∈ l2) l1

 _∘ₗ_ : ∀ {B}{p q r : List B} → (q ⇒ₗ r) → (p ⇒ₗ q) → (p ⇒ₗ r)
 l1 ∘ₗ [] = []
 l1 ∘ₗ (x , l2) = VecList.nth x l1 , (l1 ∘ₗ l2)

 _❴_❵l : ∀ {n m}{σ σ' : List (Ty n)} → σ ⇒ₗ σ' → (r : n ⇒ᵣ m) → (σ ❴ r ❵s) ⇒ₗ (σ' ❴ r ❵s)
 [] ❴ r ❵l = []
 (x , f) ❴ r ❵l = ∈-map⁺ _❴ r ❵ x , (f ❴ r ❵l)

 idₗ : ∀ {B}{l : List B} → l ⇒ₗ l
 idₗ {l = []} = []
 idₗ {l = x ∷ l} = Ο , VecList.map (λ a → 1+) (idₗ {l = l})

 wkl : ∀ {n}{σ σ' : List (Ty n)} → σ ⇒ₗ σ' → wkC σ ⇒ₗ wkC σ'
 wkl r = {!!}

 data _⇒_ : A → A → Set where
    Hom : ∀ {n n' σ σ' τ σ❴η❵ τ'} 
                (η : n ⇒ᵣ n') →
                σ❴η❵ ⇒ₗ σ' →
                -- σ❴η❵ ≡ σ ❴ η ❵s →
                σ ❴ η ❵s ≡ σ❴η❵ →
                τ ❴ η ❵ ≡ τ' →
                (n ∣ σ ⟶ τ) ⇒ (n' ∣ σ' ⟶ τ')

 pattern Hom= t u = Hom t u 1ₑ 1ₑ

 id : ∀ {a} → a ⇒ a
 id {n ∣ σ ⟶ τ} = Hom (idᵣ {n}) idₗ (σ ❴idᵣ❵s) (τ ❴idᵣ❵)

 _∘_ : ∀ {a b c : A} → b ⇒ c → a ⇒ b → a ⇒ c
 Hom= η x ∘ Hom= η' x' = Hom (η ∘ᵣ η') (x ∘ₗ (x' ❴ η ❵l)) {!!} {!!}

 data O' n Γ τ : Set where
   Var : τ ∈ Γ → O' n Γ τ
   App : Ty n → O' n Γ τ
   Lam : ∀ τ₁ τ₂ → τ ≡ τ₁ ⇒T τ₂ → O' n Γ τ
   TApp : ∀ (τ₁ : Ty (1 + n))(τ₂ : Ty n) → τ ≡ τ₁ [ τ₂ ] → O'  n Γ τ
   TLam : ∀ τ' → τ ≡ ∀T τ' → O' n Γ τ
 module EqO' {n Γ τ} where
   _≟_ : ∀  (o o' : O' n Γ τ) → Dec (o ≡ o')

   Var x ≟ Var x' = {!!}
   -- with x Fin.≟ x'
   -- ... | yes 1ₑ = {!!}
   -- ... | no p = ?
   App t ≟ App t' = {!!}
   -- ... | yes 1ᵣ = ?
   -- ... | no p = {!!}
   Lam τ u x ≟ Lam τ' u' x' = {!!}
   TApp τ₁ τ₂ e ≟ TApp τ₁' τ₂' e' = {!!}
   TLam τ₂ e ≟ TLam τ₂' e' = {!!}

   Var _ ≟ App _ = no (λ ())
   Var x ≟ Lam τ₁ τ₂ x₁ = no (λ ())
   Var x ≟ TApp τ₁ τ₂ x₁ = no (λ ())
   Var x ≟ TLam τ' x₁ = no (λ ())
   App x ≟ Var x₁ = no (λ ())
   App x ≟ Lam τ₁ τ₂ x₁ = no (λ ())
   App x ≟ TApp τ₁ τ₂ x₁ = no (λ ())
   App x ≟ TLam τ' x₁ = no (λ ())
   Lam τ₁ τ₂ x ≟ Var x₁ = no (λ ())
   Lam τ₁ τ₂ x ≟ App x₁ = no λ ()
   Lam τ₁ τ₂ x ≟ TApp τ₃ τ₄ x₁ = no (λ ())
   Lam τ₁ τ₂ x ≟ TLam τ' x₁ = no (λ ())
   TApp τ₁ τ₂ x ≟ Var x₁ = no (λ ())
   TApp τ₁ τ₂ x ≟ App x₁ = no (λ ())
   TApp τ₁ τ₂ x ≟ Lam τ₃ τ₄ x₁ = no (λ ())
   TApp τ₁ τ₂ x ≟ TLam τ' x₁ = no (λ ())
   TLam τ' x ≟ Var x₁ = no (λ ())
   TLam τ' x ≟ App x₁ = no (λ ())
   TLam τ' x ≟ Lam τ₁ τ₂ x₁ = no (λ ())
   TLam τ' x ≟ TApp τ₁ τ₂ x₁ = no (λ ())



 module _ {n Γ τ} where
  α' : O' n Γ τ → List A
  α' (Var x) = []
  α' (App τ') = (n ∣ Γ ⟶ (τ' ⇒T τ)) ∷ (n ∣ Γ ⟶ τ') ∷ []
  α' (Lam τ₁ τ₂ x) = n ∣ (τ₁ ∷ Γ) ⟶ τ₂ ∷ []
  α' (TApp τ₁ τ₂ x) = n ∣ Γ ⟶ (∀T τ₁) ∷ []
  α' (TLam τ' x) = (1 + n) ∣ wkC Γ ⟶ τ' ∷ []
 module RenSymbol {n Γ τ n' Γ' τ'} where
  _｛_｝ : O' n Γ τ → (n ∣ Γ ⟶ τ) ⇒ (n' ∣ Γ' ⟶ τ') → O' n' Γ' τ'
  -- o ｛ Hom η x e1 e2 ｝ = {!o!}
  Var i ｛ Hom= η x ｝ = 
       Var ( VecList.nth (∈-map⁺ _❴ η ❵ i) x )
  App τ₂ ｛ Hom= η x ｝ = App (τ₂ ❴ η ❵)
  Lam τ₁ τ₂ 1ₑ ｛ Hom= η x ｝ = Lam (τ₁ ❴ η ❵) (τ₂ ❴ η ❵) 1ₑ
  TApp τ₁ τ₂ 1ₑ ｛ Hom= η x ｝ = TApp (τ₁ ❴ η ↑ ❵) (τ₂ ❴ η ❵) {!e!}
  TLam τ' 1ₑ ｛ Hom= η x ｝ = TLam (τ' ❴ η ↑ ❵) 1ₑ

  _^_ : (r : (n ∣ Γ ⟶ τ) ⇒ (n' ∣ Γ' ⟶ τ')) → (o : O' n Γ τ) → 
            Pointwise _⇒_ (α' o) (α' (o ｛ r ｝))
  Hom= η x ^ Var i = []
  Hom= η x ^ App _ =
     Hom= η x ∷
     Hom= η x ∷ []
  Hom= η x ^ Lam τ₁ τ₂ 1ₑ =
     Hom η (Ο , VecList.map (λ a x₁ → 1+ x₁) x) 1ₑ 1ₑ ∷ []
  Hom= η x ^ TApp τ₁ τ₂ 1ₑ = 
    Hom= η x ∷ []
     
  Hom= η x ^ TLam τ' 1ₑ =
    Hom (η ↑) (wkl x) {!!} 1ₑ
     ∷ []

  _｛_｝⁻¹ : ∀  (o : O' n' Γ' τ') (x : (n ∣ Γ ⟶ τ) ⇒ (n' ∣ Γ' ⟶ τ')) →
      Maybe-PreImage (_｛ x ｝) o
  Var i ｛ Hom= η x ｝⁻¹ with {! nth⁻¹ Fin._≟_  !}
  ... | e = {!
  Var ( nth⁻¹ Fin._≟_ i x)

  !}
  App t ｛ Hom= η x ｝⁻¹ = {!!}
  Lam τ₁ τ₂ x₁ ｛ Hom= η x ｝⁻¹ = {!!}
  TApp τ₁ τ₂ x₁ ｛ Hom= η x ｝⁻¹ = {!!}
  TLam τ' x₁ ｛ Hom= η x ｝⁻¹ = {!!}

 
 data O : A → Set where
   op : ∀ {n Γ τ} → O' n Γ τ → O (n ∣ Γ ⟶ τ)
 -- O (n ∣ σ ⟶ τ) = O' n σ τ

 α : {a : A} → O a → List A
 α (op o) = α' o
 _｛_｝ : {a b : A} → O a → a ⇒ b → O b
 _｛_｝ {n ∣ σ ⟶ τ} {n₁ ∣ σ₁ ⟶ τ₁} (op o) r = op (RenSymbol._｛_｝ o r)
 _^_ : {a b : A} (x : a ⇒ b) (o : O a) → Pointwise _⇒_ (α o) (α (o ｛ x ｝))
 _^_  {n ∣ σ ⟶ τ} {n₁ ∣ σ₁ ⟶ τ₁} r (op o)= RenSymbol._^_ r o

system-F-sig : Signature lzero lzero lzero
system-F-sig = record
               { System-F 
               }

system-F-friendly : isFriendly system-F-sig
system-F-friendly = record { equaliser = {!!} ; pullback = {!!} ; _≟_ = {!!} ; _｛_｝⁻¹ = {!!} }
   where open System-F
