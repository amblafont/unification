{-# OPTIONS --no-termination-check #-}
module examples where

open import Relation.Nullary using (Dec ; yes ; no)
open import Data.List as List hiding (map ; [_])
open import Data.List.Relation.Binary.Pointwise using (Pointwise ; [] ; _∷_)
open import Data.Product using (_,_; Σ; _×_ )
open import Data.Maybe.Base using (Maybe) renaming (nothing to ⊥ ; just to ⌊_⌋)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
open import Agda.Primitive

open import Agda.Builtin.Unit
open import lib
open import main
open import Data.Fin as Fin using (Fin)
open import Data.Nat using (ℕ; _≟_ ; _+_)
open import Data.Vec.Base as Vec using (Vec; []; _∷_)
open import Data.Sum.Base hiding (map)

postulate ∈-map : ∀ {i j}{A : Set i}{B : Set j}{a l} → (f : A → B) → a ∈ l → f a ∈ List.map f l

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


 _❴_❵ : ∀ {n m} → Ty n → n ⇒ᵣ m → Ty m
 Var x ❴ r ❵ = Var (Vec.lookup r x)
 (T ⇒T T') ❴ r ❵ = T ❴ r ❵ ⇒T (T' ❴ r ❵)
 ∀T T ❴ r ❵ = ∀T (T ❴ r ↑ ❵)

 _❴_❵s : ∀ {n m} → List (Ty n) → n ⇒ᵣ m → List (Ty m)
 σ ❴ r ❵s = List.map (_❴ r ❵) σ


-- unary substitution
 _[_] : ∀ {n} → Ty (1 + n) → Ty n → Ty n
 Var x [ u ] = {!!}
 (t ⇒T t') [ u ] = (t [ u ]) ⇒T (t' [ u ])
 ∀T t [ u ] = ∀T (t [ {!!} ])

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
 (x , f) ❴ r ❵l = ∈-map _❴ r ❵ x , (f ❴ r ❵l)

 idₗ : ∀ {B}{l : List B} → l ⇒ₗ l
 idₗ {l = []} = []
 idₗ {l = x ∷ l} = Ο , VecList.map (λ a → 1+) (idₗ {l = l})

 data _⇒_ : A → A → Set where
    Hom : ∀ {n n' σ σ' τ σ❴η❵ τ'} 
                (η : n ⇒ᵣ n') →
                σ❴η❵ ⇒ₗ σ' →
                σ❴η❵ ≡ σ ❴ η ❵s →
                τ' ≡ τ ❴ η ❵ →
                (n ∣ σ ⟶ τ) ⇒ (n' ∣ σ' ⟶ τ')

 id : ∀ {a} → a ⇒ a
 id {n ∣ σ ⟶ τ} = Hom (idᵣ {n}) idₗ {!!} {!!}

 _∘_ : ∀ {a b c : A} → b ⇒ c → a ⇒ b → a ⇒ c
 Hom η x ≡.refl ≡.refl ∘ Hom η' x' ≡.refl ≡.refl = Hom (η ∘ᵣ η') (x ∘ₗ (x' ❴ η ❵l)) {!!} {!!}

 module _ n (Γ : List (Ty n)) (τ : Ty n) where
  data O' : Set where
   Var : τ ∈ Γ → O'
   App : Ty n → O'
   Lam : ∀ τ₁ τ₂ → τ ≡ τ₁ ⇒T τ₂ → O'
   TApp : ∀ (τ₁ : Ty (1 + n))(τ₂ : Ty n) → τ ≡ τ₁ [ τ₂ ] → O' 
   TLam : ∀ τ' → τ ≡ ∀T τ' → O'
 module _ {n Γ τ} where
  α' : O' n Γ τ → List A
  α' (Var x) = []
  α' (App τ') = (n ∣ Γ ⟶ (τ' ⇒T τ)) ∷ (n ∣ Γ ⟶ τ') ∷ []
  α' (Lam τ₁ τ₂ x) = n ∣ (τ₁ ∷ Γ) ⟶ τ₂ ∷ []
  α' (TApp τ₁ τ₂ x) = n ∣ Γ ⟶ (∀T τ₁) ∷ []
  α' (TLam τ' x) = (1 + n) ∣ {!Γ!} ⟶ τ' ∷ []
 module RenSymbol {n Γ τ n' Γ' τ'} where
  _｛_｝ : O' n Γ τ → (n ∣ Γ ⟶ τ) ⇒ (n' ∣ Γ' ⟶ τ') → O' n' Γ' τ'
  -- o ｛ Hom η x e1 e2 ｝ = {!!}
  Var τ∈ ｛ Hom η x e1 e2 ｝ = {!Var τ∈ !}
  App x₁ ｛ Hom η x e1 e2 ｝ = {!Var!}
  Lam τ₁ τ₂ x₁ ｛ Hom η x e1 e2 ｝ = {!!}
  TApp τ₁ τ₂ x₁ ｛ Hom η x e1 e2 ｝ = {!!}
  TLam τ' x₁ ｛ Hom η x e1 e2 ｝ = {!!}
  -- Var x ｛ r ｝ = {!!}
  -- App x ｛ r ｝ = {!!}
  -- Lam τ₁ τ₂ x ｛ r ｝ = {!!}
  -- TApp τ₁ τ₂ x ｛ r ｝ = {!!}
  -- TLam τ' x ｛ r ｝ = {!!}
 
 data O : A → Set where
   op : ∀ {n Γ τ} → O' n Γ τ → O (n ∣ Γ ⟶ τ)
 -- O (n ∣ σ ⟶ τ) = O' n σ τ

 α : {a : A} → O a → List A
 α (op o) = α' o
 -- α {.(n ∣ Γ ⟶ τ)} (Var n Γ τ x) = []
 -- α {.(n ∣ Γ ⟶ τ)} (App n Γ τ τ') = (n ∣ Γ ⟶ (τ' ⇒T τ)) ∷ (n ∣ Γ ⟶ τ') ∷ []
 -- α {.(n ∣ Γ ⟶ (τ₁ ⇒T τ₂))} (Lam n Γ τ₁ τ₂) = n ∣ (τ₁ ∷ Γ) ⟶ τ₂ ∷ []
 -- α {.(n ∣ Γ ⟶ (τ₁ [ τ₂ ]))} (TApp n Γ τ₁ τ₂) = n ∣ Γ ⟶ (∀T τ₁) ∷ []
 -- α {.(n ∣ Γ ⟶ ∀T τ')} (TLam n Γ τ') = (1 + n) ∣ {!Γ!} ⟶ τ' ∷ []

   {- 
 data O : A → Set where
   Var : ∀ n Γ τ → τ ∈ Γ → O (n ∣ Γ ⟶ τ)
   App : ∀ n Γ τ  → Ty n → O (n ∣ Γ ⟶ τ)
   Lam : ∀ n Γ τ₁ τ₂  → O (n ∣ Γ ⟶ (τ₁ ⇒T τ₂))
   TApp : ∀ n Γ (τ₁ : Ty (1 + n))(τ₂ : Ty n) → O (n ∣ Γ ⟶ (τ₁ [ τ₂ ]))
   TLam : ∀ n Γ τ' → O (n ∣ Γ ⟶ ∀T τ')

 α : {a : A} → O a → List A
 α {.(n ∣ Γ ⟶ τ)} (Var n Γ τ x) = []
 α {.(n ∣ Γ ⟶ τ)} (App n Γ τ τ') = (n ∣ Γ ⟶ (τ' ⇒T τ)) ∷ (n ∣ Γ ⟶ τ') ∷ []
 α {.(n ∣ Γ ⟶ (τ₁ ⇒T τ₂))} (Lam n Γ τ₁ τ₂) = n ∣ (τ₁ ∷ Γ) ⟶ τ₂ ∷ []
 α {.(n ∣ Γ ⟶ (τ₁ [ τ₂ ]))} (TApp n Γ τ₁ τ₂) = n ∣ Γ ⟶ (∀T τ₁) ∷ []
 α {.(n ∣ Γ ⟶ ∀T τ')} (TLam n Γ τ') = (1 + n) ∣ {!Γ!} ⟶ τ' ∷ []

 _｛_｝ : {a b : A} → O a → a ⇒ b → O b
 o ｛ r ｝ = o ❴ _ ◄ r ❵

 _❴_◄_❵ : ∀ {a} → O a → ∀ b → a ⇒ b → O b
 -- o ❴ n' ∣ Γ' ⟶ .(_ ❴ η ❵) ◄ Hom η x ≡.refl ≡.refl ❵ = {!!}
 Var _ _ _ τ∈ ❴ n' ∣ Γ' ⟶ .(_ ❴ η ❵) ◄ Hom η x ≡.refl ≡.refl ❵ =
     Var _ _ _ ( VecList.nth (∈-map _❴ η ❵ τ∈) x )
 App _ _ τ τ' ❴ n' ∣ Γ' ⟶ .(_ ❴ η ❵) ◄ Hom η x ≡.refl ≡.refl ❵ = App _ _ _ (τ' ❴ η ❵)
 -- Lam Γ n τ₁ τ₂ ❴ n' ∣ Γ' ⟶ τ'  ◄ Hom η x e1 e2 ❵ = {! Lam _ _ (τ₁ ❴ η ❵) (τ₂ ❴ η ❵) !}
 Lam _ _ τ₁ τ₂ ❴ n' ∣ Γ' ⟶ .((τ₁ ⇒T τ₂) ❴ η ❵) ◄ Hom η x ≡.refl ≡.refl ❵ =  Lam _ _ (τ₁ ❴ η ❵) (τ₂ ❴ η ❵) 
 TApp _ _ τ₁ τ₂ ❴ n' ∣ Γ' ⟶ .((τ₁ [ τ₂ ]) ❴ η ❵) ◄ Hom η x ≡.refl ≡.refl ❵ = {! TApp _ _ (τ₁ ❴ η ↑ ❵) (τ₂ ❴ η ❵) !}
 TLam _ _ τ' ❴ n' ∣ Γ' ⟶ .(∀T τ' ❴ η ❵) ◄ Hom η x ≡.refl ≡.refl ❵ = TLam _ _ (τ' ❴ η ↑ ❵)
 
 _｛_｝ : {a b : A} → O a → a ⇒ b → O b
 o ｛ r ｝ = o ❴ _ ◄ r ❵
  

 _^_ : {a b : A} (x : a ⇒ b) (o : O a) → Pointwise _⇒_ (α o) (α (o ｛ x ｝))
 _^_ {.(_ ∣ _ ⟶ _)} {.(_ ∣ _ ⟶ (_ ❴ η ❵))} (Hom η x ≡.refl ≡.refl) (Var _ _ _ x₁) = []
 _^_ {.(_ ∣ _ ⟶ _)} {.(_ ∣ _ ⟶ (_ ❴ η ❵))} (Hom η x ≡.refl ≡.refl) (App _ _ _ x₁) =
     Hom η x ≡.refl ≡.refl ∷ Hom η x ≡.refl ≡.refl ∷ []
 _^_ {.(_ ∣ _ ⟶ (τ₁ ⇒T τ₂))} {.(_ ∣ _ ⟶ ((τ₁ ⇒T τ₂) ❴ η ❵))} (Hom η x ≡.refl ≡.refl) (Lam _ _ τ₁ τ₂)
      = Hom η (Ο , VecList.map (λ a x₁ → 1+ x₁) x) ≡.refl ≡.refl ∷ []
 _^_ {.(_ ∣ _ ⟶ (τ₁ [ τ₂ ]))} {.(_ ∣ _ ⟶ ((τ₁ [ τ₂ ]) ❴ η ❵))} (Hom η x ≡.refl ≡.refl) (TApp _ _ τ₁ τ₂)
     = {!!}
 _^_ {.(_ ∣ _ ⟶ ∀T τ')} {.(_ ∣ _ ⟶ (∀T τ' ❴ η ❵))} (Hom η x ≡.refl ≡.refl) (TLam _ _ τ')
     = Hom (η ↑ ) {!!} {!!} {!!} ∷ []


system-F-sig : Signature lzero lzero lzero
system-F-sig = record
               { System-F 
               }

system-F-friendly : isFriendly system-F-sig
system-F-friendly = record { equaliser = {!!} ; pullback = {!!} ; _≟_ = {!!} ; _｛_｝⁻¹ = {!!} }


-}
