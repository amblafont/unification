{-# OPTIONS --no-termination-check --type-in-type #-}
module examples where

open import Data.List as List hiding (map ; [_])
open import Data.Empty renaming (⊥ to Empty)
open import Data.List.Relation.Binary.Pointwise using (Pointwise ; [] ; _∷_)
open import Data.Product using (_,_; Σ; _×_ ; proj₁ ; proj₂)
open import Data.Maybe.Base using (Maybe) renaming (nothing to ⊥ ; just to ⌊_⌋)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_ ; _≢_ ; cong ; cong₂ ; setoid) renaming (refl to 1ₑ)
open import Agda.Primitive
open import Relation.Binary hiding (_⇒_)
open import Data.List.Membership.Propositional 
open import Data.List.Membership.Propositional.Properties using (∈-map⁺)
open import Data.Vec.Properties using (lookup-allFin ; map-∘ ; map-cong ; lookup-map ; tabulate-∘ ; tabulate-allFin)
open import Data.Vec.Membership.Propositional renaming (_∈_ to _∈̬_)
-- open import Data.List.Relation.Unary.Any.Properties using (gmap)
open import Data.List.Relation.Unary.Any as Any using (index ; here ; there) renaming (_─_ to _⑊_ )
open import Data.Vec.Relation.Unary.Any using () renaming (index to index̬)
open import Data.Vec.Relation.Unary.Any.Properties using () renaming (lookup-index to lookup-index̬)

open import Agda.Builtin.Unit
open import Relation.Nullary using (Dec ; yes ; no ; does)
open import Relation.Nullary.Decidable using (dec-yes-irr ; dec-true ; dec-false)
open import Relation.Nullary.Negation.Core using (contraposition)
open import lib
open import main
open import Data.Fin as Fin using (Fin)
open import Data.Fin.Properties using (inject₁-injective ; suc-injective)
open import Data.Nat as ℕ using (ℕ; _+_) 
open import Data.Vec.Base as Vec using (Vec; []; _∷_)
open import Data.Sum.Base as Sum hiding (map)
open import Data.Bool.Base
import Function.Base


-- ∈-map' : ∀ {i j}{A : Set i}{B : Set j}{a l} → (f : A → B) → a ∈ l → f a ∈ List.map f l
-- ∈-map' f a∈ = ∈-map⁺ f a∈
-- gmap (λ {1ₑ → 1ₑ}) a∈  
-- ∈-map⁺

-- TODO: upload in the standard library
module MoreVec where
  map-insert : ∀ {i j n}{A : Set i}{B : Set j}(f : A → B) k a
         (l : Vec A n) → Vec.map f (Vec.insert l k a) ≡ Vec.insert (Vec.map f l) k (f a)
  map-insert = {!map-∘!}

-- TODO: upload in the standard library
module MoreList where
 module _ {i}{A : Set i} where
  -- like first-index-injective
  index-injective : ∀ {x₁ x₂ : A}{xs} (x₁∈xs : x₁ ∈ xs) (x₂∈xs : x₂ ∈ xs) →
          index x₁∈xs ≡ index x₂∈xs → x₁ ≡ x₂
  index-injective (here e1) (here e2) e = ≡.trans e1 (≡.sym e2)
  index-injective (there x₁∈xs) (there x₂∈xs) e = index-injective x₁∈xs x₂∈xs (suc-injective e)

  open ≡

  -- like remove-inv in  Fresh...
  {-
  remove-inv : ∀ {x y} {xs : List A} (x∈xs : x ∈ xs) →
               y ∈ xs → x ≡ y ⊎ y ∈ (xs ⑊ x∈xs)
  remove-inv (here x≈z)   (here y≈z)   = inj₁ (trans x≈z (sym y≈z))
  remove-inv (here _)     (there y∈xs) = inj₂ y∈xs
  remove-inv (there _)    (here y≈z)   = inj₂ (here y≈z)
  remove-inv (there x∈xs) (there y∈xs) = Sum.map₂ there (remove-inv x∈xs y∈xs)

  -- like ∈-remove in  Fresh/..
  ∈-remove : ∀ {x y} {xs : List A} (x∈xs : x ∈ xs) → y ∈ xs → x ≢ y → y ∈ (xs ⑊ x∈xs)
  ∈-remove x∈xs y∈ys p with remove-inv x∈xs y∈ys
  ... | inj₁ x = ⊥-elim (p x)
  ... | inj₂ y = y
  -}
  -- ∈-remove x∈xs y∈xs x≉y = fromInj₂ (⊥-elim ∘′ x≉y) (remove-inv x∈xs y∈xs)

  _≟∈_ : ∀ {l}{a : A}(a∈ a∈' : a ∈ l) → Dec (a∈ ≡ a∈')
  Ο ≟∈ Ο = yes 1ₑ
  1+ p ≟∈ 1+ p' with p ≟∈ p'
  ... | yes q = yes (cong 1+ q)
  ... | no q = no λ {1ₑ → q 1ₑ}
  Ο ≟∈ 1+ p = no λ ()
  1+ q ≟∈ Ο = no λ ()


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

 open import lc using (_↑ ; commonPositions ; commonPositions-property)
      renaming (_⇒_ to _⇒ᵣ_ ; _∘_ to _∘ᵣ_ ; id to idᵣ)
 infixr 19 _⇒T_
 data Ty n : Set where
   Var : Fin n → Ty n
   _⇒T_ : Ty n → Ty n → Ty n
   ∀T : Ty (1 + n) → Ty n

 ⇒T-injective : ∀ {n}{T T' U U' : Ty n} → (T ⇒T T' ≡ U ⇒T U') → T ≡ U × T' ≡ U'
 ⇒T-injective 1ₑ = 1ₑ , 1ₑ

 ∀T-injective : ∀ {n}{T U : Ty (1 + n)} → (∀T T ≡ ∀T U) → T ≡ U
 ∀T-injective 1ₑ = 1ₑ
 
 Var-injective : ∀ {n}{i j : Fin n} → (Var i ≡ Var j) → i ≡ j
 Var-injective 1ₑ = 1ₑ

 -- following https://github.com/gallais/potpourri/blob/main/agda/poc/LinearDec.agda
 -- https://www.reddit.com/r/Idris/comments/keyki6/decidable_equality_with_many_dataconstructors/
 {-
 module DecidableEqTy where
   open Data.Maybe.Base using (_>>=_)
   eq : ∀ {n} → Ty n → Ty n → Set
   eq (Var x) (Var x') = x ≡ x'
   eq (T₁ ⇒T T₂) (T₁' ⇒T T₂') = eq T₁ T₁' × eq T₂ T₂'
   eq (∀T T) (∀T T') = eq T T'
   eq _ _ = Empty

   eq? : ∀ {n}(T T' : Ty n) → Maybe (eq T T')
   eq? (Var x) (Var x') with x Fin.≟ x'
   ... | yes p = ⌊ p ⌋
   ... | no _ = ⊥
   eq? (T₁ ⇒T T₂) (T₁' ⇒T T₂') = do
       p₁ ← eq? T₁ T₁'
       p₂ ← eq? T₂ T₂'
       ⌊ p₁ , p₂ ⌋
   eq? (∀T T) (∀T T') = do
         p ← eq? T T'
         ⌊ p ⌋
   eq? _ _ = ⊥

   eq?-diag : ∀ {n} (T : Ty n) → Σ (eq T T) (λ x → eq? T T ≡ ⌊ x ⌋)
   eq?-diag (Var x) with (x Fin.≟ x)
   ... | yes p = p , 1ₑ
   ... | no p = ⊥-elim (p 1ₑ)
   eq?-diag (T₁ ⇒T T₂) with
         x1 , e1 ← eq?-diag T₁
       | x2 , e2 ← eq?-diag T₂
        rewrite e1 | e2 = (x1 , x2) , 1ₑ
   eq?-diag (∀T T) with eq?-diag T
   ... | x , e rewrite e = x  , 1ₑ

   eq?-diag⊥ : ∀ {n} {T T' : Ty n} → T ≡ T' → eq? T T' ≢ ⊥
   eq?-diag⊥ {T = T} 1ₑ with x , p ← eq?-diag T rewrite p = λ ()

   _≟_ : ∀ {n} (T T' : Ty n) → Dec (T ≡ T')
   T ≟ T' with eq? T T' in eq
   ... | ⊥ = no λ x → eq?-diag⊥ x eq
   -- then it is necessary that eq is a datatype to be able to pattern-match on it
   ... | ⌊ e ⌋ = {!e!}
   -}

 module DecidableEqTy' where
   open Relation.Nullary.Decidable using (via-injection)
   import Function.Injection
   _≟_ : ∀ {n} (T T' : Ty n) → Dec (T ≡ T')
   Var x ≟ Var x' with x Fin.≟ x'
   ... | yes p = yes (cong Var p)
   ... | no p = no λ e → p (Var-injective e)
   (T₁ ⇒T T₂) ≟ (T₁' ⇒T T₂') with T₁ ≟ T₁' | T₂ ≟ T₂'
   ... | yes e1 | yes e2 = yes (cong₂ _⇒T_ e1 e2)
   ... | _ | no e2 = no (λ x → e2 (proj₂ (⇒T-injective x)))
   ... | no e1 | _ = no (λ x → e1 (proj₁ (⇒T-injective x)))

   ∀T T ≟ ∀T T' with T ≟ T'
   ... | yes p = yes (cong ∀T p)
   ... | no p = no (λ x → p (∀T-injective x))

   Var x ≟ (T' ⇒T T'') = no (λ ())
   Var x ≟ ∀T T' = no (λ ())
   (T₁ ⇒T T₂) ≟ Var x = no (λ ())
   (T₁ ⇒T T₂) ≟ ∀T T' = no (λ ())
   ∀T T₁ ≟ Var x = no (λ ())
   ∀T T₁ ≟ (T' ⇒T T'') = no (λ ())

   


 wkᵣ : ∀ {n} → n ⇒ᵣ (1 + n)
 wkᵣ {n} = Vec.map Fin.inject₁ idᵣ

 _❴_❵ : ∀ {n m} → Ty n → n ⇒ᵣ m → Ty m
 Var x ❴ r ❵ = Var (Vec.lookup r x)
 (T ⇒T T') ❴ r ❵ = T ❴ r ❵ ⇒T (T' ❴ r ❵)
 ∀T T ❴ r ❵ = ∀T (T ❴ r ↑ ❵)

 module _ where
  open Data.Maybe.Base using (_>>=_)
    
  _❴_❵⁻¹ : ∀ {n m} → (t : Ty m) → (x : n ⇒ᵣ m) → Maybe (pre-image (_❴ x ❵) t)
  Var x ❴ r ❵⁻¹ = do
       PreImage x' ← nth⁻¹ Fin._≟_ x r
       ⌊ PreImage (Var x')  ⌋
  (T ⇒T T') ❴ r ❵⁻¹ = do
       PreImage U  ← T  ❴ r ❵⁻¹
       PreImage U' ← T' ❴ r ❵⁻¹
       ⌊  PreImage (U ⇒T U')  ⌋
  ∀T T ❴ r ❵⁻¹ = do
       PreImage T' ← T ❴ r ↑ ❵⁻¹
       ⌊ PreImage (∀T T') ⌋

 _❴_❵s : ∀ {n m} → List (Ty n) → n ⇒ᵣ m → List (Ty m)
 σ ❴ r ❵s = List.map (_❴ r ❵) σ

 -- open ≡.≡.reasoning
 idᵣ↑ : ∀ {n} → idᵣ {n} ↑ ≡ idᵣ
 idᵣ↑ {ℕ.zero} = 1ₑ
 idᵣ↑ {ℕ.suc n} = cong (Fin.zero ∷_)
    (
    begin

    Vec.insert
      (Vec.map Fin.inject₁
       (Vec.tabulate Fin.suc))
      (Fin.fromℕ n) (Fin.suc (Fin.fromℕ n))

     ≡⟨ cong (λ x → Vec.insert x (Fin.fromℕ n) (Fin.suc (Fin.fromℕ n)))
        (≡.trans
         (≡.sym (tabulate-∘ Fin.inject₁ Fin.suc))
         (tabulate-∘ Fin.suc Fin.inject₁)) ⟩

     Vec.insert (Vec.map Fin.suc (Vec.tabulate Fin.inject₁))
      (Fin.fromℕ n) (Fin.suc (Fin.fromℕ n))

     ≡⟨ ≡.sym (MoreVec.map-insert Fin.suc (Fin.fromℕ n) (Fin.fromℕ n) (Vec.tabulate Fin.inject₁)) ⟩

     Vec.map Fin.suc
       (Vec.insert (Vec.tabulate Fin.inject₁)
        (Fin.fromℕ n) (Fin.fromℕ n))

     ≡⟨ cong (λ x → Vec.map Fin.suc (Vec.insert x (Fin.fromℕ n) (Fin.fromℕ n)))
         (tabulate-allFin Fin.inject₁) ⟩

     Vec.map Fin.suc
       (Vec.insert (Vec.map Fin.inject₁ idᵣ)
        (Fin.fromℕ n) (Fin.fromℕ n))

     ≡⟨ cong (Vec.map Fin.suc) (idᵣ↑ {n}) ⟩

     Vec.map Fin.suc (Fin.zero ∷ Vec.tabulate Fin.suc)

     ≡⟨ cong (Fin.suc Fin.zero ∷_) (≡.sym (tabulate-∘ Fin.suc Fin.suc)) ⟩

      Fin.suc Fin.zero ∷
      Vec.tabulate (λ x → Fin.suc (Fin.suc x))
     ∎
     ) where open ≡.≡-Reasoning
    -- idᵣ↑ {n}!}

-- prop
 _❴idᵣ❵ : ∀ {n} → (A : Ty n) → A ❴ idᵣ ❵ ≡ A
 Var x ❴idᵣ❵ = cong Var (lookup-allFin x)
 (A ⇒T B) ❴idᵣ❵ = cong₂ _⇒T_ (A ❴idᵣ❵) (B ❴idᵣ❵)
 ∀T A ❴idᵣ❵ = cong ∀T (≡.trans (cong (A ❴_❵) idᵣ↑) (A ❴idᵣ❵))

 _❴idᵣ❵s : ∀ {n} → (l : List (Ty n)) → l ❴ idᵣ ❵s ≡ l 
 [] ❴idᵣ❵s = 1ₑ
 (x ∷ l) ❴idᵣ❵s = cong₂ _∷_ (x ❴idᵣ❵) (l ❴idᵣ❵s)




 commonPositions↑ : ∀ {n m} → (x y : m ⇒ᵣ n) → let (p , z) = commonPositions m x y in
                       commonPositions (1 + m) (x ↑)(y ↑) ≡ (1 + p , z ↑)
 commonPositions↑ {n} [] [] with Fin.fromℕ n Fin.≟ Fin.fromℕ n
 ... | yes p = 1ₑ
 ... | no p =  ⊥-elim (p ≡.refl)
 commonPositions↑ (x ∷ xs) (y ∷ ys) rewrite commonPositions↑ xs ys with x Fin.≟ y
 ... | yes e rewrite dec-true (Fin.inject₁ x Fin.≟ Fin.inject₁ y) (cong Fin.inject₁ e)
       = let p , _ = commonPositions _ xs ys in
         cong (_ ,_) (cong (_ ∷_) (≡.trans (MoreVec.map-insert Fin.suc _ _ _)
         ((cong (λ x → Vec.insert x (Fin.fromℕ p) _)
           (≡.trans (≡.sym (map-∘ _ _ _)) (map-∘ _ _ _)))
         )))
 ... | no e rewrite dec-false (Fin.inject₁ x Fin.≟ Fin.inject₁ y) (contraposition inject₁-injective e)
   = let p , _ = commonPositions _ xs ys in
     cong (_ ,_) (≡.trans (MoreVec.map-insert Fin.suc _ _ _)
         ((cong (λ x → Vec.insert x (Fin.fromℕ p) _)
           (≡.trans (≡.sym (map-∘ _ _ _)) (map-∘ _ _ _)))
         ))

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
 wkl [] = []
 wkl {σ' = σ'} (x , r) = ∈-map⁺ wkT x , wkl r

 wkl' : ∀ {n a}{σ σ' : List (Ty n)} → σ ⇒ₗ σ' → σ ⇒ₗ (a ∷ σ')
 wkl' r = VecList.map (λ _ → 1+) r

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
    
 open DecidableEqTy' renaming (_≟_ to _≟T_)
 _≟_ : ∀ {n Γ τ} (o o' : O' n Γ τ) → Dec (o ≡ o')

 Var x ≟ Var x' with x MoreList.≟∈ x'
 ... | yes p = yes (cong Var p)
 ... | no p = no (λ { 1ₑ → p 1ₑ })
 App t ≟ App t' with t ≟T t'
 ... | yes p = yes (cong App p)
 ... | no p = no (λ {1ₑ → p 1ₑ})
 Lam τ u 1ₑ ≟ Lam τ' u' 1ₑ with τ ≟T τ' | u ≟T u'
 ... | yes p | yes q = yes 1ₑ
 ... | no p | _ = no λ x → p 1ₑ
 ... | _ | no p = no λ _ → p 1ₑ
 TApp τ₁ τ₂ 1ₑ ≟ TApp τ₁' τ₂' e with τ₁ ≟T τ₁' | τ₂ ≟T τ₂' | e
 ... | yes 1ₑ | yes 1ₑ | 1ₑ = yes 1ₑ
 ... | no p | _ | _ = no λ { 1ₑ  → p 1ₑ}
 ... | _ | no p | _ = no λ { 1ₑ  → p 1ₑ}
 TLam τ₂ 1ₑ ≟ TLam .τ₂ 1ₑ = yes 1ₑ

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



 module PreserveEqualiser
    (equaliser : ∀ {n m} → (x y : m ⇒ᵣ n) → Σ ℕ (λ p → p ⇒ᵣ m))
    (equaliser↑ : ∀ {n m} → (x y : m ⇒ᵣ n) → let (p , z) = equaliser x y in
                       equaliser (x ↑)(y ↑) ≡ (1 + p , z ↑))
    (equaliser-property : ∀ {n m i} → (x y : m ⇒ᵣ n) → Vec.lookup x i ≡ Vec.lookup y i → 
         let (p , z) = equaliser x y in
         i ∈̬ z) where

   commonPositions-inv : ∀ {n m} (x y : m ⇒ᵣ n) → (let p , z = equaliser x y)
         → (τ : Ty m) → τ ❴ x ❵ ≡ τ ❴ y ❵ → pre-image (_❴ z ❵) τ
   commonPositions-inv x y (Var i) e with Var-injective e
   ... | e' with equaliser-property x y e'
   ... | j∈ = Var (index̬ j∈) , cong Var (≡.sym (lookup-index̬ j∈))
   commonPositions-inv x y (T ⇒T T') e with ⇒T-injective e
   ... | e1 , e2 with commonPositions-inv x y T e1 | commonPositions-inv x y T' e2
   ... | PreImage U | PreImage U' = PreImage (U ⇒T U')
   commonPositions-inv x y (∀T T) e with ∀T-injective e
   ... | e' with commonPositions-inv (x ↑) (y ↑) T e'
   ... | U , p rewrite equaliser↑ x y  = (∀T U) , cong ∀T p

   commonPositions-invC : ∀ {n m Γ Γ'} (x y : m ⇒ᵣ n) → (Γ ❴ x ❵s ⇒ₗ Γ')
      → (Γ ❴ y ❵s ⇒ₗ Γ') → 
      (let p , z = equaliser x y) →
      Σ (List (Ty p)) λ Δ → Δ ❴ z ❵s ⇒ₗ Γ
   commonPositions-invC {Γ = []} x y [] [] = [] , []
   -- mimicking the definition of commonPosition
   commonPositions-invC {Γ = m ∷ Γ} x y (t  , ts) (u , us) with
       commonPositions-invC x y ts us | index t Fin.≟ index u
   ... | Δ , s | yes q = do
            p , z ← equaliser x y
            PreImage j  ← commonPositions-inv x y m ( MoreList.index-injective _ _ q)
            j ∷ Δ , Ο , wkl' s
           -- identity do notation for powerful pattern matching (PreImage)
           where open Function.Base using () renaming (_|>′_ to _>>=_)
   ... | Δ , s | no q = Δ ,  wkl' s

 open PreserveEqualiser (λ x y → commonPositions _ x y) commonPositions↑ commonPositions-property
 

 module RenSymbol {n Γ τ n' Γ' τ'} where
  _｛_｝ : O' n Γ τ → (n ∣ Γ ⟶ τ) ⇒ (n' ∣ Γ' ⟶ τ') → O' n' Γ' τ'
  -- o ｛ Hom η x e1 e2 ｝ = {!o!}
  Var i ｛ Hom= η x ｝ = 
       Var ( VecList.nth (∈-map⁺ _❴ η ❵ i) x )
  App τ₂ ｛ Hom= η x ｝ = App (τ₂ ❴ η ❵)
  Lam τ₁ τ₂ e ｛ Hom= η x ｝ = Lam (τ₁ ❴ η ❵) (τ₂ ❴ η ❵) (cong (_❴ η ❵) e)
  TApp τ₁ τ₂ e ｛ Hom= η x ｝ = TApp (τ₁ ❴ η ↑ ❵) (τ₂ ❴ η ❵) {!e!}
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



  equaliser : ∀ (x y : (n ∣ Γ ⟶ τ) ⇒ (n' ∣ Γ' ⟶ τ') ) → Σ A (λ p → p ⇒ (n ∣ Γ ⟶ τ))
  equaliser (Hom= η x) (Hom η' x' 1ₑ e) with commonPositions n η η'
                                          | commonPositions-inv η η' τ (≡.sym e)
                                          | commonPositions-invC η η' x x'
  ... | p , z | τ'' , e' | Δ , x'' = (p ∣ Δ ⟶ τ'') , (Hom z x'' 1ₑ e')

 equaliser : {a : A} (m : A) → m ⇒ a → m ⇒ a → Σ A (λ p → p ⇒ m)
 equaliser {a} m x y = RenSymbol.equaliser x y 

 module _ {n' Γ' τ'} where
  open Data.Maybe.Base using (_>>=_)
  open RenSymbol

  _◄_｛_｝⁻¹ : ∀ {n Γ} τ (o : O' n' Γ' τ') (x : (n ∣ Γ ⟶ τ) ⇒ (n' ∣ Γ' ⟶ τ')) →
      Maybe (pre-image (_｛ x ｝) o)
  τ ◄ Var i ｛ Hom= η x ｝⁻¹ with {! nth⁻¹ Fin._≟_  !}
  ... | e = {!
  Var ( nth⁻¹ Fin._≟_ i x)

  !}
  τ ◄ App t ｛ Hom= η x ｝⁻¹ = do
         PreImage t' ← t ❴ η ❵⁻¹
         ⌊ PreImage (App t') ⌋  
  (τ₁ ⇒T τ₂) ◄ Lam ._ ._ 1ₑ ｛ Hom= η x ｝⁻¹ =
     ⌊  PreImage (Lam τ₁ τ₂ 1ₑ) ⌋
  ∀T τ ◄ TLam ._ 1ₑ ｛ Hom= η x ｝⁻¹ = ⌊ PreImage (TLam τ 1ₑ) ⌋
  τ ◄ TApp τ₁ τ₂ x₁ ｛ Hom= η x ｝⁻¹ = do
              PreImage τ₁' ← τ₁ ❴ η ↑ ❵⁻¹
              PreImage τ₂' ← τ₂ ❴ η ❵⁻¹
              ⌊ (TApp τ₁' τ₂' {!x₁!}) , cong (TApp _ _) {!!} ⌋
              -- what I need to know:
              -- if τ { η } = τ₁' [ τ₂' ] then there eixsts
              -- τ₁ τ₂ preimage of τ₁' and τ₂' such that τ = τ₁ [ τ₂ ]


 
 data O : A → Set where
   op : ∀ {n Γ τ} → O' n Γ τ → O (n ∣ Γ ⟶ τ)
 -- O (n ∣ σ ⟶ τ) = O' n σ τ
 _≟O_ : {a : A} (o o' : O a) → Dec (o ≡ o')
 op x ≟O op y with x ≟ y
 ... | yes p = yes (cong op p)
 ... | no p = no λ { 1ₑ → p 1ₑ}
 

 α : {a : A} → O a → List A
 α (op o) = α' o
 _｛_｝ : {a b : A} → O a → a ⇒ b → O b
 _｛_｝ {n ∣ σ ⟶ τ} {n₁ ∣ σ₁ ⟶ τ₁} (op o) r = op (RenSymbol._｛_｝ o r)
 _^_ : {a b : A} (x : a ⇒ b) (o : O a) → Pointwise _⇒_ (α o) (α (o ｛ x ｝))
 _^_  {n ∣ σ ⟶ τ} {n₁ ∣ σ₁ ⟶ τ₁} r (op o)= RenSymbol._^_ r o

 _｛_｝⁻¹  : {a : A} (o : O a) {b : A} (x : b ⇒ a) → Maybe (pre-image (_｛ x ｝) o)
 op o ｛ x ｝⁻¹ with _◄_｛_｝⁻¹ _ o x
 ... | ⊥ =  ⊥
 ... | ⌊ PreImage o' ⌋ = ⌊ PreImage (op o') ⌋


system-F-sig : Signature lzero lzero lzero
system-F-sig = record
               { System-F 
               }

system-F-friendly : isFriendly system-F-sig
system-F-friendly = record { System-F hiding (_≟_ ) renaming (_≟O_ to _≟_ ) ;
   pullback = {!!}  }
   where open System-F

