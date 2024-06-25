module systemF where

open import Data.List as List hiding (map ; [_] ; lookup)
open import Data.List.Properties as ListProp
open import Data.Empty renaming (⊥ to Empty)
open import Data.List.Relation.Binary.Pointwise using (Pointwise ; [] ; _∷_)
open import Data.Vec.Relation.Binary.Pointwise.Inductive using (Pointwise-≡⇒≡)
open import Data.Product using (_,_ ; _,′_ ; Σ; _×_ ; proj₁ ; proj₂)
open import Data.Maybe.Base using (Maybe) renaming (nothing to ⊥ ; just to ⌊_⌋)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_ ; _≢_ ; cong ; cong₂ ; setoid) renaming (refl to 1ₑ)
open import Relation.Binary.PropositionalEquality.WithK
open import Agda.Primitive
open import Relation.Binary hiding (_⇒_)
open import Data.List.Membership.Propositional 
import Data.List.Membership.Propositional.Properties as ListProp
open import Data.List.Membership.Propositional.Properties using (∈-map⁺ ; ∈-map⁻)
open import Data.Vec.Properties using (lookup-allFin ; map-∘ ; map-cong ; lookup-map ; tabulate-∘ ; tabulate-allFin)
open import Data.Product.Properties using (,-injective)
open import Data.Vec.Membership.Propositional renaming (_∈_ to _∈̬_)
import Data.Vec.Membership.Propositional as VecProp
import Data.Vec.Membership.Propositional.Properties as VecProp
import Data.Vec.Properties as VecProp
open import Data.List.Relation.Unary.Any as Any using (index ; here ; there) renaming (_─_ to _⑊_ )
open import Data.Vec.Relation.Unary.Any using () renaming (index to index̬)
open import Data.Vec.Relation.Unary.Any.Properties using () renaming (lookup-index to lookup-index̬)
import Data.Vec.Relation.Unary.Any.Properties as VecAnyProp

open import Agda.Builtin.Unit
open import Relation.Nullary using (¬_ ; Dec ; yes ; no ; does)
open import Relation.Nullary.Decidable using (dec-yes-irr ; dec-true ; dec-false ; dec-no)
open import Relation.Nullary.Negation.Core using (contraposition)
open import lib 
open import main using (Signature ; isFriendly)
open import Data.Fin as Fin using (Fin)
open import Data.Fin.Properties using (inject₁-injective ; suc-injective)
open import Data.Nat as ℕ using (ℕ; _+_) 
open import Data.Nat.Properties using (+-identityʳ ; +-suc)
open import Data.Vec.Base as Vec using (Vec; []; _∷_)
import Data.Vec.Properties as VecProp
import Data.Vec.Relation.Binary.Equality.Setoid as VecProp hiding (map-++)
open import Data.List.Membership.Setoid.Properties using (index-injective)
open import Data.Sum.Base as Sum hiding (map)
open import Data.Bool.Base
import Function.Base

open import lc using (_↑ ; commonPositions ; commonPositions-property ; commonValues ; commonValues-property)
      renaming (hom to _⇒ᵣ_ ; _∘_ to _∘ᵣ_ ; id to idᵣ)




open VecList using (VecList ; [] ; _,_)
module System-F where

{- ----------------------

Syntax of types

-------------------------- -}
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


 _≟T_ : ∀ {n} (T T' : Ty n) → Dec (T ≡ T')
 Var x ≟T Var x' with x Fin.≟ x'
 ... | yes p = yes (cong Var p)
 ... | no p = no λ e → p (Var-injective e)
 (T₁ ⇒T T₂) ≟T (T₁' ⇒T T₂') with T₁ ≟T T₁' | T₂ ≟T T₂'
 ... | yes e1 | yes e2 = yes (cong₂ _⇒T_ e1 e2)
 ... | _ | no e2 = no (λ x → e2 (proj₂ (⇒T-injective x)))
 ... | no e1 | _ = no (λ x → e1 (proj₁ (⇒T-injective x)))

 ∀T T ≟T ∀T T' with T ≟T T'
 ... | yes p = yes (cong ∀T p)
 ... | no p = no (λ x → p (∀T-injective x))

 Var x ≟T (T' ⇒T T'') = no (λ ())
 Var x ≟T ∀T T' = no (λ ())
 (T₁ ⇒T T₂) ≟T Var x = no (λ ())
 (T₁ ⇒T T₂) ≟T ∀T T' = no (λ ())
 ∀T T₁ ≟T Var x = no (λ ())
 ∀T T₁ ≟T (T' ⇒T T'') = no (λ ())

   



 _❴_❵ : ∀ {n m} → Ty n → n ⇒ᵣ m → Ty m
 Var x ❴ r ❵ = Var (Vec.lookup r x)
 (T ⇒T T') ❴ r ❵ = T ❴ r ❵ ⇒T (T' ❴ r ❵)
 ∀T T ❴ r ❵ = ∀T (T ❴ r ↑ ❵)

 module _ where
  open Data.Maybe.Base using (_>>=_)
    
  _❴_❵⁻¹ : ∀ {n m} → (t : Ty m) → (x : n ⇒ᵣ m) → Maybe (pre-image (_❴ x ❵) t)
  Var x ❴ r ❵⁻¹ = do
       PreImage x' ← MoreVec.lookup⁻¹ Fin._≟_ x r
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

-- weakening
 wkᵣ : ∀ {n} → n ⇒ᵣ (1 + n)
 wkᵣ {n} = Vec.map Fin.inject₁ idᵣ

 wkT : ∀ {n} → Ty n → Ty (1 + n)
 wkT T = T ❴ wkᵣ ❵

 wkC : ∀ {n} → List (Ty n) → List (Ty (1 + n))
 wkC = List.map wkT
 
 _⇒ₛ_ : ℕ → ℕ → Set
 n ⇒ₛ m = Vec (Ty m) n

 _⇑ : ∀ {n m} → n ⇒ₛ m → (1 + n) ⇒ₛ (1 + m)
 σ ⇑ = Vec.insertAt (Vec.map (_❴ Vec.tabulate Fin.inject₁ ❵) σ) (Fin.fromℕ _) (Var (Fin.fromℕ _))


 _⟦_⟧ : ∀ {n m} → Ty n → n ⇒ₛ m → Ty m
 Var x ⟦ σ ⟧ = Vec.lookup σ x
 (τ ⇒T τ') ⟦ σ ⟧ = τ ⟦ σ ⟧ ⇒T τ' ⟦ σ ⟧
 ∀T τ ⟦ σ ⟧ = ∀T (τ ⟦ σ ⇑ ⟧)

 _❴_❵σ : ∀ {n m p} → (σ : n ⇒ₛ m) → (η : m ⇒ᵣ p) → n ⇒ₛ p
 σ ❴ η ❵σ = Vec.map (_❴ η ❵) σ

 _⟦_⟧ᵣ : ∀ {n m p} → (η : n ⇒ᵣ m) → (σ : m ⇒ₛ p) → n ⇒ₛ p
 η ⟦ σ ⟧ᵣ = Vec.map (Vec.lookup σ) η


{- ----------------------

Various substitution properties

-------------------------- -}


 idᵣ↑ : ∀ {n} → idᵣ {n} ↑ ≡ idᵣ
 idᵣ↑ {ℕ.zero} = 1ₑ
 idᵣ↑ {ℕ.suc n} = cong (Fin.zero ∷_)
    (
    begin

    Vec.insertAt
      (Vec.map Fin.inject₁
       (Vec.tabulate Fin.suc))
      (Fin.fromℕ n) (Fin.suc (Fin.fromℕ n))

     ≡⟨ cong (λ x → Vec.insertAt x (Fin.fromℕ n) (Fin.suc (Fin.fromℕ n)))
        (≡.trans
         (≡.sym (tabulate-∘ Fin.inject₁ Fin.suc))
         (tabulate-∘ Fin.suc Fin.inject₁)) ⟩

     Vec.insertAt (Vec.map Fin.suc (Vec.tabulate Fin.inject₁))
      (Fin.fromℕ n) (Fin.suc (Fin.fromℕ n))

     ≡⟨ ≡.sym (VecProp.map-insertAt Fin.suc (Fin.fromℕ n) (Vec.tabulate Fin.inject₁) (Fin.fromℕ n)) ⟩

     Vec.map Fin.suc
       (Vec.insertAt (Vec.tabulate Fin.inject₁)
        (Fin.fromℕ n) (Fin.fromℕ n))

     ≡⟨ cong (λ x → Vec.map Fin.suc (Vec.insertAt x (Fin.fromℕ n) (Fin.fromℕ n)))
         (tabulate-allFin Fin.inject₁) ⟩

     Vec.map Fin.suc
       (Vec.insertAt (Vec.map Fin.inject₁ idᵣ)
        (Fin.fromℕ n) (Fin.fromℕ n))

     ≡⟨ cong (Vec.map Fin.suc) (idᵣ↑ {n}) ⟩

     Vec.map Fin.suc (Fin.zero ∷ Vec.tabulate Fin.suc)

     ≡⟨ cong (Fin.suc Fin.zero ∷_) (≡.sym (tabulate-∘ Fin.suc Fin.suc)) ⟩

      Fin.suc Fin.zero ∷
      Vec.tabulate (λ x → Fin.suc (Fin.suc x))
     ∎
     ) where open ≡.≡-Reasoning

 _❴idᵣ❵ : ∀ {n} → (A : Ty n) → A ❴ idᵣ ❵ ≡ A
 Var x ❴idᵣ❵ = cong Var (lookup-allFin x)
 (A ⇒T B) ❴idᵣ❵ = cong₂ _⇒T_ (A ❴idᵣ❵) (B ❴idᵣ❵)
 ∀T A ❴idᵣ❵ = cong ∀T (≡.trans (cong (A ❴_❵) idᵣ↑) (A ❴idᵣ❵))

 _❴idᵣ❵s : ∀ {n} → (l : List (Ty n)) → l ❴ idᵣ ❵s ≡ l 
 [] ❴idᵣ❵s = 1ₑ
 (x ∷ l) ❴idᵣ❵s = cong₂ _∷_ (x ❴idᵣ❵) (l ❴idᵣ❵s)


 ∘ᵣ↑ : ∀ {p q r} → (x : p ⇒ᵣ q)(y : q ⇒ᵣ r) → (y ∘ᵣ x) ↑ ≡ ((y ↑) ∘ᵣ (x ↑) )
 ∘ᵣ↑ [] y = cong (_∷ []) (≡.sym (VecProp.insertAt-lookup (Vec.map Fin.inject₁ y) (Fin.fromℕ _) (Fin.fromℕ _)))
 ∘ᵣ↑ (x ∷ xs) y rewrite ∘ᵣ↑ xs y = cong (_∷ _)
      (≡.trans (≡.sym (lookup-map x Fin.inject₁ y)) (≡.sym ( MoreVec.insert-lookup-last< x _ _ ))) 

 ❴❵❴❵ : ∀ {p q r} τ (x : p ⇒ᵣ q)(y : q ⇒ᵣ r) → τ ❴ x ❵ ❴ y ❵ ≡ τ ❴ y ∘ᵣ x ❵
 ❴❵❴❵ (Var i) x y = cong Var (≡.sym (lookup-map i (Vec.lookup y) x ))
 ❴❵❴❵ (τ ⇒T τ') x y = cong₂ _⇒T_ (❴❵❴❵ τ x y) (❴❵❴❵ τ' x y)
 ❴❵❴❵ (∀T τ) x y = cong ∀T (≡.trans (❴❵❴❵ τ (x ↑) (y ↑))
     (cong (τ ❴_❵) (≡.sym (∘ᵣ↑ x y))))

 ❴❵❴❵s : ∀ {p q r} σ (x : p ⇒ᵣ q)(y : q ⇒ᵣ r) → (σ ❴ x ❵s) ❴ y ❵s ≡ σ ❴ y ∘ᵣ x ❵s
 ❴❵❴❵s σ x y = ≡.trans (≡.sym ( ListProp.map-∘ σ ))
      (ListProp.map-cong (λ τ → ❴❵❴❵ τ x y) σ) 

 ↑∘ᵣinject₁ : ∀ {m p} (η : m ⇒ᵣ p) →
      (η ↑) ∘ᵣ (Vec.tabulate Fin.inject₁) ≡ (Vec.tabulate Fin.inject₁ ∘ᵣ η)
 ↑∘ᵣinject₁ η rewrite ≡.sym (VecProp.tabulate-∘ (Vec.lookup ( η ↑) ) Fin.inject₁ )
    | VecProp.map-cong (VecProp.lookup∘tabulate Fin.inject₁) η
    = ≡.trans (VecProp.tabulate-cong λ x → MoreVec.insert-lookup-last< x (Fin.fromℕ _)
                (Vec.map Fin.inject₁ η)
        ) (≡.trans (VecProp.tabulate-cong (λ x → lookup-map x Fin.inject₁ η))
          (≡.trans (tabulate-∘ Fin.inject₁ (Vec.lookup η))
          (cong (Vec.map Fin.inject₁) (VecProp.tabulate∘lookup η))))


 ❴❵⇑ : ∀ {n m p} (η : m ⇒ᵣ p) (σ : n ⇒ₛ m)
      → ((σ ❴ η ❵σ) ⇑)  ≡ ((σ ⇑) ❴ η ↑ ❵σ)
 ❴❵⇑ {n}{m}{p} η σ
   rewrite VecProp.map-insertAt (_❴ η ↑ ❵) (Var (Fin.fromℕ m)) (σ ❴ Vec.tabulate Fin.inject₁ ❵σ) (Fin.fromℕ n)
   | VecProp.insertAt-lookup (Vec.map Fin.inject₁ η) (Fin.fromℕ _)(Fin.fromℕ _)
   | ≡.sym (VecProp.map-∘ (_❴ η ↑ ❵)(_❴ Vec.tabulate Fin.inject₁ ❵) σ)
   | ≡.sym (VecProp.map-∘ (_❴ Vec.tabulate Fin.inject₁ ❵)(_❴ η ❵) σ)
   = cong (λ xi → Vec.insertAt xi (Fin.fromℕ _) _)
     (VecProp.map-cong (λ x → ≡.trans (❴❵❴❵ x η _)
       (≡.sym (≡.trans (❴❵❴❵ x _ _)
       (cong (x ❴_❵) (↑∘ᵣinject₁ η))))) σ)

 ⟦⟧⇑ : ∀ {n m p} (η : n ⇒ᵣ m) (σ : m ⇒ₛ p)
      → 
    ((η ⟦ σ ⟧ᵣ) ⇑) ≡ ((η ↑) ⟦ σ ⇑ ⟧ᵣ)
 ⟦⟧⇑ {n}{m}{p} η σ
   rewrite VecProp.map-insertAt (Vec.lookup (σ ⇑)) (Fin.fromℕ _) (Vec.map Fin.inject₁ η) (Fin.fromℕ _)
   | VecProp.insertAt-lookup (σ ❴ Vec.tabulate Fin.inject₁ ❵σ) (Fin.fromℕ _)(Var (Fin.fromℕ p))
   | ≡.sym (VecProp.map-∘ (Vec.lookup (σ ⇑)) Fin.inject₁ η)
   | VecProp.map-cong  (λ x → MoreVec.insert-lookup-last< x (Var (Fin.fromℕ _)) (σ ❴ Vec.tabulate Fin.inject₁ ❵σ)) η
   | ≡.sym (VecProp.map-∘ _❴ Vec.tabulate Fin.inject₁ ❵ (Vec.lookup σ) η)
   = cong (λ xi → Vec.insertAt xi (Fin.fromℕ _) _)
      (VecProp.map-cong (λ x → ≡.sym (VecProp.lookup-map x (_❴ Vec.tabulate Fin.inject₁ ❵) σ)) η)

 ⟦⟧❴❵ : ∀ {n m p} → (τ : Ty n) → (σ : n ⇒ₛ m) → (η : m ⇒ᵣ p)
       → τ ⟦ σ ⟧ ❴ η ❵ ≡ (τ ⟦ σ ❴ η ❵σ ⟧)
 ⟦⟧❴❵ (Var x) σ η = ≡.sym (lookup-map x _❴ η ❵ σ)
 ⟦⟧❴❵ (τ ⇒T τ') σ η = cong₂ _⇒T_ (⟦⟧❴❵ τ σ η) (⟦⟧❴❵ τ' σ η)
 ⟦⟧❴❵ (∀T τ) σ η = cong ∀T (≡.trans (⟦⟧❴❵ τ (σ ⇑) (η ↑)) (cong (τ ⟦_⟧) (≡.sym (❴❵⇑ η σ))))

 ❴❵⟦⟧ : ∀ {n m p} → (τ : Ty n) → (η : n ⇒ᵣ m) (σ : m ⇒ₛ p)
       → (τ  ❴ η ❵) ⟦ σ ⟧ ≡ (τ ⟦ η ⟦ σ ⟧ᵣ ⟧)
 ❴❵⟦⟧ (Var x) σ η = ≡.sym (lookup-map x (Vec.lookup η) σ)
 ❴❵⟦⟧ (τ ⇒T τ') σ η = cong₂ _⇒T_ (❴❵⟦⟧ τ σ η) (❴❵⟦⟧ τ' σ η)
 ❴❵⟦⟧ (∀T τ) η σ = cong ∀T ((≡.trans (❴❵⟦⟧ τ (η ↑)(σ ⇑) ) (cong (τ ⟦_⟧) (≡.sym (⟦⟧⇑ η σ)))))

 -- replace the last variable with the given argument, living the other untouched
 last↦_ : ∀ {n } → Ty n → (1 + n) ⇒ₛ n
 last↦ τ = Vec.insertAt (Vec.tabulate Var) (Fin.fromℕ _) τ

 -- unary substitution
 _[_] : ∀ {n} → Ty (1 + n) → Ty n → Ty n
 τ₁ [ τ₂ ] = τ₁ ⟦ last↦ τ₂ ⟧

 lookup-last↦-inject₁ : ∀ {n n'} (τ₂ : Ty n) (η  : n ⇒ᵣ n') x
    → Vec.lookup (last↦ (τ₂ ❴ η ❵)) (Fin.inject₁ x) ≡ Var x
 lookup-last↦-inject₁ τ₂ η x rewrite MoreVec.insert-lookup-last< x (τ₂ ❴ η ❵) (Vec.tabulate Var)
      = VecProp.lookup∘tabulate Var x
 

 last↦❴❵ : ∀ {n n'} (τ₂ : Ty n) (η : n ⇒ᵣ n')
        → ((last↦ τ₂) ❴ η ❵σ) ≡ ((η ↑) ⟦ last↦ (τ₂ ❴ η ❵) ⟧ᵣ)
 last↦❴❵ τ₂ η
    rewrite VecProp.map-insertAt _❴ η ❵ τ₂ (Vec.tabulate Var) (Fin.fromℕ _)
      | ≡.sym (tabulate-∘ _❴ η ❵ Var )
      | VecProp.map-insertAt (Vec.lookup (last↦ (τ₂ ❴ η ❵))) (Fin.fromℕ _) (Vec.map Fin.inject₁ η) (Fin.fromℕ _)
      | ≡.sym (VecProp.map-∘ (Vec.lookup (last↦ (τ₂ ❴ η ❵))) Fin.inject₁ η)
      | VecProp.insertAt-lookup (Vec.tabulate Var) (Fin.fromℕ _) (τ₂ ❴ η ❵)
      | VecProp.map-cong {f = λ xi → Vec.lookup (last↦ (τ₂ ❴ η ❵)) (Fin.inject₁ xi) }{g = Var}
           (λ x → lookup-last↦-inject₁ τ₂ η x)

           η
      | tabulate-∘ Var (Vec.lookup η)
      | VecProp.tabulate∘lookup η
     = 1ₑ

 []❴❵ : ∀ {n n'} (τ₁ : Ty (1 + n))(τ₂ : Ty n) (η  : n ⇒ᵣ n') → 
          ((τ₁ [ τ₂ ]) ❴ η ❵) ≡ ((τ₁ ❴ η ↑ ❵) [ τ₂ ❴ η ❵ ])
 []❴❵ τ₁ τ₂ η =
    ≡.trans (⟦⟧❴❵ τ₁ (last↦ τ₂) η )
    (≡.trans (cong (τ₁ ⟦_⟧) (last↦❴❵ τ₂ η))
    (≡.sym (❴❵⟦⟧ τ₁ (η ↑) (last↦ (τ₂ ❴ η ❵)) )))

 ❴❵-wkT : ∀ {n n'} (T : Ty n)(η : n ⇒ᵣ n') → wkT (T ❴ η ❵) ≡ ((wkT T) ❴ η ↑ ❵)
 wkᵣ∘ᵣ : ∀ {n n'} (η : n ⇒ᵣ n') → wkᵣ ∘ᵣ η ≡ (η ↑ ) ∘ᵣ wkᵣ 

 ❴❵-wkT T η = ≡.trans (❴❵❴❵ T η wkᵣ) (≡.trans (cong (T ❴_❵) (wkᵣ∘ᵣ η)) (≡.sym (❴❵❴❵ T wkᵣ (η ↑))))



 

 ∘ᵣidᵣ : ∀ {n n'} (η : n ⇒ᵣ n') → η ∘ᵣ idᵣ ≡ η
 ∘ᵣidᵣ η = VecProp.map-lookup-allFin η 

 idᵣ∘ᵣ : ∀ {n n'} (η : n ⇒ᵣ n') → idᵣ ∘ᵣ η ≡ η
 idᵣ∘ᵣ η = ≡.trans (VecProp.map-cong (λ x → VecProp.lookup∘tabulate _ x ) _)
            (VecProp.map-id η)

 wkᵣ∘ᵣ η = ≡.trans (≡.trans (≡.trans
            (VecProp.map-cong (λ x → lookup-map _ Fin.inject₁ idᵣ ) _)
           (≡.trans (≡.trans (VecProp.map-∘ Fin.inject₁ (Vec.lookup idᵣ) _)
            (≡.sym ((≡.trans (VecProp.map-∘ Fin.inject₁ (Vec.lookup η) _)
                 (cong (Vec.map Fin.inject₁) (≡.trans (∘ᵣidᵣ η) (≡.sym (idᵣ∘ᵣ η))))))))
           (VecProp.map-cong (λ x → ≡.sym (lookup-map x Fin.inject₁ η)) idᵣ)))
           (VecProp.map-cong (λ x → ≡.sym (MoreVec.insert-lookup-last< x _ _)) _))
           -- tabulate-allFin      -- 
         (VecProp.map-∘ _ Fin.inject₁ idᵣ )



 ❴❵-wkC : ∀ {n n'}(Γ : List (Ty n)) (η : n ⇒ᵣ n') →
       (wkC Γ ❴ η ↑ ❵s) ≡ wkC (Γ ❴ η ❵s)
 ❴❵-wkC Γ η = ≡.trans (≡.sym (ListProp.map-∘ Γ))
            (≡.trans
            (ListProp.map-cong (λ τ →
               ≡.trans (❴❵❴❵ τ _ _)
               (≡.trans (cong (τ ❴_❵) (≡.sym (wkᵣ∘ᵣ η))) (≡.sym (❴❵❴❵ τ _ _))))
            _)
            (ListProp.map-∘ Γ)
            )

{- ----------------------

The category of arities

-------------------------- -}


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
 l1 ∘ₗ (x , l2) = VecList.lookup l1 x , (l1 ∘ₗ l2)

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
 Hom= η x ∘ Hom= η' x' = Hom (η ∘ᵣ η') (x ∘ₗ (x' ❴ η ❵l)) (≡.sym (❴❵❴❵s _ η' η)) (≡.sym (❴❵❴❵ _ η' η))

{- ----------------------

Indexed set of symbols with their arities

-------------------------- -}
 data O' n Γ τ : Set where
   Var : τ ∈ Γ → O' n Γ τ
   App : Ty n → O' n Γ τ
   Lam : ∀ τ₁ τ₂ → τ ≡ τ₁ ⇒T τ₂ → O' n Γ τ
   TApp : ∀ (τ₁ : Ty (1 + n))(τ₂ : Ty n) → τ ≡ τ₁ [ τ₂ ] → O'  n Γ τ
   TLam : ∀ τ' → τ ≡ ∀T τ' → O' n Γ τ

 module _ {n Γ τ} where
   α : O' n Γ τ → List A
   α (Var x) = []
   α (App τ') = (n ∣ Γ ⟶ (τ' ⇒T τ)) ∷ (n ∣ Γ ⟶ τ') ∷ []
   α (Lam τ₁ τ₂ x) = n ∣ (τ₁ ∷ Γ) ⟶ τ₂ ∷ []
   α (TApp τ₁ τ₂ x) = n ∣ Γ ⟶ (∀T τ₁) ∷ []
   α (TLam τ' x) = (1 + n) ∣ wkC Γ ⟶ τ' ∷ []

 O : A → Set
 O a = O' (A.n a) (A.σ a) (A.τ a)

 module _ {n Γ τ n' Γ' τ'} where
  _｛_｝ : O' n Γ τ → (n ∣ Γ ⟶ τ) ⇒ (n' ∣ Γ' ⟶ τ') → O' n' Γ' τ'
  -- o ｛ Hom η x e1 e2 ｝ = {!o!}
  Var i ｛ Hom= η x ｝ = 
        Var ( VecList.lookup x (∈-map⁺ _❴ η ❵ i) ) 
  App τ₂ ｛ Hom= η x ｝ = App (τ₂ ❴ η ❵)
  Lam τ₁ τ₂ e ｛ Hom= η x ｝ = Lam (τ₁ ❴ η ❵) (τ₂ ❴ η ❵) (cong (_❴ η ❵) e)
  TApp τ₁ τ₂ e ｛ Hom= η x ｝ = TApp (τ₁ ❴ η ↑ ❵) (τ₂ ❴ η ❵) e'
     where
       e' : τ ❴ η ❵ ≡ τ₁ ❴ η ↑ ❵ [ τ₂ ❴ η ❵ ]
       e' = ≡.trans (cong _❴ η ❵ e) ([]❴❵ τ₁ τ₂ η)
  TLam τ' 1ₑ ｛ Hom= η x ｝ = TLam (τ' ❴ η ↑ ❵) 1ₑ

  _^_ : (r : (n ∣ Γ ⟶ τ) ⇒ (n' ∣ Γ' ⟶ τ')) → (o : O' n Γ τ) → 
            Pointwise _⇒_ (α o) (α (o ｛ r ｝))
  Hom= η x ^ Var i = []
  Hom= η x ^ App _ =
     Hom= η x ∷
     Hom= η x ∷ []
  Hom= η x ^ Lam τ₁ τ₂ 1ₑ =
     Hom η (Ο , VecList.map (λ a x₁ → 1+ x₁) x) 1ₑ 1ₑ ∷ []
  Hom= η x ^ TApp τ₁ τ₂ 1ₑ = 
    Hom= η x ∷ []
     
  Hom= η x ^ TLam τ' 1ₑ =
    Hom (η ↑) (wkl x) (❴❵-wkC _ η) 1ₑ
     ∷ []

 module _ {n' Γ' τ'} where
  open Data.Maybe.Base using (_>>=_)

  _◄_｛_｝⁻¹ : ∀ {n Γ} τ (o : O' n' Γ' τ') (x : (n ∣ Γ ⟶ τ) ⇒ (n' ∣ Γ' ⟶ τ')) →
      Maybe (pre-image (_｛ x ｝) o)
  τ ◄ Var i ｛ Hom= η x ｝⁻¹ with VecList.lookup⁻¹ _≟T_ MoreList._≟∈_ i x
  ... | ⊥ = ⊥
  ... | ⌊ PreImage i' ⌋ with ∈-map⁻ _❴ η ❵ i' | MoreList.∈-map⁺-map⁻ {ℓ' = lzero} _❴ η ❵ i' 
  ... | τ' , i'' , e | e' with τ' ≟T τ | e | e'
       -- if we restrict to an injective renaming η,
       -- they should always be equal because
       -- they have the same image by _❴ η ❵
  ... | no _ | _ | _ = ⊥
  ... | yes 1ₑ | 1ₑ | 1ₑ = ⌊ Var i'' , 1ₑ ⌋
  τ ◄ App t ｛ Hom= η x ｝⁻¹ = do
         PreImage t' ← t ❴ η ❵⁻¹
         ⌊ PreImage (App t') ⌋  
  (τ₁ ⇒T τ₂) ◄ Lam ._ ._ 1ₑ ｛ Hom= η x ｝⁻¹ =
     ⌊  PreImage (Lam τ₁ τ₂ 1ₑ) ⌋
  ∀T τ ◄ TLam ._ 1ₑ ｛ Hom= η x ｝⁻¹ = ⌊ PreImage (TLam τ 1ₑ) ⌋
  τ ◄ TApp τ₁' τ₂' x₁ ｛ Hom= η x ｝⁻¹ = do
              PreImage τ₁ ← τ₁' ❴ η ↑ ❵⁻¹
              PreImage τ₂ ← τ₂' ❴ η ❵⁻¹
              yes p  ← ⌊ (τ ≟T (τ₁ [ τ₂ ])) ⌋
              -- if we restrict to an injective renaming η,
              -- they should always be equal because
              -- they have the same image by _❴ η ❵
                  where no _ → ⊥
              ⌊ TApp τ₁ τ₂ p ,  cong (TApp (τ₁ ❴ η ↑ ❵) (τ₂ ❴ η ❵)) (≡-irrelevant _ _)  ⌋

 _｛_｝⁻¹  : {a : A} (o : O a) {b : A} (x : b ⇒ a) → Maybe (pre-image (_｛ x ｝) o)
 o ｛ x ｝⁻¹ = _ ◄ o ｛ x ｝⁻¹

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





{- ----------------------

Equalisers (based on commonPositions)

-------------------------- -}

 commonPositions↑ : ∀ {n m} → (x y : m ⇒ᵣ n) → let (p , z) = commonPositions m x y in
                       commonPositions (1 + m) (x ↑)(y ↑) ≡ (1 + p , z ↑)
 commonPositions↑ {n} [] [] with Fin.fromℕ n Fin.≟ Fin.fromℕ n
 ... | yes p = 1ₑ
 ... | no p =  ⊥-elim (p ≡.refl)
 commonPositions↑ (x ∷ xs) (y ∷ ys) rewrite commonPositions↑ xs ys with x Fin.≟ y
 ... | yes e rewrite dec-true (Fin.inject₁ x Fin.≟ Fin.inject₁ y) (cong Fin.inject₁ e)
       = let p , _ = commonPositions _ xs ys in
         cong (_ ,_) (cong (_ ∷_) (≡.trans (VecProp.map-insertAt Fin.suc _ _ _)
         ((cong (λ x → Vec.insertAt x (Fin.fromℕ p) _)
           (≡.trans (≡.sym (VecProp.map-∘ _ _ _)) (VecProp.map-∘ _ _ _)))
         )))
 ... | no e rewrite dec-false (Fin.inject₁ x Fin.≟ Fin.inject₁ y) (contraposition inject₁-injective e)
   = let p , _ = commonPositions _ xs ys in
     cong (_ ,_) (≡.trans (VecProp.map-insertAt Fin.suc _ _ _)
         ((cong (λ x → Vec.insertAt x (Fin.fromℕ p) _)
           (≡.trans (≡.sym (VecProp.map-∘ _ _ _)) (VecProp.map-∘ _ _ _)))
         ))

 equaliser-Ty : ∀ {n m} (x y : m ⇒ᵣ n) → (let p , z = commonPositions _ x y)
       → (τ : Ty m) → τ ❴ x ❵ ≡ τ ❴ y ❵ → pre-image (_❴ z ❵) τ
 equaliser-Ty x y (Var i) e with commonPositions-property x y (Var-injective e)
 ... | j∈ = Var (index̬ j∈) , cong Var (≡.sym (lookup-index̬ j∈))
 equaliser-Ty x y (T ⇒T T') e = do
       e1 , e2 ← ⇒T-injective e
       PreImage U  ← equaliser-Ty x y T  e1
       PreImage U' ← equaliser-Ty x y T' e2
       PreImage (U ⇒T U')
    where open Function.Base using () renaming (_|>′_ to _>>=_)

 equaliser-Ty x y (∀T T) e with ∀T-injective e
 ... | e' with equaliser-Ty (x ↑) (y ↑) T e'
 ... | U , p rewrite commonPositions↑ x y  = (∀T U) , cong ∀T p

 equaliser-context : ∀ {n m Γ Γ'} (x y : m ⇒ᵣ n) → (Γ ❴ x ❵s ⇒ₗ Γ')
    → (Γ ❴ y ❵s ⇒ₗ Γ') → 
    (let p , z = commonPositions _ x y) →
    Σ (List (Ty p)) λ Δ → Δ ❴ z ❵s ⇒ₗ Γ
    
 equaliser-context {Γ = []} x y [] [] = [] , []
 -- mimicking the definition of commonPosition
 equaliser-context {Γ = m ∷ Γ} x y (t  , ts) (u , us) with
     equaliser-context x y ts us | index t Fin.≟ index u
 ... | Δ , s | yes q 
       with PreImage j  ← equaliser-Ty x y m (index-injective (setoid _) _ _ q)
       = j ∷ Δ , Ο , wkl' s
 ... | Δ , s | no q = Δ ,  wkl' s
 equaliser : {a : A} (m : A) → m ⇒ a → m ⇒ a → Σ A (λ p → p ⇒ m)
 equaliser _ (Hom {τ = τ} η x 1ₑ 1ₑ) (Hom η' x' 1ₑ e) with commonPositions _ η η'
                                           | equaliser-Ty η η' τ (≡.sym e)
                                           | equaliser-context η η' x x'
 ... | p , z | τ'' , e' | Δ , x'' = (p ∣ Δ ⟶ τ'') , (Hom z x'' 1ₑ e')


{- ----------------------

Pullbacks (based on commonValues)

-------------------------- -}

    

 private

  helper-≡ : ∀ {i j}{A : Set i}{B : Set j} → (abc abc' : Σ ℕ (λ n → (Vec A n × Vec B n)))
     → (let a , b , c = abc)
     → (let a' , b' , c' = abc')
     → Vec.toList b ≡ Vec.toList b'
     → Vec.toList c ≡ Vec.toList c'
     → abc ≡ abc'
  helper-≡ (.ℕ.zero , [] , []) (.ℕ.zero , [] , []) = λ x x₁ → 1ₑ
  helper-≡ (.(ℕ.suc _) , b0 ∷ b , c) (.ℕ.zero , [] , c') () e'
  helper-≡ (.(ℕ.suc _) , b0 ∷ b , c0 ∷ c) (.(ℕ.suc _) , b0' ∷ b' , c0' ∷ c') e e' 
     with helper-≡ (_ , b , c) (_ , b' , c') (∷-injectiveʳ e) (∷-injectiveʳ e')  
  ... | 1ₑ rewrite ∷-injectiveˡ e | ∷-injectiveˡ e' = 1ₑ
  helper2 :  ∀ {i}{A : Set i}{n n' m m'}(xs : Vec A n)(xs' : Vec A n'){ys : Vec A m}{ys' : Vec A m'} →
                        Vec.toList xs ≡ Vec.toList xs'
                      → Vec.toList ys ≡ Vec.toList ys' →
                  Vec.toList (xs Vec.++ ys) ≡ Vec.toList (xs' Vec.++ ys')
  helper2 [] [] e1 e2 = e2
  helper2 (x ∷ xs) (x₁ ∷ xs') e1 e2 =
     cong₂ _∷_ (∷-injectiveˡ e1) (helper2 xs xs' (∷-injectiveʳ e1) e2 )

 commonValues↑ : ∀ {n m m'} → (x : m ⇒ᵣ n)(y : m' ⇒ᵣ n) → let (p , l , r) = commonValues m x y in
                    commonValues (1 + m) (x ↑)(y ↑) ≡ (1 + p , l ↑ , r ↑)

 commonValues↑ {n}{m}{m'} [] ys
   rewrite MoreVec.find-indices-insert-last (Fin._≟ Fin.fromℕ n) (Vec.map Fin.inject₁ ys)  1ₑ
   | MoreVec.find-indices-0 (Fin._≟ Fin.fromℕ n) (Vec.map Fin.inject₁ ys)
     λ x eq → MoreFin.inject₁-≢-fromℕ _
        (≡.trans (≡.sym (proj₂ (proj₂ (VecProp.find (VecAnyProp.map⁻ x))))) eq)
    = 1ₑ
 commonValues↑ {n} (_∷_ {m} x xs) ys rewrite commonValues↑ xs ys
   | MoreVec.find-indices-insert-last-⊥ (Fin._≟ Fin.inject₁ x) (Vec.map Fin.inject₁ ys) {a = Fin.fromℕ _}
     ( λ e → MoreFin.inject₁-≢-fromℕ _ (≡.sym e))
   with p , l , r ← commonValues _ xs ys
   with indices ← (MoreVec.find-indices (Fin._≟ x) ys) in eq_indices
   with vindices ← Vec.fromList indices in eq_vindices
   with zeros1 ← (Vec.replicate (List.length (List.map Fin.inject₁ (MoreVec.find-indices (Fin._≟ Fin.inject₁ x) (Vec.map Fin.inject₁ ys)))) (Fin.zero {n = 1 + m})) in eq_zeros1
   with zeros2 ← (Vec.replicate (List.length indices) (Fin.zero {n = m})) in eq_zeros2
    rewrite  (VecProp.map-++ Fin.inject₁ zeros2 (Vec.map Fin.suc l))
   |         (VecProp.map-++ Fin.inject₁ vindices r)
   -- ptet faut echanger la
   |      VecProp.map-insertAt Fin.suc (Fin.fromℕ m)(Vec.map Fin.inject₁ l) (Fin.fromℕ p)
   |   ≡.sym (   VecProp.map-∘ Fin.suc Fin.inject₁ l)
   with zeros2' ← Vec.map Fin.inject₁ zeros2 in eq_zeros2'
   = helper-≡ _ _
       (≡.trans
        (helper2 zeros1 zeros2'
          (≡.trans (≡.sym (cong Vec.toList eq_zeros1))
          (≡.trans (
          ≡.trans (≡.trans (MoreVec.toList-replicate _ _)
          (≡.trans (≡.trans (cong (λ xi → replicate xi _)
            (≡.trans (cong (λ xi → length (List.map Fin.inject₁ xi)) eq-aux)
            ( ListProp.length-map Fin.inject₁ indices )))
          (≡.sym (ListProp.map-replicate _ _ _)))
          (≡.sym (≡.cong (List.map _) (MoreVec.toList-replicate _ _))))
          )
          (≡.sym (VecProp.toList-map _ _))
          )
          (cong Vec.toList (≡.trans (≡.cong (Vec.map _) eq_zeros2) eq_zeros2')))
          )
          (cong (λ xi → Vec.toList (Vec.insertAt xi _ _))
             (VecProp.map-∘ Fin.inject₁ Fin.suc l)))
        (≡.sym (MoreVec.insert-last-++ zeros2' (Vec.map Fin.inject₁ (Vec.map Fin.suc l)) (Fin.fromℕ _))))
      (≡.trans
        (helper2
               (Vec.fromList
               (List.map Fin.inject₁
                 (MoreVec.find-indices (Fin._≟ Fin.inject₁ x)
                 (Vec.map Fin.inject₁ ys))))
               (Vec.map Fin.inject₁ vindices)
          (≡.trans (VecProp.toList∘fromList _)
          (≡.trans (cong (List.map _)
          (≡.trans (≡.trans eq-aux
            (≡.sym (VecProp.toList∘fromList indices))) (cong Vec.toList eq_vindices)))
          (≡.sym (VecProp.toList-map Fin.inject₁ vindices)))
          )
          1ₑ)
        (≡.sym (MoreVec.insert-last-++ (Vec.map Fin.inject₁ vindices) (Vec.map Fin.inject₁ r) (Fin.fromℕ _) ))
        
              )
    where
      eq-aux : MoreVec.find-indices (Fin._≟ Fin.inject₁ x)
          (Vec.map Fin.inject₁ ys) ≡ indices

      eq-aux = ≡.trans (MoreVec.find-indices-map⁻
               (Fin._≟ _)(Fin._≟ _) Fin.inject₁ (cong Fin.inject₁) inject₁-injective ys)
               eq_indices

 pullback-Ty : ∀ {m m' n} (x : m ⇒ᵣ n)(y : m' ⇒ᵣ n) → (let p , l , r = commonValues _ x y)
         → (τ : Ty m) → (τ' : Ty m') → τ ❴ x ❵ ≡ τ' ❴ y ❵
         → pre-image (λ t → t ❴ l ❵ ,′ t ❴ r ❵) (τ ,′ τ')
 pullback-Ty x y (Var x₁) (Var x₂) eq
    with commonValues-property _ _
            (≡.subst (_∈̬ _) (Var-injective eq) (VecProp.∈-lookup x₁ x)) (VecProp.∈-lookup x₂ y)
 ... | ∈2 =
    let p , l , r = commonValues _ x y in
    let e = ≡.trans (VecAnyProp.lookup-index ∈2) (VecProp.lookup-zip (index̬ ∈2 ) l r) in
    let p1 , p2 = ,-injective (≡.sym e) in
    Var (index̬ ∈2) , 
               cong₂ (λ x y → Var x , Var y) (≡.trans p1 aux)
               (≡.trans p2 (VecProp.index-∈-lookup x₂ y))
      where
         open ≡.≡-Reasoning
         aux =
           begin
             index̬ (≡.subst (_∈̬ x) (Var-injective eq) (VecProp.∈-lookup x₁ x))
               ≡⟨ index̬-subst _ _ (Var-injective eq) ⟩
             index̬ (VecProp.∈-lookup x₁ x)
               ≡⟨ VecProp.index-∈-lookup x₁ x ⟩
             x₁
           ∎
           where
            index̬-subst : ∀ {i}{A : Set i}{n} → (l : Vec A n)
                → ∀ {a a' : A}(a∈ : a ∈̬ l)(ea : a ≡ a')
                → index̬ (≡.subst (_∈̬ l) ea a∈) ≡ index̬ a∈
            index̬-subst l a∈ 1ₑ = 1ₑ

 pullback-Ty x y (T ⇒T U) (T' ⇒T U') eq = do
        e1 , e2 ← ⇒T-injective eq
        PreImage T''  ← pullback-Ty x y T T'  e1
        PreImage U'' ← pullback-Ty x y U U' e2
        PreImage (T'' ⇒T U'')
     where open Function.Base using () renaming (_|>′_ to _>>=_)
 pullback-Ty x y (∀T τ) (∀T τ') e with ∀T-injective e
 ... | e' with pullback-Ty (x ↑) (y ↑) τ τ' e'
 ... | U , p rewrite commonValues↑ x y = ∀T U  , cong (λ {( a , b) → ∀T a , ∀T b}) p


 pullback-context : ∀ {n m m' Γ₁ Γ₂ Γ'} (x : m ⇒ᵣ n)(y : m' ⇒ᵣ n) → (Γ₁ ❴ x ❵s ⇒ₗ Γ')
     → (Γ₂ ❴ y ❵s ⇒ₗ Γ') → 
     (let p , l , r = commonValues _ x y) →
     Σ (List (Ty p)) λ Δ → (Δ ❴ l ❵s ⇒ₗ Γ₁ × Δ ❴ r ❵s ⇒ₗ Γ₂ )
 pullback-context {Γ₁ = []} x y [] us = [] , [] , []
 -- to simplify, we assume that the morphisms are injective
 -- contrary to the general definition of commonValues
 pullback-context {Γ₁ = γ ∷ Γ₁} x y (t , ts) us with
     pullback-context x y ts us
 ... | Δ , s₁ , s₂ with s₁' ← VecList.map (λ _ → 1+) s₁ | VecList.lookup⁻¹  _≟T_ MoreList._≟∈_ t us
 ... | ⊥ = Δ , s₁' , s₂
 ... | ⌊ u , e ⌋ 
     with j , j∈Γ₂ , ej ← ∈-map⁻ _ u
     with PreImage xi ← pullback-Ty x y γ j ej 
       = (xi ∷ Δ) , (Ο , s₁') , (j∈Γ₂ , s₂)


 pullback : (m : A) {m' a : A} → m ⇒ a → m' ⇒ a → Σ A (λ p → (p ⇒ m) × (p ⇒ m'))
 pullback (n ∣ σ ⟶ τ) {n₁ ∣ σ₁ ⟶ τ₁} {n₂ ∣ σ₂ ⟶ τ₂} (Hom= η x) (Hom η' x' 1ₑ e)
    with commonValues _ η η'
       | pullback-Ty η η' τ τ₁ (≡.sym e)
       | pullback-context η η' x x'
 ... | p , l , r | PreImage τ' | Δ , s₁ , s₂ =
          (p ∣ Δ ⟶ τ') , (Hom= l s₁ , Hom= r s₂)



system-F-sig : Signature lzero lzero lzero
system-F-sig = record { System-F }

system-F-friendly : isFriendly system-F-sig
system-F-friendly = record { System-F }
