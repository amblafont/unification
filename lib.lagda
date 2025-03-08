\begin{code}
module lib where

open import Data.Vec.Base as Vec using (Vec; []; _∷_)
open import Data.Vec.Membership.Propositional using () renaming (_∈_ to _∈̬_ )
import Data.Vec.Membership.Propositional.Properties as VecProp
import Data.Vec.Relation.Unary.Any.Properties as VecProp
open import Data.Vec.Relation.Unary.Any as VecAny using (here ; there)
open import Data.List as List using (List ; _++_ ; _∷_ ; [] )
import Data.List.Properties as ListProp
open import Data.List.Relation.Unary.Any as ListAny using (here ; there ; any ; _∷=_ ) renaming (_─_ to _⑊_ )
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties as ListProp
open import Data.List.Membership.Setoid.Properties using (∈-∷=⁺-updated)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_ ; _≢_ ; setoid) renaming (refl to 1ₑ)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Fin as Fin using (Fin)
open import Data.Fin.Properties using ( suc-injective)
open import Data.Product using (_,_; Σ)
open import Data.Product.Properties using (,-injective)
import Data.Nat as Nat
open import Data.Bool.Base
open import Data.Maybe.Base using (Maybe) renaming (nothing to ⊥ ; just to ⌊_⌋)
open import Relation.Nullary hiding (⌊_⌋)
open import Relation.Nullary.Decidable using (dec-true ; dec-false)
import Relation.Binary
import Relation.Unary
open import Agda.Primitive


pre-image : ∀ {i j}{A : Set i}{B : Set j} (f : A → B) → B → Set (i ⊔ j)
pre-image f b = Σ _ (λ a → f a ≡ b)
-- a simple way to (de)construct pre images
pattern PreImage a = a , 1ₑ

-- simple (de)constructors for _∈_
pattern Ο {l} = here {xs = l} 1ₑ
pattern 1+ {x}{l} a = there {x}{l} a

-- Some notations
module _ {i}{A : Set i} where
  _[_∶_] : ∀ (Γ : List A) {m} → m ∈ Γ → A → List A
  ℓ [ M ∶ m ] = M ∷= m

  _∶_ : ∀ {Γ : List A} {m} → (M : m ∈ Γ) → (a : A) → a ∈ (Γ [ M ∶ a ])
  M ∶ m = ∈-∷=⁺-updated (setoid A) M


  data _Maybe-⑊_ {ℓ : List A}{a}(a∈ : a ∈ ℓ) : ∀ {a'} → a' ∈ ℓ → Set i where
    ⊥ : a∈ Maybe-⑊ a∈
    ⌊_⌋ : ∀ {a'}{a'∈ : a' ∈ ℓ} → (a∈' : a ∈ (ℓ ⑊ a'∈)) → a∈ Maybe-⑊ a'∈

  _⑊?_ : ∀ {l : List A}{a}(a∈ : a ∈ l){a'} → (a'∈ : a' ∈ l) → a∈ Maybe-⑊ a'∈
  Ο ⑊? Ο = ⊥
  Ο ⑊? 1+ a'∈ = ⌊ Ο ⌋
  1+ a∈ ⑊? Ο = ⌊ a∈ ⌋
  1+ a∈ ⑊? 1+ a'∈ with a∈ ⑊? a'∈
  ... | ⌊ a∈ ⌋ = ⌊ 1+ a∈ ⌋
  ... | ⊥ = ⊥

module VecList where

  -- VecList B [l₀ ; .. ; lₙ] ≃ B l₀ × .. × B lₙ
  data VecList {A : Set}(B : A → Set) : List A  → Set where
    [] : VecList B []
    _,_ : ∀ {a as} → B a → VecList B as → VecList B (a ∷ as)


  map : ∀ {A : Set}{B B' : A → Set}{l : List A} → (∀ a → B a → B' a) → VecList B l → VecList B' l
  map f [] = []
  map f (x , xs) = f _ x , map f xs

  lookup : ∀ {A : Set}{B : A → Set}{l : List A}{a} → VecList B l → a ∈ l → B a
  lookup (t , _) Ο = t
  lookup (_ , ts) (1+ a∈) = lookup ts a∈

  module _ {A : Set}{B : A → Set}(_≟_ : Relation.Binary.Decidable (_≡_ {A = A}))
       (_≟B_ : ∀ {a} → Relation.Binary.Decidable (_≡_ {A = B a})) where
    private
      _≟B'_ : ∀ {a a'}(b : B a) (b' : B a') → Dec (Σ (a ≡ a') (λ e → ≡.subst B e b ≡ b'))
      _≟B'_ {a} {a'} b b' with a ≟ a'
      ... | no p = no λ { (x , _) → p x}
      ... | yes 1ₑ with b ≟B b'
      ... | no p = no λ { ( 1ₑ , x ) → p x}
      ... | yes p = yes (1ₑ , p)


    lookup⁻¹ : ∀ {a} (b : B a) {l} (xs : VecList B l) → Maybe (pre-image (lookup xs) b)
    lookup⁻¹ b [] = ⊥
    lookup⁻¹ b (b' , xs) with b ≟B' b'
    ... | yes (1ₑ , 1ₑ) = ⌊ PreImage Ο ⌋
    ... | no _ = do
         PreImage i ← lookup⁻¹ b xs
         ⌊ PreImage (1+ i) ⌋
        where open Data.Maybe.Base using (_>>=_)

  tabulate : ∀ {A : Set}{B : A → Set} → (∀ a → B a) → (ℓ : List A) → VecList B ℓ
  tabulate f [] = []
  tabulate f (x ∷ ℓ) = f x , tabulate f ℓ

module MoreFin where
  inject₁-≢-fromℕ : ∀ {n} i → Fin.inject₁ i ≢ Fin.fromℕ n
  inject₁-≢-fromℕ Fin.zero = λ ()
  inject₁-≢-fromℕ (Fin.suc i) = λ e → inject₁-≢-fromℕ i (suc-injective e)

module MoreList where

 module _ {i}{A : Set i} where

  _≟∈_ : ∀ {l}{a : A}(a∈ a∈' : a ∈ l) → Dec (a∈ ≡ a∈')
  Ο ≟∈ Ο = yes 1ₑ
  1+ p ≟∈ 1+ p' with p ≟∈ p'
  ... | yes q = yes (≡.cong 1+ q)
  ... | no q = no λ {1ₑ → q 1ₑ}
  Ο ≟∈ 1+ p = no λ ()
  1+ q ≟∈ Ο = no λ ()

 module _ {ℓ : Level} {A  : Set ℓ} {ℓ' : Level} {B : Set ℓ} where
   import Data.List.Membership.Setoid (setoid A) as SetoidA
   open import Data.List.Relation.Unary.Any.Properties using (map⁻)
   ∈-map⁺-map⁻ :
      (f : A → B) {y : B} {xs : List A} →
      (y∈ : y ∈ List.map f xs) →
      let (y' , i'' , e) = ∈-map⁻ f y∈
      in ∈-map⁺ f i'' ≡  ≡.subst (_∈ _) e y∈
   ∈-map⁺-map⁻ f {xs = x ∷ xs} Ο = 1ₑ
   ∈-map⁺-map⁻ f {y}{xs = x ∷ xs} (1+ y∈) rewrite ∈-map⁺-map⁻ f y∈
      with SetoidA.find (map⁻ y∈)
   ... | y' , i'' , e = aux y∈ e
     where
       aux : ∀ {y} (y∈ : y ∈ List.map f xs) (e : y ≡ f y') →
         1+ (≡.subst (_∈ (List.map f xs)) e y∈) ≡
         ≡.subst (_∈ (f x ∷ List.map f xs)) e (1+ y∈)
       aux y∈ 1ₑ = 1ₑ


module MoreVec where
  module _ {i}{A : Set i}(_≟_ : Relation.Binary.Decidable (_≡_ {A = A})) where

    open import Data.Vec.Membership.DecPropositional _≟_
    open VecAny using (index)
    lookup⁻¹ : ∀ a {n} (l : Vec A n) → Maybe (pre-image (Vec.lookup l) a)
    lookup⁻¹ a {n} l with a ∈? l
    ... | no _ = ⊥
    ... | yes a∈ rewrite VecProp.lookup-index a∈ = ⌊ PreImage (index a∈) ⌋

  insert-lookup-last< : ∀ {i}{A : Set i}{n} k a (l : Vec A n)
     → Vec.lookup (Vec.insertAt l (Fin.fromℕ n) a) (Fin.inject₁ k) ≡ Vec.lookup l k
  insert-lookup-last< Fin.zero a (x ∷ l) = 1ₑ
  insert-lookup-last< (Fin.suc k) a (x ∷ l) = insert-lookup-last< k a l

  insert-last-++ : ∀ {i}{A : Set i}{n m}(xs : Vec A n)(ys : Vec A m) a →
      Vec.toList (Vec.insertAt (xs Vec.++ ys) (Fin.fromℕ _) a) ≡
      Vec.toList (xs Vec.++ (Vec.insertAt ys (Fin.fromℕ _) a))
  insert-last-++ [] ys a = 1ₑ
  insert-last-++ (x ∷ xs) ys a = ≡.cong (x ∷_) (insert-last-++ xs ys a)


  module _ {i}{j}{A : Set i}{P : A → Set j}(P? : Relation.Unary.Decidable P) where
    -- return the list of indices that satfies P
    find-indices : ∀ {n} → (xs : Vec A n) → List (Fin n)
    find-indices [] = []
    find-indices (x ∷ xs) with ys ← List.map Fin.suc (find-indices xs)
                    | does (P? x)
    ... | true = Fin.zero ∷ ys
    ... | false = ys

    open VecAny using (here ; there )

    find-indices-∈ : ∀ {n a} → {xs : Vec A n} → (a∈ : a ∈̬ xs) → P a → (VecAny.index a∈ ∈ find-indices xs)
    find-indices-∈ (here 1ₑ) Pa rewrite dec-true (P? _) Pa  = here 1ₑ
    find-indices-∈ (there {x = x}{xs = xs} a∈) Pa
       with rec ← ListProp.∈-map⁺ Fin.suc (find-indices-∈ a∈ Pa)
        | does (P? x)
    ... | true = there rec
    ... | false = rec

    find-indices-insert-last : ∀ {n} → (xs : Vec A n) → ∀ {a} → P a →
        find-indices (Vec.insertAt xs (Fin.fromℕ n) a) ≡
             List.map Fin.inject₁ (find-indices xs) ++ (Fin.fromℕ n ∷ [])
    find-indices-insert-last [] Pa rewrite dec-true (P? _) Pa = 1ₑ
    find-indices-insert-last (x ∷ xs) Pa rewrite find-indices-insert-last xs Pa
       with P? x
    ... | yes p rewrite
            ListProp.map-++ Fin.suc (List.map Fin.inject₁ (find-indices xs) ) (Fin.fromℕ _ ∷ [])
          | ≡.sym (ListProp.map-∘ {g = Fin.suc}{Fin.inject₁}(find-indices xs))
          | ≡.sym (ListProp.map-∘ {g = Fin.inject₁}{Fin.suc}(find-indices xs))
         = 1ₑ


    ... | no p rewrite
            ListProp.map-++ Fin.suc (List.map Fin.inject₁ (find-indices xs) ) (Fin.fromℕ _ ∷ [])
         | ≡.sym (ListProp.map-∘ {g = Fin.suc}{Fin.inject₁}(find-indices xs))
         | ≡.sym (ListProp.map-∘ {g = Fin.inject₁}{Fin.suc}(find-indices xs))
      = 1ₑ

    find-indices-insert-last-⊥ : ∀ {n} → (xs : Vec A n) → ∀ {a} → ¬ P a →
        find-indices (Vec.insertAt xs (Fin.fromℕ n) a) ≡
             List.map Fin.inject₁ (find-indices xs)
    find-indices-insert-last-⊥ [] Pa rewrite dec-false (P? _) Pa = 1ₑ
    find-indices-insert-last-⊥ (x ∷ xs) Pa rewrite find-indices-insert-last-⊥ xs Pa
        | ≡.sym (ListProp.map-∘ {g = Fin.suc}{Fin.inject₁}(find-indices xs))
        with P? x
    ... | yes p
        rewrite  ≡.sym (ListProp.map-∘ {g = Fin.inject₁}{Fin.suc}(find-indices xs))
          = 1ₑ
    ... | no p
        rewrite  ≡.sym (ListProp.map-∘ {g = Fin.inject₁}{Fin.suc}(find-indices xs))
          = 1ₑ


    find-indices-0 : ∀ {n} → (xs : Vec A n) → (∀ {a} → a ∈̬ xs → ¬ P a) →
        find-indices xs ≡ []
    find-indices-0 [] ¬P = 1ₑ
    find-indices-0 (x ∷ xs) ¬P rewrite dec-false (P? x) (¬P (here 1ₑ))
      | find-indices-0 xs (λ z → ¬P (there z))
       = 1ₑ

  find-indices-map⁻ : ∀ {i}{j}{k}{A : Set i}{B : Set j}
      {PA : A → Set j}(PA? : Relation.Unary.Decidable PA)
      {PB : B → Set k}(PB? : Relation.Unary.Decidable PB) →
      ∀ (f : A → B) {n} →
      (∀ {a} → PA a → PB (f a)) →
      (∀ {a} → PB (f a) → PA a) →
      (xs : Vec A n) →
        find-indices PB? (Vec.map f xs) ≡ find-indices PA? xs

  find-indices-map⁻ PA? PB? f AB BA [] = 1ₑ
  find-indices-map⁻ PA? PB? f AB BA (x ∷ xs) with PA? x
  ... | yes p rewrite dec-true (PB? (f x)) (AB p) | find-indices-map⁻ PA? PB? f AB BA xs = 1ₑ
  ... | no p rewrite dec-false (PB? (f x)) (λ x₁ → p (BA x₁)) | find-indices-map⁻ PA? PB? f AB BA xs = 1ₑ







\end{code}



