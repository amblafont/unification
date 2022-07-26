open import Data.List hiding ([_])
open import Data.Unit hiding (_≤_)
open import Data.Empty
open import Data.Nat hiding (_^_)
open import Data.Nat.Properties as ℕₚ
open import Data.Product hiding (map)
open import Data.Sum hiding (map)
open import Agda.Builtin.Equality
open import Relation.Binary.PropositionalEquality using (sym ; cong)
module occurcheckind where

 module _ (D : Set) (I : Set)(L : I → List (D → D))(S : I → Set) where
  -- I can't figure out how to find lemmas about max in the standard lib, so I define mine
  max : ℕ → List ℕ → ℕ
  max _ [] = 0
  max p (x ∷ l) with ℕₚ.≤-total x (max p l)
  ... | inj₁ _ = max p l
  ... | inj₂ _ = x

  maxl : ∀ {n p l q} → p ≥ q → max n (p ∷ l) ≥ q
  maxl {n} {p}{l}{q} lepq with ℕₚ.≤-total p (max n l)
  ... | inj₁ x = ≤-trans lepq x
  ... | inj₂ y = lepq

  maxr : ∀ {n p l q} → max n l ≥ q → max n (p ∷ l) ≥ q
  maxr {n} {p}{l}{q} lepq with ℕₚ.≤-total p (max n l)
  ... | inj₁ x = lepq
  ... | inj₂ y = ≤-trans lepq y

  _⇒_ : ∀ (X Y : D → Set) → Set 
  X ⇒ Y = ∀ d → X d → Y d


  data M[_]^_ : (X : D → Set) → List D → Set 
  data M (X : D → Set) : D → Set 

  data M[_]^_ where
     M^[] : ∀ X → M[ X ]^ []
     _M^::_ : ∀ {X} {d}{l} → M X d → M[ X ]^ l → M[ X ]^ (d ∷ l)

  -- on pourrait faire une version avec une liste de paires de foncteur et de M X
  data M X where
    η : ∀ {d} → X d → M X d
    op : ∀ i {d} → S i → (M[ X ]^ (map (λ f → f d) (L i))) → M X d

  _[_]l : ∀ {X Y : D → Set}{l} → M[ X ]^ l  → (X ⇒ M Y) → M[ Y ]^ l
  _[_] : ∀ {X Y : D → Set}{d} → M X d → (X ⇒ M Y) → M Y d

  η x [ σ ] = σ _ x
  op i s x [ σ ] = op i s (x [ σ ]l)

  M^[] _ [ σ ]l = M^[] _
  (x M^:: ms) [ σ ]l = (x [ σ ]) M^:: (ms [ σ ]l)

  hs : ∀ {X}{l} → M[ X ]^ l → List ℕ
  h : ∀ {X}{d} → M X d → ℕ

  h (η x) = 0
  h (op i s x) = suc (max 0 (hs x))

  hs (M^[] _) = []
  hs (x M^:: ms) = h x ∷ hs ms

  _+ᵢ_ : (D → Set) → (D → Set) → (D → Set)
  (X +ᵢ Y) d = X d ⊎ Y d


  is-closed : ∀ {X}{d} → M X d → M (λ _ → ⊥) d ⊎ ℕ
  are-closed : ∀ {X}{l} → M[ X ]^ l → (M[ (λ _ → ⊥) ]^ l) ⊎ ℕ

  are-closed (M^[] _) = inj₁ (M^[] _)
  are-closed (m M^:: ms) with are-closed ms | is-closed m
  ... | inj₁ ms | inj₁ m = inj₁ (m M^:: ms)
  ... | inj₂ n | _ = inj₂ n
  ... | inj₁ ms | inj₂ n = inj₂ n
  -- ... | inj₁ ms | inj₂ n = inj₂ n

  is-closed (η x) = inj₂ 0
  is-closed (op i s ms) with are-closed ms
  ... | inj₁ ms = inj₁ (op i s ms)
  ... | inj₂ n = inj₂ (1 + n)



  h-comp : ∀ {X}{Y}a  → (u : X ⇒ M Y) (m : M X a) → ∀ n (p : ℕ) → is-closed m ≡ inj₂ n →
      (∀ d x → h (u d x) ≥ p) → h (m [ u ]) ≥ n + p

  hs-comp : ∀ {X}{Y}l  → (u : X ⇒ M Y) (ms : M[ X ]^ l) → ∀ n (p : ℕ) → are-closed ms ≡ inj₂ n →
      (∀ d x → h (u d x) ≥ p) → max 0 (hs (ms [ u ]l)) ≥ n + p
     
  h-comp a u (η x) .0 p refl hp = hp a x
  h-comp a u (op i s ms) n p cm hp with are-closed ms in eq
  h-comp a u (op i s ms) .(1 + n) p refl hp | inj₂ n = s≤s aux
    where
      aux : (max 0 (hs (ms [ u ]l))) ≥ (n + p)
      aux = hs-comp (map (λ f → f a) (L i)) u ms n p eq hp

  hs-comp .(_ ∷ _) u (_M^::_ {d = d}{l = l} m ms) n p cm hp with are-closed ms in eqms | is-closed m in eqm
  hs-comp .(_ ∷ _) u (_M^::_ {d = d} {l = l} m ms) .n p refl hp | inj₁ x | inj₂ n = aux
    where
          tete : h (m [ u ]) ≥ n + p
          tete = h-comp d u m n p eqm hp

          aux : max 0 (h (m [ u ]) ∷ hs (ms [ u ]l)) ≥ n + p
          aux = maxl tete

  hs-comp .(_ ∷ _) u (_M^::_ {d = d} {l} m ms) .n p refl hp | inj₂ n | cm' = aux
    where
          queue : max 0 (hs (ms [ u ]l)) ≥ n + p
          queue = hs-comp l u ms n p eqms hp

          aux : max 0 (h (m [ u ]) ∷ hs (ms [ u ]l)) ≥ n + p
          aux = maxr {n = 0}{p = h (m [ u ])} {l = hs (ms [ u ]l)} queue

  {-
  We want to show that
  M 0 → M A
  ↓      ↓
  M 0 → M 0 + ℕ
  is a pullback

  By the pullback lemma, it is equivalent to show that the following is a pullback
  M 0 → M A
  ↓      ↓
      M 0 + ℕ
         ↓
  1  →  1 + 1
    inl 

  This means that given t ∈ M A d such that is-closed t = inj₁ u , there exists a unique u'
  such that t = M i (u')
  Of course, this is going to be u.
  For uniqueness, it is enough to show that is-closed (M i u) = inj₁ u for any u


  -}
  pbk-unique : ∀ {A}{d} → (u : M (λ _ → ⊥) d) → is-closed {X = A}(u [ (λ d₁ → ⊥-elim) ]) ≡ inj₁ u
  pbks-unique : ∀ {A}{l} → (u : M[ (λ _ → ⊥) ]^ l) → are-closed {X = A}(u [ (λ d₁ → ⊥-elim) ]l) ≡ inj₁ u

  pbk-unique {A} {d} (op i s ms) rewrite pbks-unique {A}{map (λ f → f d) (L i)} ms = refl


  pbks-unique {A} {.[]} (M^[] .(λ _ → ⊥)) = refl
  pbks-unique {A} {.(_ ∷ _)} (x M^:: u) rewrite pbk-unique {A} x | pbks-unique {A} u = refl

  pbk-exist : ∀ {A}{d} → (t : M A d)(u : M (λ _ → ⊥) d) → is-closed {X = A} t ≡ inj₁ u
               → t ≡ u [ (λ d₁ → ⊥-elim) ]

  pbks-exist : ∀ {A}{l} → (t : M[ A ]^ l)(u : M[ (λ _ → ⊥) ]^ l ) → are-closed {X = A} t ≡ inj₁ u
               → t ≡ u [ (λ d₁ → ⊥-elim) ]l
  pbk-exist {A} {d} (op i s x) u ct with are-closed x in eq
  pbk-exist {A} {d} (op i s x) .(op i s u) refl | inj₁ u rewrite pbks-exist x u eq = refl

  pbks-exist (M^[] _) .(M^[] (λ _ → ⊥)) refl = refl
  pbks-exist (x M^:: t) u ct with are-closed t in eqt | is-closed x in eqx
  pbks-exist (x M^:: t) .(x₂ M^:: x₁) refl | inj₁ x₁ | inj₁ x₂ rewrite pbk-exist x x₂ eqx | pbks-exist t x₁ eqt  = refl

  -- reste a montrer que le yoneda est de la meme taille que l'element





