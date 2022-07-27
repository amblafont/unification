{-# OPTIONS --type-in-type #-}
open import Data.List hiding ([_])
open import Data.Unit hiding (_≤_)
open import Data.Empty
open import Data.Nat hiding (_^_)
open import Data.Nat.Properties as ℕₚ
open import Data.Product hiding (map)
open import Data.Sum hiding (map)
open import Agda.Builtin.Equality
open import Relation.Binary.PropositionalEquality using (sym ; cong ; trans)
module occurcheckind where
 ⊥-elim-d : ∀ {w } {Whatever : ⊥  → Set w} → (witness : ⊥ ) → Whatever witness
 ⊥-elim-d ()

 le0 : ∀ n p → n + p ≤ p → n ≡ 0
 le0 = {!!}

 eq-le : ∀ n p → n ≡ p → n ≤ p
 eq-le = {!!}

 funext : ∀{A}{B : A → Set}(f g : ∀ a → B a) → (∀ a → f a ≡ g a) → f ≡ g
 funext = {!!}
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

 record is-cat (C : Set) : Set where
    field
      hom : C → C → Set
      _·_ : ∀ {a b c : C} → hom a b → hom b c → hom a c

 open is-cat {{...}} public

 instance
   SetCat : is-cat Set
   hom {{ SetCat }} X Y = X → Y
   _·_ {{ SetCat}} f g = λ x → g (f x)

 record is-functor {C : Set} {D : Set} {{ Cc : is-cat C }} {{ Dc : is-cat D}} (F : C → D) : Set where
  field
    homF : ∀ {a b} → hom a b → hom (F a) (F b)

 open is-functor {{ ... }} public

 ∥_∥ : {C D : Set} ⦃ Cc : is-cat C ⦄ ⦃ Dc : is-cat D ⦄ (F : C → D)
      ⦃ r : is-functor F ⦄ {a b : C} →
      hom a b → hom (F a) (F b)
 ∥ F ∥ f = homF f

 record Functor (C : Set) (D : Set){{ Cc : is-cat C}}{{ Dc : is-cat D}} : Set where
   -- private module C = Category C
   -- private module D = Category D
   field
    obF : C → D
    instance Functor-is-func : is-functor obF
    -- is-func : ∀ {a b : C} → hom a b → hom (∣_∣ a) (∣_∣ b)

 open Functor public

 module _ (D : Set) {{ Dc : is-cat D}} (I : Set)(L : I → List (Functor D D))(S : I → D → Set){{ SF : ∀ {i} → is-functor (S i)}} where

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
    op : ∀ i {d} → S i d → (M[ X ]^ (map (λ F → obF F d) (L i))) → M X d

  _[_] : ∀ {X Y : D → Set}{d} → M X d → (X ⇒ M Y) → M Y d
  _[_]l : ∀ {X Y : D → Set}{l} → M[ X ]^ l  → (X ⇒ M Y) → M[ Y ]^ l

  η x [ σ ] = σ _ x
  op i s x [ σ ] = op i s (x [ σ ]l)

  M^[] _ [ σ ]l = M^[] _
  (x M^:: ms) [ σ ]l = (x [ σ ]) M^:: (ms [ σ ]l)

  [][] : ∀ {X Y Z : D → Set}{d} (t : M X d) (u : X ⇒ M Y) (v : Y ⇒ M Z) → (t [ u ]) [ v ] ≡ (t [ (λ d x → u d x [ v ]) ])
  [][] = {!!}

  record has-weight (C : D → Set) : Set where
    field
      o : ∀ {d} → C d → ℕ
  open has-weight {{ ... }} public


  ∣_∣ : ∀ {X}{{oX : has-weight X}}{d} → M X d → ℕ
  ∣_∣l : ∀ {X}{{oX : has-weight X}}{l} → M[ X ]^ l → List ℕ

  ∣ η x ∣ = o x
  ∣ op i s x ∣ = suc (max 0 ∣ x ∣l)

  ∣_∣l (M^[] _) = []
  ∣_∣l (x M^:: ms) = ∣ x ∣ ∷ ∣ ms ∣l

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



  -- define h u as min h (u d)
  -- then h (m [ u ]) >= h u + || m ||
  {-
  Does it allow to show the think we want about the pullback of
    MA
     ↓   ?
A → M0
  u

Assume given an element t ∈ MA_d sucht that || t || exists and such that
u_i = t [ u ]
Then, | u_i | ≥ | u | + ||t || but if u is flat then |u_i| = |u| and we can conclude
that || t || = 0
but flatness does not work for the argument M ↦ M(-+1)
  -}
  h-comp : ∀ {X}{Y}{{oY : has-weight Y}}a  → (u : X ⇒ M Y) (m : M X a) → ∀ n (p : ℕ) → is-closed m ≡ inj₂ n →
      (∀ d x →  ∣ u d x ∣  ≥ p) → ∣ m [ u ] ∣ ≥ n + p

  hs-comp : ∀ {X}{Y}{{oY : has-weight Y}}l  → (u : X ⇒ M Y) (ms : M[ X ]^ l) → ∀ n (p : ℕ) → are-closed ms ≡ inj₂ n →
      (∀ d x → ∣ u d x ∣   ≥ p) → max 0 ∣ ms [ u ]l ∣l  ≥ n + p

  h-comp a u (η x) .0 p refl hp = hp a x
  h-comp a u (op i s ms) n p cm hp with are-closed ms in eq
  h-comp a u (op i s ms) .(1 + n) p refl hp | inj₂ n = s≤s aux
    where
      aux : (max 0 ∣ ms [ u ]l ∣l) ≥ n + p
      aux =  hs-comp (map (λ F → obF F a) (L i)) u ms n p eq hp 

  hs-comp .(_ ∷ _) u (_M^::_ {d = d}{l = l} m ms) n p cm hp with are-closed ms in eqms | is-closed m in eqm
  hs-comp .(_ ∷ _) u (_M^::_ {d = d} {l = l} m ms) .n p refl hp | inj₁ x | inj₂ n = aux
    where
          tete : ∣ m [ u ] ∣ ≥ n + p
          tete = h-comp d u m n p eqm hp

          aux : max 0 (∣ m [ u ] ∣ ∷ ∣ ms [ u ]l ∣l) ≥ n + p
          aux = maxl tete

  hs-comp .(_ ∷ _) u (_M^::_ {d = d} {l} m ms) .n p refl hp | inj₂ n | cm' = aux
    where
          queue : max 0 ∣ ms [ u ]l ∣l ≥ n + p
          queue = hs-comp l u ms n p eqms hp

          -- aux : max 0 (h (m [ u ]) ∷ hs (ms [ u ]l)) ≥ n + p
          aux : max 0 (∣ m [ u ] ∣ ∷ ∣ ms [ u ]l ∣l) ≥ n + p
          aux = maxr {n = 0}{p = ∣ m [ u ] ∣} {l = ∣ ms [ u ]l ∣l} queue

  is-flat : ∀ {X}{Y}{{oY : has-weight Y}} → (X ⇒ M Y) → Set
  is-flat {X} f = ∀ {d d' : D} (x : X d)(x' : X d') →  ∣ f d x ∣ ≡ ∣ f d' x' ∣

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

  pbk-unique {A} {d} (op i s ms) rewrite pbks-unique {A}{map (λ F → obF F d) (L i)} ms = refl


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


  instance
    ⊥-has-weight : has-weight (λ _ → ⊥)
    o {{ ⊥-has-weight}} = ⊥-elim


  
  -- The main result
  {-
  A → M0 flat
  then the pullback
      MA
       ↓
  A → M0
  is A + A×M_0 A
  -}
  main-result : ∀ {A}(u : A ⇒ M (λ _ → ⊥)) → is-flat u → ∀ d (a : A d) (t : M A d) → u d a ≡ t [ u ] → (Σ (A d) λ a' → t ≡ η a' × u d a ≡ u d a') ⊎ t ≡ u d a [ (λ _ → ⊥-elim) ]
  main-result {A} u fl d a t eq with is-closed t in eqt
  ... | inj₁ x rewrite eq | pbk-exist t x eqt rewrite [][] x (λ k → ⊥-elim) u
      = inj₂ (trans (cong (_[_] x) (funext _ _ λ a₁ → funext _ _ ⊥-elim-d)) (sym ([][] x _ (λ k → ⊥-elim)) ))

  ... | inj₂ n with n-0 (h-comp {A} d u t n ∣ u d a ∣ eqt λ d₁ x → eq-le _ _ (fl a x))
    where n-0 : ∣ t [ u ] ∣ ≥ n + ∣ u d a ∣ → n ≡ 0
          n-0 h rewrite eq = le0 _ _ h
  main-result {A} u fl d a (η x) eq | inj₂ .0 | refl = inj₁ (x , (refl , eq))
  main-result {A} u fl d a (op i x ms) eq | inj₂ .0 | refl with are-closed ms
  ... | inj₁ x = ⊥-elim (impossible eqt)
    where impossible : inj₁ (op i _ x) ≡ inj₂ 0 → ⊥
          impossible ()
  ... | inj₂ y = ⊥-elim (impossible eqt)
    where impossible : inj₂ (suc y) ≡ inj₂ 0 → ⊥
          impossible ()
     

  -- reste a montrer que le yoneda est de la meme taille que l'element
  -- yoneda lemma

  y = hom {{ Dc}}

  _ʸ : ∀ {X : D → Set}{{XF : is-functor X}}{d} → X d → y d ⇒ X
  _ʸ {X}{d} x d' f = ∥ X ∥ f x

  instance
    y-is-functor : ∀ {d} → is-functor (y d)
    homF {{y-is-functor {d} }} f x = x · f


  instance
    M-is-functor : ∀ {X} {{ XF : is-functor X}} → is-functor (M X)
    Ml-is-functor : ∀ {X} {{ XF : is-functor X}} {l} → is-functor (λ d → M[ X ]^ (map (λ F → obF F d) l) )
    homF ⦃ M-is-functor {X} ⦃ XF ⦄ ⦄ f (η x) = η (∥ X ∥ f x)
    homF ⦃ M-is-functor {X} ⦃ XF ⦄ ⦄ f (op i s ms) = op i (homF f s) (homF {{ r = Ml-is-functor }} f ms)
    homF ⦃ Ml-is-functor {X} ⦃ XF ⦄ {[]} ⦄ f ms = ms
    homF ⦃ Ml-is-functor {X} ⦃ XF ⦄ {F ∷ l} ⦄ f (m M^:: ms) = homF {{ r = M-is-functor}} (homF f) m   M^:: homF {{ r = Ml-is-functor}} f ms where open Functor F

  module _ (X : D → Set){{XF : is-functor X}} where
    instance
      X-has-weight : has-weight X
      o {{ X-has-weight }} = λ _ → 0
    size-y : ∀ d (u : M X d) → ∀ (a : D) (f : hom d a) → ∣ u ∣ ≡ ∣ (u ʸ) a f ∣
    size-ys : ∀  d (l : List (Functor D D))
                    (ms : M[ X ]^ map (λ F → obF F d) l) →
                    (a : D)
                    (f : hom d a) →
            ∣ ms ∣l ≡ ∣ (is-functor.homF Ml-is-functor f ms) ∣l 
    size-y d (η x) a f = refl
    size-y d (op i s ms) a f rewrite size-ys d (L i) ms a f = refl

    size-ys d [] ms a f = refl
    size-ys d (F ∷ l) (m M^:: ms) a f rewrite size-y (obF F d) m (obF F a) (homF {{ r = Functor.Functor-is-func F }} f) | size-ys d l ms a f    = refl 

    y-is-flat : ∀ d (u : M X d) → is-flat (u ʸ)
    y-is-flat d u = λ x x' → trans (sym (size-y d u _ x)) (size-y d u _ x')

  -- final : ∀ (X : D → Set) {{ XF : is-functor X}} a b (u : M X a)(f : y a b) (t : M (y b)  ) →
  --             homF f u ≡ ?





