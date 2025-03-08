\begin{code}
module lcsig where

open import lib
open import Agda.Primitive
open import main using (Signature ; isFriendly)
open import Data.Vec.Base as Vec using (Vec)
open import Data.Nat as ℕ using (ℕ; _+_)
open import Data.Fin as Fin using (Fin)
open import Data.List as List hiding (map ; [_] ; lookup)
open import Data.List.Relation.Binary.Pointwise using (Pointwise ; [] ; _∷_)
import lc
open import lc using (hom ; _↑)
\end{code}
%<*lc-sig>
\begin{code}
data O n : Set where
   Var : Fin n → O n
   App : O n
   Lam : O n

α : {n : ℕ} → O n → List ℕ
α (Var x) = []
α {n} App = n ∷ n ∷ []
α {n} Lam = 1 + n ∷ []

_｛_｝ : ∀ {a b : ℕ} → O a → hom a b → O b
Var x ｛ s ｝ = Var (Vec.lookup s x)
App ｛ s ｝ = App
Lam ｛ s ｝ = Lam

-- Pointwise hom [a₁, ⋯, aₙ] [b₁, ⋯, bₙ] is the type of the
-- lists of the shape [c₁, ⋯, cₙ] with c­ᵢ : hom aᵢ bᵢ
_^_ : {a b : ℕ} (x : hom a b) (o : O a) → Pointwise hom (α o) (α (o ｛ x ｝))
x ^ Var y = []
x ^ App = x ∷ x ∷ []
x ^ Lam = (x ↑) ∷ []
\end{code}
%</lc-sig>
\begin{code}
signature : Signature lzero lzero lzero
signature = record { A = ℕ;
                    hom = hom;
                    id = lc.id;
                    _∘_ = lc._∘_;
                    O = O;
                    α = α;
                    _｛_｝ = _｛_｝;
                    _^_ = _^_}
\end{code}