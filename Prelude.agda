open import Agda.Primitive using (Level; lzero; lsuc) renaming (_⊔_ to lmax)
open import Data.Bool hiding (_<_; _≟_)
open import Data.Empty
open import Data.Fin
open import Data.List hiding (lookup)
open import Data.Nat
open import Data.Product hiding (map)
open import Data.Sum renaming (_⊎_ to _+_; inj₁ to Inl ; inj₂ to Inr) hiding (map)
open import Data.Unit renaming (tt to <>)
open import Data.Vec hiding (map; _++_; concat; filter)
open import Function
open import Relation.Binary.PropositionalEquality hiding (inspect)
open import Relation.Nullary
open import Relation.Unary

module Prelude where
  
  private
    variable
      ℓ : Level

  postulate
    extensionality : ∀ {A B : Set} {f g : A → B}
      → (∀ (x : A) → f x ≡ g x)
        -----------------------
      → f ≡ g

  assimilation : ∀ {A : Set} (¬x ¬x' : ¬ A) → ¬x ≡ ¬x'
  assimilation ¬x ¬x' = extensionality (λ x → ⊥-elim (¬x x))

  ¬-≡ : ∀ {A : Set} → (¬a : ¬ A) → (¬a' : ¬ A) → ¬a ≡ ¬a'
  ¬-≡ ¬a ¬a' = extensionality λ { a → ⊥-elim (¬a a) }

