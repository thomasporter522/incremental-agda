open import Data.Nat hiding (_+_)
open import Data.Unit 
open import Data.Bool hiding (_<_; _≟_)
open import Data.Sum renaming (_⊎_ to _+_; inj₁ to Inl ; inj₂ to Inr) hiding (map)
open import Data.Product hiding (map)
open import Relation.Nullary 
open import Relation.Binary.PropositionalEquality hiding (inspect)
open import Prelude

open import Core.Core

module Core.Settled where

data Settled : ExpUp -> Set where 
  SettledConst : ∀ {t} ->
    Settled (EUp (⇑ (t , Old)) EConst)
  SettledHole : ∀ {t} ->
    Settled (EUp (⇑ (t , Old)) EHole)
  SettledFunSyn : ∀ {t1 t2 m1 m2 e} ->
    Settled (EUp (⇑ (t1 , Old)) (EFun (t2 , Old) m1 (ELow ̸⇓ m2 e)))
  SettledFunAna : ∀ {t1 t2 m1 m2 e} ->
    Settled (EUp ̸⇑ (EFun (t1 , Old) m1 (ELow (⇓ (t2 , Old)) m2 e)))
  SettledAp : ∀ {t1 t2 m1 m2 m3 e1 e2} ->
    Settled e1 -> 
    Settled e2 -> 
    Settled (EUp (⇑ (t1 , Old)) (EAp (ELow ̸⇓ m1 e1) m2 (ELow (⇓ (t2 , Old)) m3 e2)))
  SettledVar : ∀ {t x m} ->
    Settled (EUp (⇑ (t , Old)) (EVar x m))
  SettledAsc : ∀ {t1 t2 t3 m e} ->
    Settled e -> 
    Settled (EUp (⇑ (t1 , Old)) (EAsc (t2 , Old) (ELow (⇓ (t3 , Old)) m e)))

