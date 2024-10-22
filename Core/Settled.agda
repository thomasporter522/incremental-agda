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

data SettledExcept : ExpUp -> Set where 
  SettledExceptConst : ∀ {t n} ->
    SettledExcept (EUp (⇑ (t , n)) EConst)
  SettledExceptHole : ∀ {t n} ->
    SettledExcept (EUp (⇑ (t , n)) EHole)
  SettledExceptFunSyn : ∀ {t1 t2 m1 m2 e n} ->
    SettledExcept (EUp (⇑ (t1 , n)) (EFun (t2 , Old) m1 (ELow ̸⇓ m2 e)))
  SettledExceptFunAna : ∀ {t1 t2 m1 m2 e n} ->
    SettledExcept (EUp ̸⇑ (EFun (t1 , n) m1 (ELow (⇓ (t2 , Old)) m2 e)))
  SettledExceptAp : ∀ {t1 t2 m1 m2 m3 e1 e2 n} ->
    SettledExcept e1 -> 
    SettledExcept e2 -> 
    SettledExcept (EUp (⇑ (t1 , n)) (EAp (ELow ̸⇓ m1 e1) m2 (ELow (⇓ (t2 , Old)) m3 e2)))
  SettledExceptVar : ∀ {t x m n} ->
    SettledExcept (EUp (⇑ (t , n)) (EVar x m))
  SettledExceptAsc : ∀ {t1 t2 t3 m e n} ->
    SettledExcept e -> 
    SettledExcept (EUp (⇑ (t1 , n)) (EAsc (t2 , Old) (ELow (⇓ (t3 , Old)) m e)))

data SettledLow : ExpLow -> Set where 
  SettledLowAna : ∀ {e t m} ->
    Settled e ->
    SettledLow (ELow (⇓ (t , Old)) m e)

data PSettled : Program -> Set where 
  PSettledRoot : ∀ {e} ->
    Settled e -> 
    PSettled (PRoot e)

settled-implies-settled-except : ∀ {e} ->
  (Settled e) -> (SettledExcept e)
settled-implies-settled-except SettledConst = SettledExceptConst
settled-implies-settled-except SettledHole = SettledExceptHole
settled-implies-settled-except SettledFunSyn = SettledExceptFunSyn
settled-implies-settled-except SettledFunAna = SettledExceptFunAna
settled-implies-settled-except (SettledAp s s₁) = SettledExceptAp (settled-implies-settled-except s) (settled-implies-settled-except s₁)
settled-implies-settled-except SettledVar = SettledExceptVar
settled-implies-settled-except (SettledAsc s) = SettledExceptAsc (settled-implies-settled-except s)