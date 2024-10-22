open import Data.Nat hiding (_+_)
open import Data.Unit 
open import Data.Bool hiding (_<_; _≟_)
open import Data.Sum renaming (_⊎_ to _+_; inj₁ to Inl ; inj₂ to Inr) hiding (map)
open import Data.Product hiding (map)
open import Relation.Nullary 
open import Relation.Binary.PropositionalEquality hiding (inspect)
open import Prelude

open import Core.Core
open import Core.WellTyped
open import Core.Update
open import Core.Settled

module Core.StepsOrSettled where


-- StepsOrSettledLow : (e : ExpLow) ->
--   Σ[ e' ∈ ExpLow ] (e L↦ e') + (Settled e)
-- StepsOrSettledLow

mutual 

  StepsOrSettledSyn : 
    ∀ {Γ e} ->
    Σ[ t ∈ NewType ] (Γ ⊢ e ⇒ t) ->
    Σ[ e' ∈ ExpUp ] (e Up↦ e') + (SettledExcept e)
  StepsOrSettledSyn (t , SynConst m) = Inr SettledExceptConst
  StepsOrSettledSyn (t , SynHole m) = Inr SettledExceptHole
  StepsOrSettledSyn (t , SynFun wt m) = {!   !}
  StepsOrSettledSyn (.(TArrow _ _ , New) , SynFunVoid wt) = {!   !}
  StepsOrSettledSyn (t , SynAp wt x x₁ x₂ x₃) = {!   !}
  StepsOrSettledSyn (t , SynVar _ m) = Inr SettledExceptVar
  StepsOrSettledSyn (t , SynVarFail _ m) = Inr SettledExceptVar
  StepsOrSettledSyn (_ , SynAsc {t = (_ , New)} {e = (ELow _ _ _)} wt m) = Inl (_ , StepUp FillU⊙ (StepAsc IsNewNew) FillU⊙)
  StepsOrSettledSyn (_ , SynAsc {t = (_ , NArrow _ _)} {e = (ELow _ _ _)} wt m) = Inl (_ , StepUp FillU⊙ (StepAsc IsNewArrow) FillU⊙)
  StepsOrSettledSyn (_ , SynAsc {t = (_ , Old)} wt m) with StepsOrSettledAna wt
  StepsOrSettledSyn (_ , SynAsc {t = (_ , Old)} wt m) | Inl (e' , StepUp fill1 step fill2) = Inl (_ , StepUp (FillUEnvUpRec (FillUEnvAsc fill1)) step (FillUEnvUpRec (FillUEnvAsc fill2)))
  StepsOrSettledSyn (_ , SynAsc {t = (_ , Old)} wt m) | Inl (e' , StepLow fill1 step fill2) = Inl (_ , StepLow (FillLEnvUpRec (FillLEnvAsc fill1)) step (FillLEnvUpRec (FillLEnvAsc fill2)))
  StepsOrSettledSyn (_ , SynAsc {t = (_ , Old)} wt m) | Inr (SettledLowAna x) = Inr (SettledExceptAsc (settled-implies-settled-except x))

  
  StepsOrSettledAna : 
    ∀ {Γ e t} ->
    (Γ ⊢ e ⇐ t) ->
    Σ[ e' ∈ ExpLow ] (e Low↦ e') + (SettledLow e)
  StepsOrSettledAna wt = {!   !}

-- StepsOrSettled : (e : Program) ->
--   Σ[ e' ∈ Program ] (e P↦ e') + (PSettled e)
-- StepsOrSettled e = {!   !} 