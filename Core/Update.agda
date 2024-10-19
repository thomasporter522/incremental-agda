open import Data.Nat hiding (_+_)
open import Data.Unit 
open import Data.Bool hiding (_<_; _≟_)
open import Data.Sum renaming (_⊎_ to _+_; inj₁ to Inl ; inj₂ to Inr) hiding (map)
open import Data.Product hiding (map)
open import Relation.Binary.PropositionalEquality hiding (inspect)
open import Prelude

module Core.Update where

data BareType : Set where 
  BareTBase : BareType 
  BareTHole : BareType
  BareTArrow : BareType -> BareType -> BareType 

data BareExp : Set where 
  BareEConst : BareExp 
  BareEHole : BareExp
  BareEFun : BareType -> BareExp -> BareExp 
  BareEAp : BareExp -> BareExp -> BareExp 
  BareEVar : ℕ -> BareExp 

data HowNew : Set where 
  All : HowNew
  Some : HowNew

data NewData : Set where 
  Old : NewData
  New : HowNew -> NewData

mutual 
  Type : Set 
  Type = (TypeCon × NewData)

  data TypeCon : Set where 
    TBase : TypeCon
    THole : TypeCon
    TArrow : Type -> Type -> TypeCon 

ex : Type 
ex = (TArrow (TBase , Old) (THole , New All), New Some)

data MarkData : Set where 
  Marked : MarkData
  Unmarked : MarkData

data SynData : Set where 
  ̸⇑ : SynData
  ⇑ : Type -> SynData

data AnaData : Set where 
  ̸⇓ : AnaData
  ⇓ : Type -> AnaData

mutual 

  record ExpUp : Set where 
    inductive 
    constructor EUp
    field 
      syn : SynData
      mid : ExpMid

  data ExpMid : Set where 
    EConst : ExpMid 
    EHole : ExpMid
    EFun : Type -> MarkData -> ExpLow -> ExpMid 
    EAp : ExpLow -> MarkData -> ExpLow -> ExpMid 
    EVar : ℕ -> MarkData -> ExpMid 

  record ExpLow : Set where 
    inductive
    constructor ELow
    field 
      ana : AnaData
      mark : MarkData
      child : ExpUp

data _↦_ : ExpLow -> ExpLow -> Set where 
  HoleConsist : ∀ {t n} ->
    ELow (⇓ (t , New n)) Unmarked (EUp (⇑ (THole , Old)) EHole) ↦
    ELow (⇓ (t , Old)) Unmarked (EUp (⇑ (THole , Old)) EHole) 



data Ctx : Set where 
  ∅ : Ctx
  _,_ : BareType -> Ctx -> Ctx
  
data _,_∈_ : ℕ → BareType → Ctx → Set where 
  InCtx0 : ∀{Γ t} -> 0 , t ∈ (t , Γ)
  InCtxSuc : ∀{Γ t t' n} -> (n , t ∈ Γ) -> (suc n , t ∈ (t' , Γ)) 

OldenType : BareType -> Type
OldenType BareTBase = (TBase , Old)
OldenType BareTHole = (THole , Old)
OldenType (BareTArrow t1 t2) = (TArrow (OldenType t1) (OldenType t2) , Old)

-- Types correctly, hasn't reached a new

mutual 
  data _⊢_up⇒_ : (Γ : Ctx) (e : ExpUp) (t : BareType) → Set where 
    SynConst : ∀{Γ} ->
      Γ ⊢ (EUp (⇑ (TBase , Old)) EConst) up⇒ BareTBase
    SynHole : ∀{Γ} ->
      Γ ⊢ (EUp (⇑ (THole , Old)) EHole) up⇒ BareTHole
    SynFun : ∀{Γ bt1 bt2 t1 t2 m e} ->
      Γ ⊢ e low⇒ bt2 ->
      t1 ≡ OldenType bt1 ->
      t2 ≡ OldenType bt2 ->
      Γ ⊢ (EUp (⇑ (TArrow t1 t2 , Old)) (EFun t1 m e)) up⇒ (BareTArrow bt1 bt2)
    SynVar : ∀{Γ x t} ->
      x , t ∈ Γ ->
      Γ ⊢ (EUp (⇑ (THole , Old)) (EVar x Unmarked)) up⇒ t

  data _⊢_low⇒_ : (Γ : Ctx) (e : ExpLow) (t : BareType) → Set where 


