open import Data.Nat hiding (_+_)
open import Data.Unit 
open import Data.Bool hiding (_<_; _≟_)
open import Data.Sum renaming (_⊎_ to _+_; inj₁ to Inl ; inj₂ to Inr) hiding (map)
open import Data.Product hiding (map)
open import Relation.Nullary 
open import Relation.Binary.PropositionalEquality hiding (inspect)
open import Prelude

module Core.Core where

data Type : Set where 
  TBase : Type 
  THole : Type
  TArrow : Type -> Type -> Type 

data BareExp : Set where 
  BareEConst : BareExp 
  BareEHole : BareExp
  BareEFun : Type -> BareExp -> BareExp 
  BareEAp : BareExp -> BareExp -> BareExp 
  BareEVar : ℕ -> BareExp 
  BareEAsc : Type -> BareExp -> BareExp 

data BareSubsumable : BareExp -> Set where 
  BareSubsumableConst : BareSubsumable BareEConst
  BareSubsumableHole : BareSubsumable BareEHole
  BareSubsumableAp : ∀ {e1 e2} → BareSubsumable (BareEAp e1 e2) 
  BareSubsumableVar : ∀ {x} → BareSubsumable (BareEVar x) 
  BareSubsumableAsc : ∀ {t e} → BareSubsumable (BareEAsc t e) 

data Newness : Set where 
  Old : Newness 
  New : Newness 
  -- NBase : Newness 
  -- NHole : Newness
  NArrow : Newness -> Newness -> Newness 

data IsNew : Newness -> Set where 
  IsNewNew : IsNew New
  IsNewArrow : ∀ {n1 n2} → IsNew (NArrow n1 n2)

data _~_ : Type -> Type -> Set where 
  ConsistBase : TBase ~ TBase
  ConsistHole1 : ∀ {t} → t ~ THole
  ConsistHole2 : ∀ {t} → THole ~ t
  ConsistArr : ∀ {t1 t2 t3 t4} → t1 ~ t3 → t2 ~ t4 → (TArrow t1 t2) ~ (TArrow t3 t4)

data _▸TArrow_,_ : Type -> Type -> Type -> Set where 
  MArrowHole : THole ▸TArrow THole , THole
  MArrowArrow : ∀ {t1 t2} → (TArrow t1 t2) ▸TArrow t1 , t2

data _̸▸TArrow : Type -> Set where 
  MArrowBase : TBase ̸▸TArrow

data _▸NArrow_,_ : Newness -> Newness -> Newness -> Set where 
  MNArrowOld : Old ▸NArrow Old , Old
  MNArrowNew : New ▸NArrow New , New
  MNArrowArrow : ∀ {n1 n2} → (NArrow n1 n2) ▸NArrow n1 , n2

narrow : Newness -> Newness -> Newness 
narrow Old Old = Old 
narrow New New = New 
narrow n1 n2 = NArrow n1 n2

NewType : Set 
NewType = (Type × Newness) 

data MarkData : Set where 
  Marked : MarkData
  Unmarked : MarkData

data SynData : Set where 
  ̸⇑ : SynData
  ⇑ : NewType -> SynData

data AnaData : Set where 
  ̸⇓ : AnaData
  ⇓ : NewType -> AnaData

-- data ExpPointer : Set where 
--   Here : ExpPointer 
--   PFun : ExpPointer -> ExpPointer
--   PAp1 : ExpPointer -> ExpPointer
--   PAp2 : ExpPointer -> ExpPointer
--   PAsc : ExpPointer -> ExpPointer

-- data ExpPointerSet : Set where 
--   P∅ : ExpPointerSet
--   _P,_ : ExpPointer -> ExpPointerSet -> ExpPointerSet

mutual 

  data ExpUp : Set where 
    EUp : SynData -> ExpMid -> ExpUp

  data ExpMid : Set where 
    EConst : ExpMid 
    EHole : ExpMid
    EFun : NewType -> MarkData -> ExpLow -> ExpMid 
    EAp : ExpLow -> MarkData -> ExpLow -> ExpMid 
    EVar : ℕ -> MarkData -> ExpMid 
    EAsc : NewType -> ExpLow -> ExpMid 

  data ExpLow : Set where 
    ELow : AnaData -> MarkData -> ExpUp -> ExpLow

data SubsumableMid : ExpMid -> Set where 
  SubsumableConst : SubsumableMid EConst
  SubsumableHole : SubsumableMid EHole
  SubsumableAp : ∀ {e1 m e2} → SubsumableMid (EAp e1 m e2) 
  SubsumableVar : ∀ {x m} → SubsumableMid (EVar x m) 
  SubsumableAsc : ∀ {t e} → SubsumableMid (EAsc t e) 

Subsumable : ExpUp -> Set 
Subsumable (EUp _ mid) = SubsumableMid mid

data Context (A : Set) : Set where 
  ∅ : Context A
  _,_ : A -> Context A -> Context A
  
data _,_∈_ {A : Set} : ℕ → A → (Context A) → Set where 
  InCtx0 : ∀ {Γ t} -> 0 , t ∈ (t , Γ)
  InCtxSuc : ∀ {Γ t t' n} -> (n , t ∈ Γ) -> (suc n , t ∈ (t' , Γ))

_̸∈_ : ∀ {A} -> ℕ → (Context A) → Set
x ̸∈ Γ = ∀ {t} -> ¬(x , t ∈ Γ)
