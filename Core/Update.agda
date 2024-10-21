open import Data.Nat hiding (_+_)
open import Data.Unit 
open import Data.Bool hiding (_<_; _≟_)
open import Data.Sum renaming (_⊎_ to _+_; inj₁ to Inl ; inj₂ to Inr) hiding (map)
open import Data.Product hiding (map)
open import Relation.Nullary 
open import Relation.Binary.PropositionalEquality hiding (inspect)
open import Prelude

module Core.Update where

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

  record ExpUp : Set where 
    inductive 
    constructor EUp
    field 
      syn : SynData
      mid : ExpMid

  data ExpMid : Set where 
    EConst : ExpMid 
    EHole : ExpMid
    EFun : NewType -> MarkData -> ExpLow -> ExpMid 
    EAp : ExpLow -> MarkData -> ExpLow -> ExpMid 
    EVar : ℕ -> MarkData -> ExpMid 
    EAsc : NewType -> ExpLow -> ExpMid 

  record ExpLow : Set where 
    inductive
    constructor ELow
    field 
      ana : AnaData
      mark : MarkData
      child : ExpUp

data SubsumableMid : ExpMid -> Set where 
  SubsumableConst : SubsumableMid EConst
  SubsumableHole : SubsumableMid EHole
  SubsumableAp : ∀ {e1 m e2} → SubsumableMid (EAp e1 m e2) 
  SubsumableVar : ∀ {x m} → SubsumableMid (EVar x m) 
  SubsumableAsc : ∀ {t e} → SubsumableMid (EAsc t e) 

Subsumable : ExpUp -> Set 
Subsumable (EUp _ mid) = SubsumableMid mid

-- data AnaStuckOnFun : AnaData -> Set where 
--   NoAnaStuck : AnaStuckOnFun ̸⇓ 
--   NMArrowStuck : ana ̸▸NArrow -> AnaStuckOnFun (⇓ ana)

-- data VarsSynthesize : ℕ -> NewType -> ExpUp -> ExpUp -> Set where 


data VarsSynthesize : ℕ -> NewType -> ExpUp -> ExpUp -> Set where 
  VSConst : ∀ {x t syn} ->
    VarsSynthesize x t (EUp syn EConst) (EUp syn EConst)
  VSHole : ∀ {x t syn} ->
    VarsSynthesize x t (EUp syn EHole) (EUp syn EHole)
  VSFun : ∀ {x t syn asc ana m1 m2 e e'} ->
    VarsSynthesize (suc x) t e e' ->
    VarsSynthesize x t (EUp syn (EFun asc m1 (ELow ana m2 e))) (EUp syn (EFun asc m1 (ELow ana m2 e')))
  VSAp : ∀ {x t syn e1 e2 e1' e2' ana1 ana2 m1 m2 m3} ->
    VarsSynthesize x t e1 e1' ->
    VarsSynthesize x t e2 e2' ->
    VarsSynthesize x t (EUp syn (EAp (ELow ana1 m1 e1) m2 (ELow ana2 m3 e2))) (EUp syn (EAp (ELow ana1 m1 e1') m2 (ELow ana2 m3 e2')))
  VSVar : ∀ {x t syn} ->
    VarsSynthesize x t (EUp syn (EVar x Unmarked)) (EUp (⇑ t) (EVar x Unmarked))
  VSAsc : ∀ {x t syn asc e e' ana m} ->
    VarsSynthesize x t e e' ->
    VarsSynthesize x t (EUp syn (EAsc asc (ELow ana m e))) (EUp syn (EAsc asc (ELow ana m e')))


data _L↦_ : ExpLow -> ExpLow -> Set where 
  -- NewSyn Steps
  StepNewSynConsist : ∀ {t1 t2 m n e} ->
    IsNew n ->
    t1 ~ t2 ->
    ELow (⇓ (t1 , Old)) m (EUp (⇑ (t2 , n)) e) L↦
    ELow (⇓ (t1 , Old)) Unmarked (EUp (⇑ (t2 , Old)) e) 
  StepNewSynInonsist : ∀ {t1 t2 m n e} ->
    IsNew n ->
    ¬(t1 ~ t2) ->
    ELow (⇓ (t1 , Old)) m (EUp (⇑ (t2 , n)) e) L↦
    ELow (⇓ (t1 , Old)) Marked (EUp (⇑ (t2 , Old)) e) 
  -- NewAna Steps
  StepNewAnaConsist : ∀ {t1 t2 n1 n2 m e} ->
    IsNew n1 ->
    SubsumableMid e -> 
    t1 ~ t2 ->
    ELow (⇓ (t1 , n1)) m (EUp (⇑ (t2 , n2)) e) L↦
    ELow (⇓ (t1 , Old)) Unmarked (EUp (⇑ (t2 , Old)) e) 
  StepNewAnaInonsist : ∀ {t1 t2 n1 n2 m e} ->
    IsNew n1 ->
    SubsumableMid e -> 
    ¬(t1 ~ t2) ->
    ELow (⇓ (t1 , n1)) m (EUp (⇑ (t2 , n2)) e) L↦
    ELow (⇓ (t1 , Old)) Marked (EUp (⇑ (t2 , Old)) e) 
  -- Fun Steps
  StepAnaFun : ∀ {t t1 t2 tasc n n1 n2 nasc m1 m2 m3 syn ana e} ->
    IsNew n ->
    t ▸TArrow t1 , t2 ->
    n ▸NArrow n1 , n2 ->
    tasc ~ t1 ->
    ELow (⇓ (t , n)) m1 (EUp syn (EFun (tasc , nasc) m2 (ELow ana m3 e))) L↦
    ELow (⇓ (t , Old)) Unmarked (EUp ̸⇑ (EFun (tasc , nasc) Unmarked (ELow (⇓ (t2 , n2)) m3 e)))
  StepAnaFunFail1 : ∀ {t t1 t2 tasc n n1 n2 nasc m1 m2 m3 syn ana e} ->
    IsNew n ->
    t ▸TArrow t1 , t2 ->
    n ▸NArrow n1 , n2 ->
    ¬(tasc ~ t1) ->
    ELow (⇓ (t , n)) m1 (EUp syn (EFun (tasc , nasc) m2 (ELow ana m3 e))) L↦
    ELow (⇓ (t , Old)) Unmarked (EUp ̸⇑ (EFun (tasc , nasc) Marked (ELow (⇓ (t2 , n2)) m3 e)))
  StepAnaFunFail2 : ∀ {t asc n m1 m2 m3 ana e} ->
    IsNew n ->
    t ̸▸TArrow ->
    ELow (⇓ (t , n)) m1 (EUp ̸⇑ (EFun asc m2 (ELow (⇓ ana) m3 e))) L↦
    ELow (⇓ (t , Old)) Unmarked (EUp ̸⇑ (EFun asc Unmarked (ELow ̸⇓ Unmarked e)))
  StepNoAnaFun : ∀ {asc m1 m2 ana e} ->
    ELow ̸⇓ Unmarked (EUp ̸⇑ (EFun asc m1 (ELow (⇓ ana) m2 e))) L↦
    ELow ̸⇓ Unmarked (EUp ̸⇑ (EFun asc m1 (ELow ̸⇓ Unmarked e)))

data _U↦_ : ExpUp -> ExpUp -> Set where 
  -- Fun Steps
  -- (Two annotation rules)
  StepNewAnnFun1 : ∀ {t1 n1 m t2 n2 e e'} ->
    IsNew n1 ->
    VarsSynthesize 0 (t1 , n1) (EUp (⇑ (t2 , n2)) e) e' ->
    EUp ̸⇑ (EFun (t1 , n1) Unmarked (ELow ̸⇓ m (EUp (⇑ (t2 , n2)) e))) U↦
    EUp (⇑ (TArrow t1 t2 , New)) (EFun (t1 , Old) Unmarked (ELow ̸⇓ m e'))
  StepNewAnnFun2 :  ∀ {t n oldt1 oldt2 oldn1 oldn2 t1 n1 m t2 n2 e e'} ->
    IsNew n2 ->
    t ▸TArrow oldt1 , oldt2 ->
    n ▸NArrow oldn1 , oldn2 ->
    VarsSynthesize 0 (t1 , n1) (EUp (⇑ (t2 , n2)) e) e' ->
    EUp (⇑ (t , n)) (EFun (t1 , n1) Unmarked (ELow ̸⇓ m (EUp (⇑ (t2 , n2)) e))) U↦
    EUp (⇑ (TArrow t1 oldt2 , NArrow n1 oldn2)) (EFun (t1 , Old) Unmarked (ELow ̸⇓ m e'))
  StepNewSynFun1 : ∀ {t1 n1 m t2 n2 e} ->
    IsNew n2 ->
    EUp ̸⇑ (EFun (t1 , n1) Unmarked (ELow ̸⇓ m (EUp (⇑ (t2 , n2)) e))) U↦
    EUp (⇑ (TArrow t1 t2 , New)) (EFun (t1 , n1) Unmarked (ELow ̸⇓ m (EUp (⇑ (t2 , Old)) e)))
  StepNewSynFun2 : ∀ {t n oldt1 oldt2 oldn1 oldn2 t1 n1 m t2 n2 e} ->
    IsNew n2 ->
    t ▸TArrow oldt1 , oldt2 ->
    n ▸NArrow oldn1 , oldn2 ->
    EUp (⇑ (t , n)) (EFun (t1 , n1) Unmarked (ELow ̸⇓ m (EUp (⇑ (t2 , n2)) e))) U↦
    EUp (⇑ (TArrow oldt1 t2 , NArrow oldn1 n2)) (EFun (t1 , n1) Unmarked (ELow ̸⇓ m (EUp (⇑ (t2 , Old)) e)))
  StepVoidSynFun : ∀ {t1 n1 m t2 n2 e} ->
    EUp ̸⇑ (EFun (t1 , n1) Unmarked (ELow ̸⇓ m (EUp (⇑ (t2 , n2)) e))) U↦
    EUp (⇑ (TArrow t1 t2 , New)) (EFun (t1 , n1) Unmarked (ELow ̸⇓ m (EUp (⇑ (t2 , Old)) e)))
  -- Ap Step
  StepAp : ∀ {t n t1 t2 n1 n2 syn ana e1 e2 m1 m2} ->
    IsNew n ->
    t ▸TArrow t1 , t2 ->
    n ▸NArrow n1 , n2 ->
    EUp syn (EAp (ELow ̸⇓ Unmarked (EUp (⇑ (t , n)) e1)) m1 (ELow ana m2 e2)) U↦
    EUp (⇑ (t1 , n1)) (EAp (ELow ̸⇓ Unmarked (EUp (⇑ (t , Old)) e1)) Unmarked (ELow (⇓ (t1 , n1)) m2 e2))
  -- Asc Step
  StepAsc : ∀ {syn t n ana m e} ->
    IsNew n ->
    EUp syn (EAsc (t , n) (ELow ana m e)) U↦
    EUp (⇑ (t , n)) (EAsc (t , Old) (ELow (⇓ (t , n)) m e))

data Ctx : Set where 
  ∅ : Ctx
  _,_ : NewType -> Ctx -> Ctx
  
data _,_∈_ : ℕ → NewType → Ctx → Set where 
  InCtx0 : ∀{Γ t} -> 0 , t ∈ (t , Γ)
  InCtxSuc : ∀{Γ t t' n} -> (n , t ∈ Γ) -> (suc n , t ∈ (t' , Γ))

_̸∈_ : ℕ → Ctx → Set
x ̸∈ Γ = ∀{t} -> ¬(x , t ∈ Γ)


-- MergeInfo (t1 , n1) (t2 , n2) (t3 , n3) holds with:
-- (t1 , n1) is the stored info
-- (t2 , n2) is the calculated true info 
-- (t3 , n3) is the info that should be passed along
-- and ensures that the stored info is compatible with the real info.
-- This is the case when t1 and t2 are the same at the points where n2 is old. 
-- Where n2 is all new, the "real" info hasn't been propagated yet and doesn't 
-- need to have been stored already. It doesn't matter whether n1 is new or old. 

data MergeInfo : NewType -> NewType -> NewType -> Set where 
  MergeInfoNew : ∀{t1 t2 n1} -> 
    MergeInfo (t1 , n1) (t2 , New) (t2 , New)
  MergeInfoOld : ∀{t1 n1} -> 
    MergeInfo (t1 , n1) (t1 , Old) (t1 , n1)
  MergeInfoArrow : ∀{t1 t2 t3 t4 t5 t6 n n1 n2 n3 n4 n5 n6} -> 
    n ▸NArrow n1 , n2 ->
    MergeInfo (t1 , n1) (t3 , n3) (t5 , n5) ->
    MergeInfo (t2 , n2) (t4 , n4) (t6 , n6) ->
    MergeInfo (TArrow t1 t2 , n) (TArrow t3 t4 , NArrow n3 n4) (TArrow t5 t6 , narrow n5 n6)

mutual 
  data _⊢_⇒_ : (Γ : Ctx) (e : ExpUp) (t : NewType) → Set where 
    SynConst : ∀{Γ info syn} ->
      MergeInfo info (TBase , Old) syn -> 
      Γ ⊢ (EUp (⇑ info) EConst) ⇒ syn
    SynHole : ∀{Γ info syn} ->
      MergeInfo info (THole , Old) syn -> 
      Γ ⊢ (EUp (⇑ info) EHole) ⇒ syn
    SynFun : ∀{Γ info t1 t2 n1 n2 syn e} ->
      ((t1 , n1) , Γ) ⊢ e ⇒ (t2 , n2) ->
      MergeInfo info (TArrow t1 t2 , narrow n1 n2) syn -> 
      Γ ⊢ (EUp (⇑ info) (EFun (t1 , n1) Unmarked (ELow ̸⇓ Unmarked e))) ⇒ syn
    SynFunVoid : ∀{Γ t1 t2 n1 n2 ana e} ->
      ((t1 , n1) , Γ) ⊢ e ⇒ (t2 , n2) ->
      Γ ⊢ (EUp ̸⇑ (EFun (t1 , n1) Unmarked (ELow ana Unmarked e))) ⇒ (TArrow t1 t2 , New)
    SynAp : ∀{Γ info t t1 t2 n n1 n2 e1 e2 syn} ->
      Γ ⊢ e1 ⇒ (t , n) ->
      t ▸TArrow t1 , t2 ->
      n ▸NArrow n1 , n2 ->
      Γ ⊢ e2 ⇐ (t1 , n1) ->
      MergeInfo info (t2 , n2) syn -> 
      Γ ⊢ (EUp (⇑ info) (EAp (ELow ̸⇓ Unmarked e1) Unmarked e2)) ⇒ syn
    SynVar : ∀{Γ info x t syn} ->
      x , t ∈ Γ ->
      MergeInfo info t syn -> 
      Γ ⊢ (EUp (⇑ info) (EVar x Unmarked)) ⇒ syn
    SynVarFail : ∀{Γ info x syn} ->
      x ̸∈ Γ ->
      MergeInfo info (THole , Old) syn -> 
      Γ ⊢ (EUp (⇑ info) (EVar x Marked)) ⇒ syn
    SynAsc : ∀{Γ info t e syn} ->
      Γ ⊢ e ⇐ t ->
      MergeInfo info t syn -> 
      Γ ⊢ (EUp (⇑ info) (EAsc t e)) ⇒ syn

  data _⊢_⇐_ : (Γ : Ctx) (e : ExpLow) (t : NewType) → Set where 
    AnaSubsume : ∀{Γ info ana t1 t2 n1 n2 e} ->
      MergeInfo info ana (t2 , n2) -> 
      Γ ⊢ e ⇒ (t1 , n1) ->
      Subsumable e ->
      (t1 ~ t2) ->
      Γ ⊢ (ELow (⇓ info) Unmarked e) ⇐ ana
    AnaSubsumeFail : ∀{Γ info ana t1 t2 n1 n2 e} ->
      MergeInfo info ana (t2 , n2) -> 
      Γ ⊢ e ⇒ (t1 , n1) ->
      Subsumable e ->
      ¬(t1 ~ t2) ->
      Γ ⊢ (ELow (⇓ info) Marked e) ⇐ ana
    AnaFun : ∀{Γ info ana t t1 t2 n n1 n2 tasc nasc e} ->
      MergeInfo info ana (t , n) -> 
      t ▸TArrow t1 , t2 ->
      n ▸NArrow n1 , n2 ->
      ((tasc , nasc) , Γ) ⊢ e ⇐ (t2 , n2) ->
      (tasc ~ t1) ->
      Γ ⊢ (ELow (⇓ info) Unmarked (EUp ̸⇑ (EFun (tasc , nasc) Unmarked e))) ⇐ ana
    AnaFunFail1 : ∀{Γ info ana t t1 t2 n n1 n2 tasc nasc e} ->
      MergeInfo info ana (t , n) -> 
      t ▸TArrow t1 , t2 ->
      n ▸NArrow n1 , n2 ->
      ((tasc , nasc) , Γ) ⊢ e ⇐ (t2 , n2) ->
      ¬(tasc ~ t1) ->
      Γ ⊢ (ELow (⇓ info) Unmarked (EUp ̸⇑ (EFun (tasc , nasc) Marked e))) ⇐ ana
    -- Paper version: analyzes the body against ? if the lambda analyzed against non-arrow
    -- My version:
    AnaFunFail2 : ∀{Γ syn-info ana-info syn-info' ana syn t tasc n nasc e} ->
      MergeInfo ana-info ana (t , n) -> 
      t ̸▸TArrow ->
      ((tasc , nasc) , Γ) ⊢ e ⇒ syn ->
      MergeInfo syn-info syn syn-info' -> 
      Γ ⊢ (ELow (⇓ ana-info) Marked (EUp (⇑ syn-info) (EFun (tasc , nasc) Unmarked (ELow ̸⇓ Unmarked e)))) ⇐ ana


data Settled : ExpUp -> Set where 
  SettledConst : ∀{t} ->
    Settled (EUp (⇑ (t , Old)) EConst)
  SettledHole : ∀{t} ->
    Settled (EUp (⇑ (t , Old)) EHole)
  SettledFunSyn : ∀{t1 t2 m1 m2 e} ->
    Settled (EUp (⇑ (t1 , Old)) (EFun (t2 , Old) m1 (ELow ̸⇓ m2 e)))
  SettledFunAna : ∀{t1 t2 m1 m2 e} ->
    Settled (EUp ̸⇑ (EFun (t1 , Old) m1 (ELow (⇓ (t2 , Old)) m2 e)))
  SettledAp : ∀{t1 t2 m1 m2 m3 e1 e2} ->
    Settled e1 -> 
    Settled e2 -> 
    Settled (EUp (⇑ (t1 , Old)) (EAp (ELow ̸⇓ m1 e1) m2 (ELow (⇓ (t2 , Old)) m3 e2)))
  SettledVar : ∀{t x m} ->
    Settled (EUp (⇑ (t , Old)) (EVar x m))
  SettledAsc : ∀{t1 t2 t3 m e} ->
    Settled e -> 
    Settled (EUp (⇑ (t1 , Old)) (EAsc (t2 , Old) (ELow (⇓ (t3 , Old)) m e)))

 
 -- (Well-formed predicate)
 -- Well-typed predicate
 -- Settled predicate
 -- Marked exp -> bare exp
 -- Bare exp -> marked exp (from scratch marking)

 -- Actions and update steps preserve well-typedness
 -- Settled, well-typed -> agrees with from-scratch
 -- Either settled or can step 
 -- Termination :)

 -- Now the original big theorem follows from action commutativity
 -- Which I don't even know how I'd express honestly
 -- So maybe I just leave it to the above. 