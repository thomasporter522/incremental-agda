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

NewType : Set 
NewType = (Type × Newness) 

data IsNew : Newness -> Set where 
  IsNewNew : IsNew New
  IsNewArrow : ∀ {n1 n2} → IsNew (NArrow n1 n2)

data _~_ : Type -> Type -> Set where 
  ConsistBase : TBase ~ TBase
  ConsistHole1 : ∀ {t} → t ~ THole
  ConsistHole2 : ∀ {t} → THole ~ t
  ConsistArr : ∀ {t1 t2 t3 t4} → t1 ~ t3 → t2 ~ t4 → (TArrow t1 t2) ~ (TArrow t3 t4)

data _▸Arrow_,_ : Type -> Type -> Type -> Set where 
  MArrowHole : THole ▸Arrow THole , THole
  MArrowArrow : ∀ {t1 t2} → (TArrow t1 t2) ▸Arrow t1 , t2

data _̸▸Arrow : Type -> Set where 
  MArrowBase : TBase ̸▸Arrow

data _▸NArrow_,_ : NewType -> NewType -> NewType -> Set where 
  MNArrowHoleOld : (THole , Old) ▸NArrow (THole , Old) , (THole , Old)
  MNArrowHoleNew : (THole , New) ▸NArrow (THole , New) , (THole , New)
  MNArrowArrowOld : ∀ {t1 t2} → (TArrow t1 t2 , Old) ▸NArrow (t1 , Old) , (t2 , Old)
  MNArrowArrowNew : ∀ {t1 t2} → (TArrow t1 t2 , New) ▸NArrow (t1 , New) , (t2 , New)
  MNArrowArrowNArrow : ∀ {t1 t2 n1 n2} → (TArrow t1 t2 , NArrow n1 n2) ▸NArrow (t1 , n1) , (t2 , n2)

data _̸▸NArrow : NewType -> Set where 
  MNArrowBase : ∀ {n} → (TBase , n) ̸▸NArrow

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
  StepAnaFun : ∀ {t t1 t2 tasc n n1 nasc m1 m2 m3 syn ana e} ->
    IsNew n ->
    (t , n) ▸NArrow (t1 , n1) , t2 ->
    tasc ~ t1 ->
    ELow (⇓ (t , n)) m1 (EUp syn (EFun (tasc , nasc) m2 (ELow ana m3 e))) L↦
    ELow (⇓ (t , Old)) Unmarked (EUp ̸⇑ (EFun (tasc , nasc) Unmarked (ELow (⇓ t2) m3 e)))
  StepAnaFunFail1 : ∀ {t t1 t2 tasc n n1 nasc m1 m2 m3 syn ana e} ->
    IsNew n ->
    (t , n) ▸NArrow (t1 , n1) , t2 ->
    ¬(tasc ~ t1) ->
    ELow (⇓ (t , n)) m1 (EUp syn (EFun (tasc , nasc) m2 (ELow ana m3 e))) L↦
    ELow (⇓ (t , Old)) Unmarked (EUp ̸⇑ (EFun (tasc , nasc) Marked (ELow (⇓ t2) m3 e)))
  StepAnaFunFail2 : ∀ {t asc n m1 m2 m3 ana e} ->
    IsNew n ->
    (t , n) ̸▸NArrow ->
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
  StepNewAnnFun2 :  ∀ {syn oldt1 oldt2 oldn1 oldn2 t1 n1 m t2 n2 e e'} ->
    IsNew n2 ->
    syn ▸NArrow (oldt1 , oldn1) , (oldt2 , oldn2) ->
    VarsSynthesize 0 (t1 , n1) (EUp (⇑ (t2 , n2)) e) e' ->
    EUp (⇑ syn) (EFun (t1 , n1) Unmarked (ELow ̸⇓ m (EUp (⇑ (t2 , n2)) e))) U↦
    EUp (⇑ (TArrow t1 oldt2 , NArrow n1 oldn2)) (EFun (t1 , Old) Unmarked (ELow ̸⇓ m e'))
  StepNewSynFun1 : ∀ {t1 n1 m t2 n2 e} ->
    IsNew n2 ->
    EUp ̸⇑ (EFun (t1 , n1) Unmarked (ELow ̸⇓ m (EUp (⇑ (t2 , n2)) e))) U↦
    EUp (⇑ (TArrow t1 t2 , New)) (EFun (t1 , n1) Unmarked (ELow ̸⇓ m (EUp (⇑ (t2 , Old)) e)))
  StepNewSynFun2 : ∀ {syn oldt1 oldt2 oldn1 oldn2 t1 n1 m t2 n2 e} ->
    IsNew n2 ->
    syn ▸NArrow (oldt1 , oldn1) , (oldt2 , oldn2) ->
    EUp (⇑ syn) (EFun (t1 , n1) Unmarked (ELow ̸⇓ m (EUp (⇑ (t2 , n2)) e))) U↦
    EUp (⇑ (TArrow oldt1 t2 , NArrow oldn1 n2)) (EFun (t1 , n1) Unmarked (ELow ̸⇓ m (EUp (⇑ (t2 , Old)) e)))
  StepVoidSynFun : ∀ {t1 n1 m t2 n2 e} ->
    EUp ̸⇑ (EFun (t1 , n1) Unmarked (ELow ̸⇓ m (EUp (⇑ (t2 , n2)) e))) U↦
    EUp (⇑ (TArrow t1 t2 , New)) (EFun (t1 , n1) Unmarked (ELow ̸⇓ m (EUp (⇑ (t2 , Old)) e)))
  -- Ap Step
  StepAp : ∀ {t n t1 t2 syn ana e1 e2 m1 m2} ->
    IsNew n ->
    (t , n) ▸NArrow t1 , t2 ->
    EUp syn (EAp (ELow ̸⇓ Unmarked (EUp (⇑ (t , n)) e1)) m1 (ELow ana m2 e2)) U↦
    EUp (⇑ t1) (EAp (ELow ̸⇓ Unmarked (EUp (⇑ (t , Old)) e1)) Unmarked (ELow (⇓ t1) m2 e2))
  -- Asc Step
  StepAsc : ∀ {syn t n ana m e} ->
    IsNew n ->
    EUp syn (EAsc (t , n) (ELow ana m e)) U↦
    EUp (⇑ (t , n)) (EAsc (t , Old) (ELow (⇓ (t , n)) m e))


data Ctx : Set where 
  ∅ : Ctx
  _,_ : Type -> Ctx -> Ctx
  
data _,_∈_ : ℕ → Type → Ctx → Set where 
  InCtx0 : ∀{Γ t} -> 0 , t ∈ (t , Γ)
  InCtxSuc : ∀{Γ t t' n} -> (n , t ∈ Γ) -> (suc n , t ∈ (t' , Γ))


_̸∈_ : ℕ → Ctx → Set
x ̸∈ Γ = ∀{t} -> ¬(x , t ∈ Γ)

-- data _̸∈_ : ℕ → Ctx → Set where 
--   NotInEmpty : ∀{x} -> x ̸∈ ∅
--   NotInExtend : ∀{Γ x y} -> (x ̸∈ Γ) -> ¬(x ≡ y) -> (x ̸∈ (y , Γ)) 

-- Types correctly, hasn't reached a new
mutual 
  data _⊢_⇒_ : (Γ : Ctx) (e : ExpUp) (t : Type) → Set where 
    SynConst : ∀{Γ} ->
      Γ ⊢ (EUp (⇑ (TBase , Old)) EConst) ⇒ TBase
    SynHole : ∀{Γ} ->
      Γ ⊢ (EUp (⇑ (THole , Old)) EHole) ⇒ THole
    SynFun : ∀{Γ t1 t2 e} ->
      (t1 , Γ) ⊢ e ⇒ t2 ->
      Γ ⊢ (EUp (⇑ (TArrow t1 t2 , Old)) (EFun (t1 , Old) Unmarked (ELow ̸⇓ Unmarked e))) ⇒ (TArrow t1 t2)
    SynAp : ∀{Γ t t1 t2 e1 e2} ->
      Γ ⊢ e1 ⇒ t ->
      t ▸Arrow t1 , t2 ->
      Γ ⊢ e2 ⇐ t1 ->
      Γ ⊢ (EUp (⇑ (t2 , Old)) (EAp (ELow ̸⇓ Unmarked e1) Unmarked e2)) ⇒ t2
    SynVar : ∀{Γ x t} ->
      x , t ∈ Γ ->
      Γ ⊢ (EUp (⇑ (t , Old)) (EVar x Unmarked)) ⇒ t
    SynVarFail : ∀{Γ x t} ->
      x ̸∈ Γ ->
      Γ ⊢ (EUp (⇑ (THole , Old)) (EVar x Marked)) ⇒ t
    SynAsc : ∀{Γ t e} ->
      Γ ⊢ e ⇐ t ->
      Γ ⊢ (EUp (⇑ (t , Old)) (EAsc (t , Old) e)) ⇒ t

  data _⊢_⇐_ : (Γ : Ctx) (e : ExpLow) (t : Type) → Set where 
    AnaSubsume : ∀{Γ t1 t2 e} ->
      Γ ⊢ e ⇒ t1 ->
      Subsumable e ->
      (t1 ~ t2) ->
      Γ ⊢ (ELow (⇓ (t2 , Old)) Unmarked e) ⇐ t2
    AnaSubsumeFail : ∀{Γ t1 t2 e} ->
      Γ ⊢ e ⇒ t1 ->
      Subsumable e ->
      ¬(t1 ~ t2) ->
      Γ ⊢ (ELow (⇓ (t2 , Old)) Marked e) ⇐ t2
    AnaFun : ∀{Γ t t1 t2 tasc e} ->
      t ▸Arrow t1 , t2 ->
      (tasc , Γ) ⊢ e ⇐ t2 ->
      tasc ~ t1 ->
      Γ ⊢ (ELow (⇓ (t , Old)) Unmarked (EUp ̸⇑ (EFun (tasc , Old) Unmarked e))) ⇐ t
    AnaFunFail1 : ∀{Γ t t1 t2 tasc e} ->
      t ▸Arrow t1 , t2 ->
      (tasc , Γ) ⊢ e ⇐ t2 ->
      ¬(tasc ~ t1) ->
      Γ ⊢ (ELow (⇓ (t , Old)) Unmarked (EUp ̸⇑ (EFun (tasc , Old) Marked e))) ⇐ t
    -- Paper version:
    -- AnaFunFail2 : ∀{Γ bt t tasc btasc e} ->
    --   t ̸▸Arrow ->
    --   (tasc , Γ) ⊢ e ⇐ THole ->
    --   Γ ⊢ (ELow (⇓ (TOld t)) Unmarked (EUp ̸⇑ (EFun (TOld tasc) Marked e))) ⇐ t
    -- My version:
    AnaFunFail2 : ∀{Γ t t2 tasc e} ->
      t ̸▸Arrow ->
      (tasc , Γ) ⊢ e ⇒ t2 ->
      Γ ⊢ (ELow (⇓ (t , Old)) Marked (EUp (⇑ (t2 , Old)) (EFun (tasc , Old) Unmarked (ELow ̸⇓ Unmarked e)))) ⇐ t

