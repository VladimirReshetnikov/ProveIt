import ZFCinPA.ValidatorEnvironmentOpening254

set_option autoImplicit false
noncomputable section
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open _root_.SetTheory.BusyBeaver.ZFC.ArithmeticCode254
open LeanProofs.ZFCinPA.ValidatorEnvironmentLabels254
open LeanProofs.ZFCinPA.ValidatorEnvironmentOpening254
open scoped LO.FirstOrder.Arithmetic

#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentOpening254.ext_zero
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentOpening254.ext_cons
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentOpening254.openingVec_typed
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentOpening254.openingVec_succ
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentOpening254.term_labels_open
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentOpening254.vec_labels_open
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentOpening254.openAt_isSemiformula
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentOpening254.openAt_rel
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentOpening254.openAt_nrel
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentOpening254.openAt_verum
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentOpening254.openAt_falsum
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentOpening254.openAt_and
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentOpening254.openAt_or
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentOpening254.openAt_all
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentOpening254.openAt_exs
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentOpening254.encode_openAt
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentOpening254.encode_free
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentOpening254.encode_all_opened
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentOpening254.encode_exs_opened

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (x : V) : Ext (0 : V) 0 (x∷0) x := ext_zero x
example (d B B' x label : V) (h : Ext d B B' x) :
    Ext (d+1) (label∷B) (label∷B') x := ext_cons h label
example (d : V) : IsSemitermVec ℒₛₑₜ (d+1) d (openingVec d) := openingVec_typed d
example (d : V) : openingVec (d+1)=qVec ℒₛₑₜ (openingVec d) := openingVec_succ d
example (d t F B B' x : V) (ht : IsSemiterm ℒₛₑₜ (d+1) t) (h : Ext d B B' x) :
    TermLabels.term (x∷F) B (termOpenAt d t)=TermLabels.term F B' t :=
  term_labels_open ht F B B' x h
example (d k ts F B B' x : V) (ht : IsSemitermVec ℒₛₑₜ k (d+1) ts)
    (h : Ext d B B' x) :
    TermLabels.vec (x∷F) B k
      (termSubstVec ℒₛₑₜ k (openingVec d) (termShiftVec ℒₛₑₜ k ts))=
      TermLabels.vec F B' k ts := vec_labels_open ht F B B' x h
example (d p : V) (hp : IsSemiformula ℒₛₑₜ (d+1) p) :
    IsSemiformula ℒₛₑₜ d (openAt d p) := openAt_isSemiformula hp
example (d k R ts : V) (hr : (ℒₛₑₜ).IsRel k R) (ht : IsUTermVec ℒₛₑₜ k ts) :
    openAt d (^rel k R ts)=
      ^rel k R (termSubstVec ℒₛₑₜ k (openingVec d) (termShiftVec ℒₛₑₜ k ts)) :=
  openAt_rel d hr ht
example (d k R ts : V) (hr : (ℒₛₑₜ).IsRel k R) (ht : IsUTermVec ℒₛₑₜ k ts) :
    openAt d (^nrel k R ts)=
      ^nrel k R (termSubstVec ℒₛₑₜ k (openingVec d) (termShiftVec ℒₛₑₜ k ts)) :=
  openAt_nrel d hr ht
example (d : V) : openAt d (^⊤ : V)=^⊤ := openAt_verum d
example (d : V) : openAt d (^⊥ : V)=^⊥ := openAt_falsum d
example (d p q : V) (hp : IsUFormula ℒₛₑₜ p) (hq : IsUFormula ℒₛₑₜ q) :
    openAt d (p ^⋏ q)=openAt d p ^⋏ openAt d q := openAt_and d hp hq
example (d p q : V) (hp : IsUFormula ℒₛₑₜ p) (hq : IsUFormula ℒₛₑₜ q) :
    openAt d (p ^⋎ q)=openAt d p ^⋎ openAt d q := openAt_or d hp hq
example (d p : V) (hp : IsUFormula ℒₛₑₜ p) :
    openAt d (^∀ p)=^∀ (openAt (d+1) p) := openAt_all d hp
example (d p : V) (hp : IsUFormula ℒₛₑₜ p) :
    openAt d (^∃ p)=^∃ (openAt (d+1) p) := openAt_exs d hp
example (d p F B B' x s : V) (hp : IsSemiformula ℒₛₑₜ (d+1) p)
    (h : Ext d B B' x) :
    encode (x∷F) B s (openAt d p)=encode F B' s p := encode_openAt hp F B B' x s h
example (p F x s : V) (hp : IsSemiformula ℒₛₑₜ 1 p) :
    encode (x∷F) 0 s (free ℒₛₑₜ p)=encode F (x∷0) s p := encode_free hp F x s
example (p F x : V) (hp : IsSemiformula ℒₛₑₜ 1 p) :
    encode F 0 x (^∀ p)=wal x (encode (x∷F) 0 (x+2) (free ℒₛₑₜ p)) :=
  encode_all_opened hp F x
example (p F x : V) (hp : IsSemiformula ℒₛₑₜ 1 p) :
    encode F 0 x (^∃ p)=wim (wal x (wim (encode (x∷F) 0 (x+2) (free ℒₛₑₜ p)) 1)) 1 :=
  encode_exs_opened hp F x
example (p : V) (hp : IsSemiformula ℒₛₑₜ 1 p) :
    encode ((0 : V)∷0) 0 0 (free ℒₛₑₜ p)=encode 0 ((0 : V)∷0) 0 p :=
  encode_free hp 0 0 0
example (p F x s : V) (hp : IsSemiformula ℒₛₑₜ (1+1) p) :
    encode (x∷F) 0 s (free ℒₛₑₜ (^∀ p))=encode F (x∷0) s (^∀ p) :=
  encode_free (by simpa using hp) F x s
example (F x : V) : TermLabels.term (x∷F) 0 (termOpenAt 0 (^#0 : V))=x := by
  simpa using term_labels_open (d := 0) (source := (^#0 : V)) (by simp)
    F 0 (x∷0) x (ext_zero x)
