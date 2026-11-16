module
public import M6PA.Theory
public import M6PA.Calibration.FoundationPAeqCodeInductionVectorReadback
@[expose] public section
namespace M6.PA.FoundationPAeqCode
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local notation "PAeq" => Presentation.language

theorem subst_imp_compat {m n p q w : V} (hp : IsSemiformula PAeq m p)
    (hq : IsSemiformula PAeq m q) (hw : IsSemitermVec PAeq m n w) :
    subst PAeq w (imp PAeq p q)=imp PAeq (subst PAeq w p) (subst PAeq w q) := by
  rw [imp,Bootstrapping.substs_or hp.neg.isUFormula hq.isUFormula,substs_neg hp hw]
  rfl

theorem closedSuccessorBody_readback {m q : V} (hq : IsSemiformula PAeq (m+1) q) :
    subst PAeq (fvarVec m) (closedSuccessorBody m q)=
      targetIndBody (subst PAeq (qVec PAeq (fvarVec m)) q) := by
  have hw := target_fvarVec_valid m 0
  have hwq : IsSemitermVec PAeq (m+1) 1 (qVec PAeq (fvarVec m)) := by simpa using hw.qVec
  have hb := hq.subst (closedBaseVector_valid m)
  have ht := hq.subst (closedStepVector_valid m)
  have hs : IsSemiformula PAeq (m+1) (imp PAeq q (subst PAeq (closedStepVector m) q)) := by simp [hq,ht]
  have ha : IsSemiformula PAeq m (qqAll (imp PAeq q (subst PAeq (closedStepVector m) q))) := by simpa using hs
  have hc : IsSemiformula PAeq m (qqAll q) := by simpa using hq
  have hr : IsSemiformula PAeq m (imp PAeq (qqAll (imp PAeq q (subst PAeq (closedStepVector m) q))) (qqAll q)) := by simp [ha,hc]
  unfold closedSuccessorBody
  rw [subst_imp_compat hb hr hw,subst_imp_compat ha hc hw,
    substs_all hs.isUFormula,substs_all hq.isUFormula,
    subst_imp_compat hq ht hw.qVec,
    substs_substs hq hw (closedBaseVector_valid m),closedBaseVector_readback,
    substs_substs hq hw.qVec (closedStepVector_valid m),closedStepVector_readback]
  have hz : IsSemitermVec (V:=V) PAeq 1 0 (zeroCode∷0) := by simp [zeroCode,Presentation.source_functions]
  have hsucc : IsSemitermVec (V:=V) PAeq 1 1 (qqFunc 1 1 (qqBvar 0∷0)∷0) := by simp [Presentation.source_functions]
  unfold targetIndBody
  simp only [paeqSubstCode_cast]
  rw [Presentation.quote_zero,Presentation.quote_successor]
  simp only [Semiterm.quote_bvar,Fin.val_zero,Nat.cast_zero]
  simp only [zeroCode] at hz ⊢
  rw [substs_substs hq hz hwq,substs_substs hq hsucc hwq,
    substVec_liftedFree m (by simp [zeroCode,Presentation.source_functions]),
    substVec_liftedFree m (by simp [Presentation.source_functions])]

#print axioms subst_imp_compat
#print axioms closedSuccessorBody_readback
end M6.PA.FoundationPAeqCode

