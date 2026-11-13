module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqTermTargetSubstParameters
public import M6PA.Calibration.NumericPAeqTermTargetSubstTemplates
public import M6PA.Calibration.NumericPAeqTermBinaryConstructors
@[expose] public section

namespace M6.PA.NumericPAeqTerm
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource (language)
open RelationalSource.Ordinal (Term Formula)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem variableValue_targetSubst {n m w z x : V}
    (hw : IsSemitermVec language n m w) (hz : IsSemiterm language n z) (hx : IsSemiterm language n x) :
    subst language w (variableValue z x)=variableValue (termSubst language w z) (termSubst language w x) := by
  rw [variableValue,substs_and (domainCode_isSemiformula hz).isUFormula (show IsSemiformula language n (equalityCode z x) from templateTwo_isSemiformula equalityTemplate hz hx).isUFormula,
    domainCode_targetSubst hw hz,equalityCode_targetSubst hw hz hx]
  rfl

theorem zeroValue_targetSubst {n m w z : V} (hw : IsSemitermVec language n m w) (hz : IsSemiterm language n z) :
    subst language w (zeroValue z)=zeroValue (termSubst language w z) := by
  rw [zeroValue,substs_and (domainCode_isSemiformula hz).isUFormula (zeroCode_isSemiformula hz).isUFormula,
    domainCode_targetSubst hw hz,zeroCode_targetSubst hw hz]
  rfl

theorem successorValue_targetSubst {n m w z child : V} (hw : IsSemitermVec language n m w) (hz : IsSemiterm language n z)
    (hc : IsSemiformula language (n+1) child) :
    subst language w (successorValue z child)=successorValue (termSubst language w z) (subst language (qVec language w) child) := by
  have hs := successorCode_isSemiformula (show IsSemiterm language (n+1) (qqBvar 0) by simp) hz.termBShift
  rw [successorValue,substs_and (domainCode_isSemiformula hz).isUFormula
    ((IsSemiformula.exs.mpr (IsSemiformula.and.mpr ⟨hc,hs⟩)).isUFormula),
    substs_ex (IsSemiformula.and.mpr ⟨hc,hs⟩).isUFormula,
    substs_and hc.isUFormula hs.isUFormula,domainCode_targetSubst hw hz,
    successorCode_targetSubst hw.qVec (show IsSemiterm language (n+1) (qqBvar 0) by simp) hz.termBShift]
  rw [substs_qVec_bShift hz hw]
  simp [successorValue,qVec]

theorem binaryValue_targetSubst (p : Formula 3)
    {n m w z left right : V} (hw : IsSemitermVec language n m w) (hz : IsSemiterm language n z)
    (hl : IsSemiformula language ((n+1)+1) left)
    (hr : IsSemiformula language ((n+1)+1) right) :
    subst language w (binaryValue p z left right)=
      binaryValue p (termSubst language w z) (subst language (qVec language (qVec language w)) left) (subst language (qVec language (qVec language w)) right) := by
  have h1 : IsSemiterm language ((n+1)+1) (qqBvar 1) := by simp
  have h0 : IsSemiterm language ((n+1)+1) (qqBvar 0) := by simp
  have hs := templateThree_isSemiformula p h1 h0 hz.termBShift.termBShift
  have htail := IsSemiformula.and.mpr ⟨hr,hs⟩
  have hbody := IsSemiformula.and.mpr ⟨hl,htail⟩
  rw [binaryValue,substs_and (domainCode_isSemiformula hz).isUFormula
    (IsSemiformula.exs.mpr (IsSemiformula.exs.mpr hbody)).isUFormula,
    substs_ex (IsSemiformula.exs.mpr hbody).isUFormula,substs_ex hbody.isUFormula,
    substs_and hl.isUFormula htail.isUFormula,substs_and hr.isUFormula hs.isUFormula,
    domainCode_targetSubst hw hz,templateThree_targetSubst p hw.qVec.qVec h1 h0 hz.termBShift.termBShift]
  rw [substs_qVec_bShift hz.termBShift hw.qVec,substs_qVec_bShift hz hw]
  have hfirst : termSubst language (qVec language (qVec language w)) (qqBvar (1:V))=qqBvar 1 := by
    simpa [qVec] using (substs_qVec_bShift
      (show IsSemiterm language (n+1) (qqBvar (0:V)) by simp) hw.qVec)
  rw [hfirst]
  simp [binaryValue,qVec]

#print axioms variableValue_targetSubst
#print axioms zeroValue_targetSubst
#print axioms successorValue_targetSubst
#print axioms binaryValue_targetSubst
end M6.PA.NumericPAeqTerm

