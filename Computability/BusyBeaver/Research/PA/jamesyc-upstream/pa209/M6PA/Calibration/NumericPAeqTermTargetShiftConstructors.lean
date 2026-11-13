module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqTermTargetShiftParameters
public import M6PA.Calibration.NumericPAeqTermBinaryConstructors
@[expose] public section

namespace M6.PA.NumericPAeqTerm
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource (language)
open RelationalSource.Ordinal (Term Formula)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem variableValue_targetShift {n z x : V}
    (hz : IsSemiterm language n z) (hx : IsSemiterm language n x) :
    shift language (variableValue z x)=variableValue (termShift language z) (termShift language x) := by
  rw [variableValue,shift_and (domainCode_isSemiformula hz).isUFormula (show IsSemiformula language n (equalityCode z x) from templateTwo_isSemiformula equalityTemplate hz hx).isUFormula,
    domainCode_targetShift hz,equalityCode_targetShift hz hx]
  rfl

theorem zeroValue_targetShift {n z : V} (hz : IsSemiterm language n z) :
    shift language (zeroValue z)=zeroValue (termShift language z) := by
  rw [zeroValue,shift_and (domainCode_isSemiformula hz).isUFormula (zeroCode_isSemiformula hz).isUFormula,
    domainCode_targetShift hz,zeroCode_targetShift hz]
  rfl

theorem successorValue_targetShift {n z child : V} (hz : IsSemiterm language n z)
    (hc : IsSemiformula language (n+1) child) :
    shift language (successorValue z child)=successorValue (termShift language z) (shift language child) := by
  have hs := successorCode_isSemiformula (show IsSemiterm language (n+1) (qqBvar 0) by simp) hz.termBShift
  rw [successorValue,shift_and (domainCode_isSemiformula hz).isUFormula
    ((IsSemiformula.exs.mpr (IsSemiformula.and.mpr ⟨hc,hs⟩)).isUFormula),
    shift_exs (IsSemiformula.and.mpr ⟨hc,hs⟩).isUFormula,
    shift_and hc.isUFormula hs.isUFormula,domainCode_targetShift hz,
    successorCode_targetShift (show IsSemiterm language (n+1) (qqBvar 0) by simp) hz.termBShift]
  simp [successorValue,termBShift_termShift hz]

theorem binaryValue_targetShift (p : Formula 3) (hp : Rewriting.shift p=p)
    {n z left right : V} (hz : IsSemiterm language n z)
    (hl : IsSemiformula language ((n+1)+1) left)
    (hr : IsSemiformula language ((n+1)+1) right) :
    shift language (binaryValue p z left right)=
      binaryValue p (termShift language z) (shift language left) (shift language right) := by
  have h1 : IsSemiterm language ((n+1)+1) (qqBvar 1) := by simp
  have h0 : IsSemiterm language ((n+1)+1) (qqBvar 0) := by simp
  have hs := templateThree_isSemiformula p h1 h0 hz.termBShift.termBShift
  have htail := IsSemiformula.and.mpr ⟨hr,hs⟩
  have hbody := IsSemiformula.and.mpr ⟨hl,htail⟩
  rw [binaryValue,shift_and (domainCode_isSemiformula hz).isUFormula
    (IsSemiformula.exs.mpr (IsSemiformula.exs.mpr hbody)).isUFormula,
    shift_exs (IsSemiformula.exs.mpr hbody).isUFormula,shift_exs hbody.isUFormula,
    shift_and hl.isUFormula htail.isUFormula,shift_and hr.isUFormula hs.isUFormula,
    domainCode_targetShift hz,templateThree_targetShift p h1 h0 hz.termBShift.termBShift]
  simp [binaryValue,hp,← termBShift_termShift hz.termBShift,← termBShift_termShift hz]

#print axioms variableValue_targetShift
#print axioms zeroValue_targetShift
#print axioms successorValue_targetShift
#print axioms binaryValue_targetShift
end M6.PA.NumericPAeqTerm

