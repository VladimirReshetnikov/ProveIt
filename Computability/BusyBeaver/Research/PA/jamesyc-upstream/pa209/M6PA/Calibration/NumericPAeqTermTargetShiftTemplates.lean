module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqTermBinaryTemplates
public import M6PA.Calibration.PAForwardRelationalRewriting
@[expose] public section

/-! Target free-variable shift through capture-aware coded fixed templates.
The source arithmetic term is not substituted or shifted. -/
namespace M6.PA.NumericPAeqTerm
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource (language)
open RelationalSource.Ordinal (Term Formula)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem templateOne_targetShift (p : Formula 1) {n z : V}
    (hz : IsSemiterm language n z) :
    shift language (templateOne p z) = templateOne (Rewriting.shift p) (termShift language z) := by
  unfold templateOne substs1
  rw [shift_substs (show IsSemiformula language 1 (⌜p⌝ : V) by simpa using FFL.FirstOrder.Semiformula.quote_isSemiformula (V:=V) p) (m:=n) (by simp [hz])]
  rw [termShiftVec_cons₁ hz.isUTerm, ← FFL.FirstOrder.Semiformula.quote_shift]

theorem templateTwo_targetShift (p : Formula 2) {n x z : V}
    (hx : IsSemiterm language n x) (hz : IsSemiterm language n z) :
    shift language (templateTwo p x z) =
      templateTwo (Rewriting.shift p) (termShift language x) (termShift language z) := by
  unfold templateTwo
  rw [shift_substs (show IsSemiformula language 2 (⌜p⌝ : V) by simpa using FFL.FirstOrder.Semiformula.quote_isSemiformula (V:=V) p) (m:=n) (by simp [hx,hz])]
  rw [termShiftVec_cons₂ hx.isUTerm hz.isUTerm, ← FFL.FirstOrder.Semiformula.quote_shift]

theorem templateThree_targetShift (p : Formula 3) {n x y z : V}
    (hx : IsSemiterm language n x) (hy : IsSemiterm language n y) (hz : IsSemiterm language n z) :
    shift language (templateThree p x y z) =
      templateThree (Rewriting.shift p) (termShift language x) (termShift language y) (termShift language z) := by
  unfold templateThree
  rw [shift_substs (show IsSemiformula language 3 (⌜p⌝ : V) by simpa using FFL.FirstOrder.Semiformula.quote_isSemiformula (V:=V) p) (m:=n) (by simp [hx,hy,hz,show (3:V)=2+1 from two_add_one_eq_three.symm])]
  rw [show (3:V)=2+1 from two_add_one_eq_three.symm, termShiftVec_cons hx.isUTerm (by simp [hy.isUTerm,hz.isUTerm]), termShiftVec_cons₂ hy.isUTerm hz.isUTerm, ← FFL.FirstOrder.Semiformula.quote_shift]

@[simp] theorem domainTemplate_targetShift : Rewriting.shift domainTemplate = domainTemplate := by
  unfold domainTemplate
  change FFL.FirstOrder.Semiformula.rewAux Rew.shift _ = _
  rw [RelationalSource.Ordinal.domain_rew]
  rfl

@[simp] theorem zeroTemplate_targetShift : Rewriting.shift zeroTemplate = zeroTemplate := by
  unfold zeroTemplate
  change FFL.FirstOrder.Semiformula.rewAux Rew.shift _ = _
  rw [RelationalSource.Ordinal.zero_rew]
  rfl

@[simp] theorem successorTemplate_targetShift : Rewriting.shift successorTemplate = successorTemplate := by
  unfold successorTemplate
  change FFL.FirstOrder.Semiformula.rewAux Rew.shift _ = _
  rw [RelationalSource.Ordinal.successor_rew]
  rfl

@[simp] theorem additionTemplate_targetShift : Rewriting.shift additionTemplate = additionTemplate := by
  unfold additionTemplate
  change FFL.FirstOrder.Semiformula.rewAux Rew.shift _ = _
  rw [RelationalSource.PairGraph.addResult_rew]
  rfl

@[simp] theorem multiplicationTemplate_targetShift : Rewriting.shift multiplicationTemplate = multiplicationTemplate := by
  unfold multiplicationTemplate
  change FFL.FirstOrder.Semiformula.rewAux Rew.shift _ = _
  rw [RelationalSource.PairGraph.mulResult_rew]
  rfl

@[simp] theorem equalityTemplate_targetShift : Rewriting.shift equalityTemplate = equalityTemplate := by
  change Semiformula.rewAux Rew.shift _ = _
  simp [equalityTemplate, RelationalSource.ND.eq, Semiformula.rewAux]

theorem domainCode_targetShift {n z : V} (hz : IsSemiterm language n z) :
    shift language (domainCode z) = domainCode (termShift language z) := by
  simpa only [domainCode, domainTemplate_targetShift] using templateOne_targetShift domainTemplate hz

theorem zeroCode_targetShift {n z : V} (hz : IsSemiterm language n z) :
    shift language (zeroCode z) = zeroCode (termShift language z) := by
  simpa only [zeroCode, zeroTemplate_targetShift] using templateOne_targetShift zeroTemplate hz

theorem successorCode_targetShift {n x z : V} (hx : IsSemiterm language n x) (hz : IsSemiterm language n z) :
    shift language (successorCode x z) = successorCode (termShift language x) (termShift language z) := by
  simpa only [successorCode, successorTemplate_targetShift] using templateTwo_targetShift successorTemplate hx hz

theorem equalityCode_targetShift {n x z : V} (hx : IsSemiterm language n x) (hz : IsSemiterm language n z) :
    shift language (equalityCode x z) = equalityCode (termShift language x) (termShift language z) := by
  simpa only [equalityCode, equalityTemplate_targetShift] using templateTwo_targetShift equalityTemplate hx hz

theorem additionCode_targetShift {n x y z : V} (hx : IsSemiterm language n x) (hy : IsSemiterm language n y) (hz : IsSemiterm language n z) :
    shift language (additionCode x y z) = additionCode (termShift language x) (termShift language y) (termShift language z) := by
  simpa only [additionCode, additionTemplate_targetShift] using templateThree_targetShift additionTemplate hx hy hz

theorem multiplicationCode_targetShift {n x y z : V} (hx : IsSemiterm language n x) (hy : IsSemiterm language n y) (hz : IsSemiterm language n z) :
    shift language (multiplicationCode x y z) = multiplicationCode (termShift language x) (termShift language y) (termShift language z) := by
  simpa only [multiplicationCode, multiplicationTemplate_targetShift] using templateThree_targetShift multiplicationTemplate hx hy hz

#print axioms templateOne_targetShift
#print axioms templateTwo_targetShift
#print axioms templateThree_targetShift
#print axioms domainCode_targetShift
#print axioms zeroCode_targetShift
#print axioms successorCode_targetShift
#print axioms equalityCode_targetShift
#print axioms additionCode_targetShift
#print axioms multiplicationCode_targetShift

end M6.PA.NumericPAeqTerm

