module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqTermBinaryTemplates
@[expose] public section

/-! Target bound substitution through fixed relational templates. Source
arithmetic syntax is unchanged; every target vector/term arity is explicit. -/
namespace M6.PA.NumericPAeqTerm
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource (language)
open RelationalSource.Ordinal (Term Formula)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem templateOne_targetSubst (p : Formula 1) {n m w z : V}
    (hw:IsSemitermVec language n m w) (hz:IsSemiterm language n z) :
    subst language w (templateOne p z)=templateOne p (termSubst language w z) := by
  unfold templateOne substs1
  rw [substs_substs (show IsSemiformula language 1 (⌜p⌝:V) by simpa using FFL.FirstOrder.Semiformula.quote_isSemiformula (V:=V) p) hw
    (IsSemitermVec.singleton.mpr hz)]
  rw [termSubstVec_cons₁ hz.isUTerm]

theorem templateTwo_targetSubst (p : Formula 2) {n m w x z : V}
    (hw:IsSemitermVec language n m w) (hx:IsSemiterm language n x) (hz:IsSemiterm language n z) :
    subst language w (templateTwo p x z)=
      templateTwo p (termSubst language w x) (termSubst language w z) := by
  unfold templateTwo
  rw [substs_substs (show IsSemiformula language 2 (⌜p⌝:V) by simpa using FFL.FirstOrder.Semiformula.quote_isSemiformula (V:=V) p) hw (by simp [hx,hz]),
    termSubstVec_cons₂ hx.isUTerm hz.isUTerm]

theorem templateThree_targetSubst (p : Formula 3) {n m w x y z : V}
    (hw:IsSemitermVec language n m w) (hx:IsSemiterm language n x)
    (hy:IsSemiterm language n y) (hz:IsSemiterm language n z) :
    subst language w (templateThree p x y z)=
      templateThree p (termSubst language w x) (termSubst language w y) (termSubst language w z) := by
  unfold templateThree
  rw [substs_substs (show IsSemiformula language 3 (⌜p⌝:V) by simpa using FFL.FirstOrder.Semiformula.quote_isSemiformula (V:=V) p) hw
    (by simp [hx,hy,hz,show (3:V)=2+1 from two_add_one_eq_three.symm])]
  rw [show (3:V)=2+1 from two_add_one_eq_three.symm,
    termSubstVec_cons hx.isUTerm (by simp [hy.isUTerm,hz.isUTerm]),termSubstVec_cons₂ hy.isUTerm hz.isUTerm]

theorem domainCode_targetSubst {n m w z : V} (hw:IsSemitermVec language n m w)
    (hz:IsSemiterm language n z) : subst language w (domainCode z)=domainCode (termSubst language w z) :=
  templateOne_targetSubst domainTemplate hw hz

theorem zeroCode_targetSubst {n m w z : V} (hw:IsSemitermVec language n m w)
    (hz:IsSemiterm language n z) : subst language w (zeroCode z)=zeroCode (termSubst language w z) :=
  templateOne_targetSubst zeroTemplate hw hz

theorem equalityCode_targetSubst {n m w x z : V} (hw:IsSemitermVec language n m w)
    (hx:IsSemiterm language n x) (hz:IsSemiterm language n z) :
    subst language w (equalityCode x z)=equalityCode (termSubst language w x) (termSubst language w z) :=
  templateTwo_targetSubst equalityTemplate hw hx hz

theorem successorCode_targetSubst {n m w x z : V} (hw:IsSemitermVec language n m w)
    (hx:IsSemiterm language n x) (hz:IsSemiterm language n z) :
    subst language w (successorCode x z)=successorCode (termSubst language w x) (termSubst language w z) :=
  templateTwo_targetSubst successorTemplate hw hx hz

#print axioms templateOne_targetSubst
#print axioms templateTwo_targetSubst
#print axioms templateThree_targetSubst
#print axioms domainCode_targetSubst
#print axioms zeroCode_targetSubst
#print axioms equalityCode_targetSubst
#print axioms successorCode_targetSubst
end M6.PA.NumericPAeqTerm

