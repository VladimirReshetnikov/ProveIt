module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqInductionStepOpeningTyped
public import M6PA.Calibration.NumericPAeqInductionStepTemplateCode
public import M6PA.Calibration.NumericPAeqTermTargetShiftTemplates
@[expose] public section
namespace M6.PA.NumericPAeqInductionStepOpening
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalPredicateBinary NumericPAeqValueCoherence NumericPAeqFormulaLogical NumericPAeqInductionStepTemplate
open NumericPAeqTerm (domainCode successorCode)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
local notation "L" => RelationalSource.language
@[simp] theorem fixedDomain_shift : (RelationalPredicateBinary.domain (V:=V)).shift=RelationalPredicateBinary.domain := by
  apply Bootstrapping.Semiformula.ext
  change shift L (⌜NumericPAeqTerm.domainTemplate⌝:V)=⌜NumericPAeqTerm.domainTemplate⌝
  rw [←FFL.FirstOrder.Semiformula.quote_shift,NumericPAeqTerm.domainTemplate_targetShift]
@[simp] theorem fixedSuccessor_shift : (successorPredicate (V:=V)).shift=successorPredicate := by
  apply Bootstrapping.Semiformula.ext
  change shift L (⌜NumericPAeqTerm.successorTemplate⌝:V)=⌜NumericPAeqTerm.successorTemplate⌝
  rw [←FFL.FirstOrder.Semiformula.quote_shift,NumericPAeqTerm.successorTemplate_targetShift]
noncomputable def openedCode (F P R:V):V := imp L (shift L (shift L F))
  (imp L (qqAnd (domainCode (qqFvar 1)) (qqAnd (domainCode (qqFvar 0)) (successorCode (qqFvar 1) (qqFvar 0))))
    (biCode (substs1 L (qqFvar 1) (shift L (shift L R))) (substs1 L (qqFvar 0) (shift L (shift L P)))))

theorem uniformMatrix_double_open (F:SF (V:=V) 0) (P R:SF (V:=V) 1):
    free L (openOuter (uniformMatrixCode F.val P.val R.val))=openedCode F.val P.val R.val := by
  rw [←uniformMatrix_val,double_open_typed]
  have ht : (uniformMatrix F P R).shift.shift.subst
      (![Semiterm.fvar 0,Semiterm.fvar 1] : Bootstrapping.SemitermVec V L 2 0)=
    (F.shift.shift 🡒 ((unary domain (Semiterm.fvar 1) ⋏
      (unary domain (Semiterm.fvar 0) ⋏ binary successorPredicate (Semiterm.fvar 1) (Semiterm.fvar 0))) 🡒
        ((unary R.shift.shift (Semiterm.fvar 1) 🡒 unary P.shift.shift (Semiterm.fvar 0)) ⋏
          (unary P.shift.shift (Semiterm.fvar 0) 🡒 unary R.shift.shift (Semiterm.fvar 1))))) := by
    simp [uniformMatrix]
  rw [ht]
  simp only [Bootstrapping.Semiformula.val_imp,Bootstrapping.Semiformula.val_and,
    Bootstrapping.Semiformula.val_shift,domainAt_val,successorAt_val,unary_val]
  rfl

theorem uniformMatrixCode_double_open {F P R:V} (hF:IsFormula L F)
    (hP:IsSemiformula L 1 P) (hR:IsSemiformula L 1 R):
    free L (openOuter (uniformMatrixCode F P R))=openedCode F P R :=
  uniformMatrix_double_open ⟨F,hF⟩ ⟨P,by simpa using hP⟩ ⟨R,by simpa using hR⟩
#print axioms fixedDomain_shift
#print axioms fixedSuccessor_shift
#print axioms uniformMatrix_double_open
#print axioms uniformMatrixCode_double_open
end M6.PA.NumericPAeqInductionStepOpening

