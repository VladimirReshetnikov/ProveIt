module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqFormulaDoubleUniversal
public import M6PA.Calibration.NumericPAeqInductionStepTemplateSyntax
@[expose] public section
namespace M6.PA.NumericPAeqInductionStepOpening
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalPredicateBinary NumericPAeqFormulaLogical
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local notation "L" => RelationalSource.language
noncomputable def outerTyped (C:SF (V:=V) 2):SF (V:=V) 1 :=
  C.shift.subst (Bootstrapping.SemitermVec.q (![Semiterm.fvar 0] : Bootstrapping.SemitermVec V L 1 0))
theorem outerTyped_val (C:SF (V:=V) 2):(outerTyped C).val=openOuter C.val := by
  simp [outerTyped,openOuter,SemitermVec.q,qVec,Bootstrapping.Semiformula.val_substs,
    Bootstrapping.Semiformula.val_shift]
theorem double_open_typed (C:SF (V:=V) 2):
    free L (openOuter C.val)=(C.shift.shift.subst (![Semiterm.fvar 0,Semiterm.fvar 1] : Bootstrapping.SemitermVec V L 2 0)).val := by
  rw [←outerTyped_val,←Bootstrapping.Semiformula.free_val]
  congr 1
  simp [outerTyped,Bootstrapping.Semiformula.free,Bootstrapping.Semiformula.shift_substs,
    Bootstrapping.Semiformula.substs_substs,SemitermVec.q]
#print axioms outerTyped_val
#print axioms double_open_typed
end M6.PA.NumericPAeqInductionStepOpening

