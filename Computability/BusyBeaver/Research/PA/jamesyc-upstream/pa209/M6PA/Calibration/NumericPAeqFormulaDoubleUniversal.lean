module
public import M6PA.Theory
public import M6PA.Calibration.FoundationRelationalSequentRequestedUniversal
@[expose] public section
namespace M6.PA.NumericPAeqFormulaLogical
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource.Numeric ActualCheckerBlueprint
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
local notation "L" => RelationalSource.language
noncomputable def openOuter (P:V):V := subst L (qVec L (qqFvar 0∷0)) (shift L P)
theorem openOuter_valid {P:V} (hp:IsSemiformula L 2 P):IsSemiformula L 1 (openOuter P) := by
  have hw : IsSemitermVec L (1:V) 0 (qqFvar 0∷0) := by simp
  exact hp.shift.subst (by simpa [one_add_one_eq_two] using hw.qVec)
theorem free_all_code {P:V} (hp:IsSemiformula L 2 P):free L (qqAll P)=qqAll (openOuter P) := by
  simp only [free,substs1,shift_all hp.isUFormula,substs_all hp.shift.isUFormula,openOuter]
theorem double_universal_certificate (P native lo z:V) (hp:IsSemiformula L 2 P)
    (hc:FormulaCovered 0 native lo z (qqAll (qqAll P)))
    (child:∀g l r:V,FormulaCovered 0 g l r (free L (openOuter P))→
      ∃code,verifyValue code=translate (parameters 0 g l r) (free L (openOuter P))+1):
    ∃code,verifyValue code=translate (parameters 0 native lo z) (qqAll (qqAll P))+1 := by
  apply requested_universal_certificate _ native lo z (IsSemiformula.all.mpr (by simpa [one_add_one_eq_two] using hp)) hc
  intro g l r h
  rw [free_all_code hp] at h ⊢
  exact requested_universal_certificate _ g l r (openOuter_valid hp) h child
#print axioms openOuter_valid
#print axioms free_all_code
#print axioms double_universal_certificate
end M6.PA.NumericPAeqFormulaLogical

