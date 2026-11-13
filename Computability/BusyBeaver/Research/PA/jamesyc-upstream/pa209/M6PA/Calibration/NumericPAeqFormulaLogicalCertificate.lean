module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqFormulaLogicalBi
@[expose] public section
namespace M6.PA.NumericPAeqFormulaLogical
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalPredicateBinary RelationalSource.Numeric ActualCheckerBlueprint
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
local notation "L" => RelationalSource.language
noncomputable def biCode (p q:V):V := qqAnd (imp L p q) (imp L q p)
theorem bi_val (p q:SF (V:=V) 0):(bi p q).val=biCode p.val q.val := by rfl
theorem andBi_requested_certificate (p q r s native lo z:V)
    (hp:IsFormula L p) (hq:IsFormula L q) (hr:IsFormula L r) (hs:IsFormula L s)
    (hc:FormulaCovered 0 native lo z
      (imp L (qqAnd (biCode p q) (biCode r s)) (biCode (qqAnd p r) (qqAnd q s)))):
    ∃code,verifyValue code=translate (parameters 0 native lo z)
      (imp L (qqAnd (biCode p q) (biCode r s)) (biCode (qqAnd p r) (qqAnd q s)))+1 := by
  let P:SF (V:=V) 0 := ⟨p,hp⟩
  let Q:SF (V:=V) 0 := ⟨q,hq⟩
  let R:SF (V:=V) 0 := ⟨r,hr⟩
  let S:SF (V:=V) 0 := ⟨s,hs⟩
  exact empty_requested_certificate _ (andBi P Q R S) native lo z hc
theorem orBi_requested_certificate (p q r s native lo z:V)
    (hp:IsFormula L p) (hq:IsFormula L q) (hr:IsFormula L r) (hs:IsFormula L s)
    (hc:FormulaCovered 0 native lo z
      (imp L (qqAnd (biCode p q) (biCode r s)) (biCode (qqOr p r) (qqOr q s)))):
    ∃code,verifyValue code=translate (parameters 0 native lo z)
      (imp L (qqAnd (biCode p q) (biCode r s)) (biCode (qqOr p r) (qqOr q s)))+1 := by
  let P:SF (V:=V) 0 := ⟨p,hp⟩
  let Q:SF (V:=V) 0 := ⟨q,hq⟩
  let R:SF (V:=V) 0 := ⟨r,hr⟩
  let S:SF (V:=V) 0 := ⟨s,hs⟩
  exact empty_requested_certificate _ (orBi P Q R S) native lo z hc
#print axioms andBi_requested_certificate
#print axioms orBi_requested_certificate
end M6.PA.NumericPAeqFormulaLogical

