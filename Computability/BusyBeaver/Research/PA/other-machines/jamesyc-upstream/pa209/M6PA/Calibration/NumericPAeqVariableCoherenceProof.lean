module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqVariableCoherenceTyped
@[expose] public section
namespace M6.PA.NumericPAeqValueCoherence
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalPredicateBinary
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local notation "L" => RelationalSource.language
variable {T : InternalTheory V L}
noncomputable def variableComparisonProof (D : SF (V:=V) 1) (E R : SF (V:=V) 2)
    (x y : ST (V:=V) 0) :
    ND.Proof (T:=T) (insert (∼transportTyped E R) ∅)
      (binary R x y 🡒 variableComparisonTyped D E R x y) := by
  apply ND.impIntro
  apply ND.allIntro
  simp only [Bootstrapping.Semiformula.free,Bootstrapping.Semiformula.shift_all,Bootstrapping.Semiformula.substs_all]
  apply ND.allIntro
  simp only [variableComparisonTyped,Bootstrapping.Semiformula.free,Bootstrapping.Semiformula.shift_all,
    Bootstrapping.Semiformula.shift_imp,Bootstrapping.Semiformula.shift_and,
    Bootstrapping.Semiformula.substs_all,Bootstrapping.Semiformula.substs_imp,
    Bootstrapping.Semiformula.substs_and,unary_shift,binary_shift,unary_subst,binary_subst]
  simp only [←Bootstrapping.Semiterm.bShift_shift_comm,Bootstrapping.Semiterm.bShift_substs_q,
    Bootstrapping.Semiterm.bShift_substs_sing]
  apply ND.impIntro
  let r : ST (V:=V) 0 := Semiterm.fvar 1
  let s : ST (V:=V) 0 := Semiterm.fvar 0
  let A := (unary D.shift.shift r ⋏ binary E.shift.shift r x.shift.shift) ⋏
    (unary D.shift.shift s ⋏ binary E.shift.shift s y.shift.shift)
  let C : ND.Seq (V:=V) := insert (∼A)
    ((insert (∼binary R x y) (insert (∼transportTyped E R) ∅) : ND.Seq (V:=V)).shift.shift)
  have hp : ND.Proof (T:=T) C A := ND.assumption _ (by simp [C])
  have ht : ND.Proof (T:=T) C (transportTyped E.shift.shift R.shift.shift) := by
    apply ND.assumption
    simp [C]
  have hi : ND.Proof (T:=T) C (binary R.shift.shift x.shift.shift y.shift.shift) := by
    apply ND.assumption
    simp [C]
  have out := transportAt E.shift.shift R.shift.shift x.shift.shift y.shift.shift r s ht hi
    (ND.andRight (ND.andLeft hp)) (ND.andRight (ND.andRight hp))
  simpa [C,A,r,s,SemitermVec.q,←Bootstrapping.Semiterm.bShift_shift_comm] using out
#print axioms variableComparisonProof
end M6.PA.NumericPAeqValueCoherence
