module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqValueCoherenceSuccessorSyntax
public import M6PA.Calibration.NumericPAeqValueCoherenceZeroCalibration
@[expose] public section
namespace M6.PA.NumericPAeqValueCoherence
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalPredicateBinary
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
local notation "L" => RelationalSource.language
noncomputable def pairwiseCode (P Q:V) : V :=
  qqAll (qqAll (imp L (qqAnd (substs1 L (qqBvar 1) P) (substs1 L (qqBvar 0) Q))
    (NumericPAeqValueIsoGuard.isoCode (qqBvar 1) (qqBvar 0))))
theorem pairwise_val (P Q:SF (V:=V) 1) : (pairwise P Q isoPredicate).val=pairwiseCode P.val Q.val := by
  simp [pairwise,pairwiseCode,unary,binary,isoPredicate,NumericPAeqValueIsoGuard.isoCode,NumericPAeqTerm.templateTwo,substs1]
  rfl

#print axioms pairwise_val
end M6.PA.NumericPAeqValueCoherence

