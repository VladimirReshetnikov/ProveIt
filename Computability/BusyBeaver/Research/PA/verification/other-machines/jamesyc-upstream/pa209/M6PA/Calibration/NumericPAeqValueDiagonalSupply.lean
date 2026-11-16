module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqValueDiagonalInvariant
@[expose] public section
namespace M6.PA.NumericPAeqValueCoherence
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource.Numeric ActualCheckerBlueprint
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
attribute [local irreducible] diagonalInvariant
theorem diagonal_guard_supply (count:V):DiagonalSupply (V:=V) count := by
  let : InductionScheme ℒₒᵣ Set.univ ⪯ theory := Entailment.WeakerThan.ofSubset Set.subset_union_right
  have : V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ Set.univ :=
    models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* theory)
  have hall : ∀count:V,DiagonalSupply (V:=V) count := by
    refine InductionScheme.succ_induction (C:=Set.univ) (P:=fun count:V => DiagonalSupply (V:=V) count) ?_ ?_ ?_
    · refine ⟨fun _ => 0,Rewriting.emb diagonalInvariant,by trivial,?_⟩
      intro count; simpa using (diagonal_invariant (V:=V) count).symm
    · exact diagonal_zero_supply
    · exact diagonal_successor_supply
  exact hall count

theorem diagonal_guard_certificate (env count native lo z:V)
    (h:∀i<count,IsSemiterm RelationalSource.language 0 (nth env i))
    (hc:FormulaCovered 0 native lo z (diagonalGuardCode env count)):
    ∃code,verifyValue code=translate (parameters 0 native lo z) (diagonalGuardCode env count)+1 :=
  diagonal_guard_supply count env h native lo z hc
#print axioms diagonal_guard_supply
#print axioms diagonal_guard_certificate
end M6.PA.NumericPAeqValueCoherence
