import DiophantineConsistency.ObjectNaturalSemiring

open SetTheory SetTheory.Form
open LeanProofs.BoundedZFCConsistency DiophantineConsistency
open ObjectOmegaSemiring

noncomputable abbrev checkedSemiring {V : Type*} {mem : V → V → Prop} (H : ZFAxioms mem) :
    CommSemiring (Natural H) := inferInstance

-- Exercise the algebra interface at arbitrary internal, potentially
-- nonstandard inputs, rather than only at external numeral assignments.
example {V : Type*} {mem : V → V → Prop} (H : ZFAxioms mem) (a b : Natural H) :
    (a+b)^2=a^2+2*a*b+b^2 := by ring

-- The formula-to-semiring bridge also reaches the actual BProv calculus.
-- This is a finite algebra regression, with no consistency claim.
example : BProv ZFCax_s [] (ObjectPolynomial.noZeroForm (Expr.constant 1 : Expr (Fin 0))) := by
  apply completeness_inf_context ZFCax_s [] _ Sentences_ZFC
  intro Dom m v hmodel _
  let H := ObjectMultiplication.axioms_of_zfc_model v hmodel
  apply (ObjectNaturalSemiring.sat_noZeroForm_iff H _).mpr ?_ v
  intro x
  change (1 : Natural H) ≠ 0
  exact one_ne_zero

#print axioms ObjectOmegaSemiring.mulRel_one_left
#print axioms Natural.plus_spec
#print axioms Natural.times_spec
#print axioms checkedSemiring
#print axioms Natural.add_graph
#print axioms Natural.mul_graph
#print axioms Natural.addRel_iff
#print axioms Natural.mulRel_iff
#print axioms Natural.natCast_val
#print axioms Natural.instNontrivial
#print axioms NatExpr.evalSemiring
#print axioms NatExpr.evalSemiring_nat
#print axioms NatExpr.eval₂_toPolynomial
#print axioms ObjectNaturalSemiring.evalRel_iff
#print axioms ObjectNaturalSemiring.equationRel_iff
#print axioms ObjectNaturalSemiring.noZeroRel_iff
#print axioms ObjectNaturalSemiring.sat_noZeroForm_iff
