import DiophantineConsistency.FoundationHAOrderBase

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.FoundationHAOrderBaseChecks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder
open FoundationPAHFSyntax FoundationHAOrderBase SetTheory.PA HA

theorem literal_zeroLtOne : sentence PeanoMinus.Axiom.zeroLtOneᴺ =
    doubleNeg (ltFormula .zero (.succ .zero)) := rfl

theorem literal_zeroLe : sentence PeanoMinus.Axiom.zeroLeᴺ =
    Formula.closeN 1 (neg (.and (neg (doubleNeg (.eq .zero (.var 0))))
      (neg (doubleNeg (ltFormula .zero (.var 0))))))) := rfl

theorem sparse_parameters : Proves (.or
    (.eq .zero (.mul (.var 0) (.add (.var 7) (.var 0))))
    (ltFormula .zero (.mul (.var 0) (.add (.var 7) (.var 0))))) := zero_le _

theorem context_retained (a b : Formula) :
    Relative Formula.Ax_s [.or a b]
      (neg (.and (neg (doubleNeg a)) (neg (doubleNeg b)))) :=
  encoded_or (Relative.hypothesis List.mem_cons_self)

#print axioms encoded_or
#print axioms zero_lt_one
#print axioms rename_ltFormula
#print axioms zero_le
#print axioms zeroLtOne
#print axioms zeroLe
#print axioms literal_zeroLtOne
#print axioms literal_zeroLe
#print axioms sparse_parameters
#print axioms context_retained
end DiophantineConsistency.FoundationHAOrderBaseChecks
