import DiophantineConsistency.ObjectDivModSyntax

open DiophantineConsistency SetTheory SetTheory.Form
open LeanProofs.BoundedZFCConsistency

example : BProv ZFCax_s [] ObjectDivision.totalForm := ObjectDivision.zfc_proves_total
example : ObjectDivModSyntax.expression.toPolynomial.totalDegree≤4 := ObjectDivModSyntax.expression_degree
example {V : Type} {mem : V → V → Prop} (H : ZFAxioms mem)
    (n d : ObjectOmegaSemiring.Natural H) (hd : 0<d) :
    ∃ q r,ObjectDivision.DivisionRel H q r n d := ObjectDivision.division_exists H n d hd

#print axioms ObjectDivision.division_exists
#print axioms ObjectDivision.division_unique
#print axioms ObjectDivision.divmod_zero
#print axioms ObjectDivision.divmod_spec
#print axioms ObjectDivision.division_iff
#print axioms ObjectDivision.exists_certificate_iff
#print axioms ObjectDivision.divmod_cast
#print axioms ObjectDivision.sentence_totalForm
#print axioms ObjectDivision.zfc_proves_total
#print axioms ObjectDivModSyntax.rows_zero_iff
#print axioms ObjectDivModSyntax.expression_degree
#print axioms ObjectDivModSyntax.expression_zero_iff
#print axioms ObjectDivModSyntax.exists_expression_zero_iff
