import GowersSzemeredi.Audit
import OAI.Combinatorics.Progressions.Lattices.NativeProperAffineRecovery

/-! Check that the Gowers import closure coexists with the full upstream
affine-recovery module. The extracted lemmas retain the original propositions;
their distinct namespace prevents duplicate declarations when the density port
and Gowers facade are imported together. The quantitative-density conclusion
is checked by `OAI.QuantitativePortAudit` and used by Theorem 1.3. -/
set_option autoImplicit false

open OAI.Erdos3.FreimanModel

example : @ProveItExtract.exists_dense_cyclic_model_of_integer_vectors =
    @exists_dense_cyclic_model_of_integer_vectors := Subsingleton.elim _ _

example : @ProveItExtract.exists_bounded_affine_box_of_cyclic_model =
    @exists_bounded_affine_box_of_cyclic_model := Subsingleton.elim _ _

#print axioms LeanProofs.GowersSzemeredi.theorem_7_1_holds
#print axioms LeanProofs.GowersSzemeredi.theorem_7_2_holds
