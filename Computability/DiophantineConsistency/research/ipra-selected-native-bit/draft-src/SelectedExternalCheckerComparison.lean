import DiophantineConsistency.FoundationZFCConsistencyNat
import DiophantineConsistency.AnnotatedRefutationPR

/-! Metatheoretic standard-natural comparison of two existing source
theorems. This is not an object-theory derivation in iPRA. -/
set_option autoImplicit false
namespace DiophantineConsistency.SelectedExternalCheckerComparison
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open FoundationZFCConsistencyNat

theorem source_nat_iff_no_annotated_certificate :
    sourceSentence.Evalb (M := ℕ) ![] ↔
      ¬∃ certificate : ℕ, AnnotatedRefutationPR.refutationProgram.val.eval certificate = 1 :=
  source_nat_iff_no_refutation.trans AnnotatedRefutationPR.no_refutation_iff.symm

theorem explicit_checker_primrec_and_semantics :
    Nat.Primrec AnnotatedRefutationPR.refutationProgram.val.eval ∧
      (sourceSentence.Evalb (M := ℕ) ![] ↔
        ¬∃ certificate : ℕ, AnnotatedRefutationPR.refutationProgram.val.eval certificate = 1) :=
  ⟨AnnotatedRefutationPR.refutationProgram_primrec, source_nat_iff_no_annotated_certificate⟩

#print axioms source_nat_iff_no_annotated_certificate
#print axioms explicit_checker_primrec_and_semantics
end DiophantineConsistency.SelectedExternalCheckerComparison
