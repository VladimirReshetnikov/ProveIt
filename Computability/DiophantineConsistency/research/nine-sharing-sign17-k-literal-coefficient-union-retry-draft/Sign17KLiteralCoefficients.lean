import DiophantineConsistency.Sign17KTileCoeffUnion942
import DiophantineConsistency.Sign17KFullCoefficients

/-! SOURCE-ONLY: replace in-Lean coefficient vector by in-Lean literal blocks. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17KLiteralCoefficients
open CurrentKernel2011
open scoped BigOperators

def literal : Fin 986 → ℕ := Fin.append
  Sign17KTileCoeffUnion942.literal Sign17KControlBlocks.literal

theorem coefficients_eq_literal (i : Fin 986) :
    Sign17KFullCoefficients.coefficients i = literal i := by
  exact Sign17KWeightAppend.append_certificates (fun x => x)
    (fun i : Fin 942 => 2 * Sign17KWeightUnion942.weights i)
    Sign17KControlBlocks.literal
    Sign17KTileCoeffUnion942.literal Sign17KControlBlocks.literal
    Sign17KTileCoeffUnion942.doubled_weights (fun _ => rfl) i

theorem rawWord_literal (r : ℕ) :
    rawWord r = r ^ 18 + r ^ 1004 + r ^ 2020 +
      ∑ i : Fin 986, literal i * r ^ (1005 - i.val) := by
  have hsum :
      (∑ i : Fin 986, Sign17KFullCoefficients.coefficients i * r ^ (1005 - i.val)) =
        ∑ i : Fin 986, literal i * r ^ (1005 - i.val) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [coefficients_eq_literal]
  calc
    rawWord r = r ^ 18 + r ^ 1004 + r ^ 2020 +
        ∑ i : Fin 986, Sign17KFullCoefficients.coefficients i * r ^ (1005 - i.val) :=
      Sign17KFullCoefficients.rawWord_coefficients r
    _ = r ^ 18 + r ^ 1004 + r ^ 2020 +
        ∑ i : Fin 986, literal i * r ^ (1005 - i.val) :=
      congrArg (fun z : ℕ => r ^ 18 + r ^ 1004 + r ^ 2020 + z) hsum

theorem K_literal : K = radix ^ 18 + radix ^ 1004 + radix ^ 2020 +
    ∑ i : Fin 986, literal i * radix ^ (1005 - i.val) := by
  exact rawWord_literal radix

end DiophantineConsistency.Sign17KLiteralCoefficients
#print axioms DiophantineConsistency.Sign17KLiteralCoefficients.coefficients_eq_literal
#print axioms DiophantineConsistency.Sign17KLiteralCoefficients.rawWord_literal
#print axioms DiophantineConsistency.Sign17KLiteralCoefficients.K_literal
