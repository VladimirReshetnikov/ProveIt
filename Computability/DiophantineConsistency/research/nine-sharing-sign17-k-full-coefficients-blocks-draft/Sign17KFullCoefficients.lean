import DiophantineConsistency.Sign17KControlBlockSum

/-! SOURCE-ONLY: join ranked tile and control coefficients, leaving sentinels separate. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17KFullCoefficients
open CurrentKernel2011
open scoped BigOperators

def coefficients : Fin 986 → ℕ := Fin.append
  (fun i : Fin 942 => 2 * Sign17KWeightUnion942.weights i)
  Sign17KControlBlocks.literal

theorem coefficient_sum (r : ℕ) :
    (∑ i : Fin 986, coefficients i * r ^ (1005 - i.val)) =
      (∑ i : Fin 942, 2 * Sign17KWeightUnion942.weights i * r ^ (1005 - i.val)) +
      (∑ i : Fin 44, Sign17KControlBlocks.literal i *
        r ^ (1005 - (942 + i.val))) := by
  rw [Fin.sum_univ_add (a := 942) (b := 44)]
  simp only [coefficients, Fin.append_left, Fin.append_right,
    Fin.val_castAdd, Fin.val_natAdd]

theorem rawWord_coefficients (r : ℕ) :
    rawWord r = r ^ 18 + r ^ 1004 + r ^ 2020 +
      ∑ i : Fin 986, coefficients i * r ^ (1005 - i.val) := by
  rw [Sign17KRankedRawWord.rawWord_ranked, Sign17KControlBlockSum.controls_as_sum, coefficient_sum]
  omega

theorem K_coefficients : K = radix ^ 18 + radix ^ 1004 + radix ^ 2020 +
    ∑ i : Fin 986, coefficients i * radix ^ (1005 - i.val) := by
  exact rawWord_coefficients radix

end DiophantineConsistency.Sign17KFullCoefficients
#print axioms DiophantineConsistency.Sign17KFullCoefficients.coefficient_sum
#print axioms DiophantineConsistency.Sign17KFullCoefficients.rawWord_coefficients
#print axioms DiophantineConsistency.Sign17KFullCoefficients.K_coefficients
