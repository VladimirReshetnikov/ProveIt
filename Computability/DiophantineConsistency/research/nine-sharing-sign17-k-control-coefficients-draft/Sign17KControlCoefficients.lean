import DiophantineConsistency.Sign17KRankedRawWord

/-! SOURCE-ONLY: combine 34 control terms into a finite coefficient vector. -/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign17KControlCoefficients
open CurrentKernel2011
open scoped BigOperators

def coefficients : Fin 44 → ℕ := ![68719476736, 137438953472, 274877906944, 549755813888, 1099511627776, 2199023255552, 4398046511104, 8796093022208, 17592186044416, 0, 0, 0, 0, 0, 0, 0, 0, 0, 524288, 1048576, 2097152, 4194304, 8388608, 16777216, 33554432, 67108864, 134217728, 268435456, 536870912, 1073741824, 2147483648, 4294967296, 8589934592, 17179869184, 34359738368, 0, 2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144]

theorem controls_as_sum (r : ℕ) :
    Sign17KRankedRawWord.controls r =
      ∑ i : Fin 44, coefficients i * r ^ (1005 - (942 + i.val)) := by
  simp [Sign17KRankedRawWord.controls, coefficients, Fin.sum_univ_succ] <;> ring

theorem rawWord_control_coefficients (r : ℕ) :
    rawWord r = r ^ 18 + r ^ 1004 + r ^ 2020 +
      (∑ i : Fin 942, 2 * Sign17KWeightUnion942.weights i * r ^ (1005 - i.val)) +
      (∑ i : Fin 44, coefficients i * r ^ (1005 - (942 + i.val))) := by
  rw [Sign17KRankedRawWord.rawWord_ranked, controls_as_sum]

end DiophantineConsistency.Sign17KControlCoefficients
#print axioms DiophantineConsistency.Sign17KControlCoefficients.controls_as_sum
#print axioms DiophantineConsistency.Sign17KControlCoefficients.rawWord_control_coefficients
