import GowersSzemeredi.Proofs18IntervalUniformStopping
import GowersSzemeredi.Proofs18NaturalIntervalIncrement

/-! A quantitative four-term progression/density-increment alternative on
ordinary intervals. The density parameter stays relative to the interval. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- A uniformity parameter sufficient for the relative interval count. -/
def intervalQuadraticUniformityParameter (delta : Real) : Real :=
  (delta ^ 4 / 32768) ^ 8

theorem intervalQuadraticUniformityParameter_pos {delta : Real} (hδ : 0 < delta) :
    0 < intervalQuadraticUniformityParameter delta := by
  unfold intervalQuadraticUniformityParameter
  positivity

theorem intervalQuadraticUniformityParameter_le_one {delta : Real}
    (hδ : 0 ≤ delta) (hδone : delta ≤ 1) : intervalQuadraticUniformityParameter delta ≤ 1 := by
  have hp : delta ^ 4 ≤ 1 := pow_le_one₀ hδ hδone
  apply pow_le_one₀ (by positivity)
  linarith

theorem intervalQuadraticUniformityParameter_count_error (delta : Real) :
    4 * intervalQuadraticUniformityParameter delta ^ (1 / 8 : Real) ≤ delta ^ 4 / 8192 := by
  have hroot : ((delta ^ 4 / 32768) ^ (8 : Nat)) ^ (1 / 8 : Real) = delta ^ 4 / 32768 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (show 0 ≤ delta ^ 4 / 32768 by positivity)]
    norm_num
  unfold intervalQuadraticUniformityParameter
  rw [hroot]
  linarith

/-- An explicit one-step alternative that can be iterated on integer sets:
either the original set contains a four-term progression, or a subprogression
inside the original interval has higher original relative density. -/
theorem interval_quadratic_dichotomy
    (N L : Nat) [NeZero N] [Fact N.Prime]
    (hL : 2 * L < N) (hLfour : 4 ≤ L) (hNL : N ≤ 8 * L)
    (B : Finset (Fin L)) (delta : Real) (hδ : 0 < delta) (hδone : delta ≤ 1)
    (hcard : (B.card : Real) = delta * L)
    (hN : quadraticExponentialThreshold (intervalQuadraticUniformityParameter delta) ≤ N)
    (hscale : 32 ≤ quadraticDiscrepancyParameter (intervalQuadraticUniformityParameter delta) * N)
    (hlarge : 8192 < delta ^ 4 * N) :
    HasNatAP (B.image Fin.val) 4 ∨
      ∃ Q : NatAP, Q.IsProper ∧ Q.carrier ⊆ Finset.range L ∧
        (quadraticDiscrepancyParameter (intervalQuadraticUniformityParameter delta) /
            (8 * boundaryRefinementConstant
              (quadraticDiscrepancyParameter (intervalQuadraticUniformityParameter delta) / 64))) *
          (N : Real) ^ (quadraticDiscrepancyExponent (intervalQuadraticUniformityParameter delta) / 16) ≤
            (Q.length : Real) ∧
        (delta + quadraticDiscrepancyParameter (intervalQuadraticUniformityParameter delta) / 8) *
            Q.length ≤ (B.image Fin.val ∩ Q.carrier).card := by
  let alpha := intervalQuadraticUniformityParameter delta
  have hα : 0 < alpha := intervalQuadraticUniformityParameter_pos hδ
  have hαone : alpha ≤ 1 := intervalQuadraticUniformityParameter_le_one hδ.le hδone
  by_cases hu : UniformOfDegree (intervalExtension N (finiteIntervalBalance B delta)) alpha 2
  · exact Or.inl (interval_relative_uniform_hasNatAP_four hL hLfour hNL B delta alpha
      hδ.le hδone hα.le (intervalQuadraticUniformityParameter_count_error delta) hlarge hu)
  · exact Or.inr (natural_interval_quadratic_density_increment alpha hα hαone N L hL hN hscale
      B delta hδ.le hδone hcard hu)

end LeanProofs.GowersSzemeredi
