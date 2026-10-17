import GowersSzemeredi.Proofs18IntervalQuadraticDichotomy
import GowersSzemeredi.Proofs18IntervalUniformStoppingSide
import GowersSzemeredi.Proofs18NaturalIntervalIncrementSide

/-! Declarations of `Proofs18IntervalQuadraticDichotomy` that the final route does not use and that
need modules outside it (moved here so that those modules can leave the route). -/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

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
