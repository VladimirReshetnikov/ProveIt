import GowersSzemeredi.Proofs18NaturalIntervalIncrement
import GowersSzemeredi.Proofs18IntervalQuadraticIncrement

/-! Declarations of `Proofs18NaturalIntervalIncrement` that the final route does not use and that
need modules outside it (moved here so that those modules can leave the route). -/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

/-- A quadratic increment on an ordinary progression in the original finite
interval. All sizes and density parameters are preserved by the transport. -/
theorem natural_interval_quadratic_density_increment
    (alpha : Real) (hα : 0 < alpha) (hαone : alpha ≤ 1)
    (N L : Nat) [NeZero N] [Fact N.Prime] (hL : 2 * L < N)
    (hN : quadraticExponentialThreshold alpha ≤ N)
    (hscale : 32 ≤ quadraticDiscrepancyParameter alpha * N)
    (B : Finset (Fin L)) (delta : Real)
    (hδ : 0 ≤ delta) (hδone : delta ≤ 1) (hcard : (B.card : Real) = delta * L)
    (hnot : ¬ UniformOfDegree (intervalExtension N (finiteIntervalBalance B delta)) alpha 2) :
    ∃ Q : NatAP, Q.IsProper ∧ Q.carrier ⊆ Finset.range L ∧
      (quadraticDiscrepancyParameter alpha /
          (8 * boundaryRefinementConstant (quadraticDiscrepancyParameter alpha / 64))) *
        (N : Real) ^ (quadraticDiscrepancyExponent alpha / 16) ≤ (Q.length : Real) ∧
      (delta + quadraticDiscrepancyParameter alpha / 8) * Q.length ≤
        (B.image Fin.val ∩ Q.carrier).card := by
  have hLN : L ≤ N := by omega
  obtain ⟨P, hP, hsub, hsize, hinc⟩ := interval_quadratic_density_increment
    alpha hα hαone N L hLN hN hscale (finiteIntervalImage N B) delta
    (finiteIntervalImage_subset B) hδ hδone
    (by simpa only [finiteIntervalImage_card hLN] using hcard)
    (by rwa [relativeBalanced_finiteIntervalImage hLN])
  obtain ⟨Q, hQ, hlen, hcarrier, hsubQ⟩ := P.exists_natAP_of_short_interval hP hL hsub
  have hPcard : P.carrier.card = P.length := hP
  refine ⟨Q, hQ, hsubQ, ?_, ?_⟩
  · simpa only [hlen, hPcard] using hsize
  · have hcount := card_inter_natAP_of_carrier_eq P Q hcarrier (finiteIntervalImage N B)
    rw [finiteIntervalImage_val hLN] at hcount
    simpa only [hlen, hPcard, hcount] using hinc

end LeanProofs.GowersSzemeredi
