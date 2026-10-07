import GowersSzemeredi.Proofs13EndpointFrequencyAddition
import GowersSzemeredi.Proofs13EndpointGoodSet

/-! A global bilinear Fourier set near maximal fourth cube mean.
The set has density at least 1-332 epsilon, and Fourier coefficients
at least (3/4-4 epsilon) N, with no size threshold. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

theorem endpoint_global_fourier {N : Nat} [NeZero N] [Fact N.Prime]
    (f : ZMod N → Complex) (hf : DiscValued f) (epsilon : Real)
    (hnear : 1 - epsilon ≤ endpointCubeMean f 4) :
    ∃ c : ZMod N, ∃ B : Finset (Pair N),
      (1 - 332 * epsilon) * (N : Real) ^ 2 ≤ B.card ∧
      ∀ p ∈ B, (3 / 4 - 4 * epsilon) * (N : Real) ≤
        ‖secondDifferenceFourier f p.1 p.2 (c * p.1 * p.2)‖ := by
  let g := fun x => endpointUnitPhase (f x)
  have hg (x : ZMod N) : ‖g x‖ = 1 := endpointUnitPhase_norm _
  have hQ : 1 - 2 * epsilon ≤ endpointCubeMean g 4 :=
    (endpoint_unitPhase_normalization f hf epsilon hnear).2
  obtain ⟨c, hc⟩ := endpointFrequencyMap_bilinear_correction g hg
  obtain ⟨B, hB, hgood⟩ := endpoint_good_set_card (endpointFrequencyMap g)
    (fun p => c * p.1 * p.2) (endpointFrequencyDefect g)
    (fun p => (endpointFrequencyDefect_bounds g (fun x => (hg x).le) p).1)
  rw [endpointFrequencyDefect_mean] at hB
  have hcard : (Fintype.card (Pair N) : Real) = (N : Real) ^ 2 := by
    simp [Pair, Fintype.card_prod, ZMod.card, pow_two]
  rw [hcard] at hB
  refine ⟨c, B, ?_, ?_⟩
  · have hcoef : 1 - 332 * epsilon ≤ 1 - endpointError (endpointFrequencyMap g)
        (fun p => c * p.1 * p.2) - 4 * (1 - endpointCubeMean g 4) := by
      linarith only [hc, hQ]
    exact (mul_le_mul_of_nonneg_right hcoef (sq_nonneg (N : Real))).trans hB
  · intro p hp
    obtain ⟨heq, ht⟩ := hgood p hp
    have hconc := endpointFrequencyMap_concentration g hg p
    rw [heq] at hconc
    have hlow : (3 / 4 : Real) ≤
        ‖endpointFourierCoefficient (secondDifference g p.1 p.2) (c * p.1 * p.2)‖ := by
      have hn := norm_nonneg (endpointFourierCoefficient (secondDifference g p.1 p.2) (c * p.1 * p.2))
      nlinarith only [hconc, ht, hn]
    have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
    rw [endpointFourierCoefficient_norm, le_div_iff₀ hN] at hlow
    have herr := secondDifferenceFourier_unitPhase_error f hf epsilon hnear p.1 p.2 (c * p.1 * p.2)
    have hnorm := norm_sub_norm_le (secondDifferenceFourier g p.1 p.2 (c * p.1 * p.2))
      (secondDifferenceFourier f p.1 p.2 (c * p.1 * p.2))
    rw [norm_sub_rev] at hnorm
    change ‖secondDifferenceFourier g p.1 p.2 (c * p.1 * p.2)‖ ≥ (3 / 4 : Real) * N at hlow
    change ‖secondDifferenceFourier f p.1 p.2 (c * p.1 * p.2) -
      secondDifferenceFourier g p.1 p.2 (c * p.1 * p.2)‖ ≤ 4 * epsilon * (N : Real) at herr
    nlinarith only [hlow, herr, hnorm]

end LeanProofs.GowersSzemeredi
