import GowersSzemeredi.Proofs05VariablePhaseRefinement
import GowersSzemeredi.Proofs18PartitionFourierBias

/-! From linear nonuniformity of a polynomial twist to an untwisted
progression discrepancy, preserving the global cell-count bound. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- The terminal phase-removal step works for every positive polynomial
degree, retains the whole partition, and applies to complex functions. -/
theorem twisted_partition_nonuniformity_discrepancy {N M k m : Nat} [NeZero N]
    (Q : Fin M → ModAP N) (phi : ZMod N → ZMod N)
    (f : ZMod N → Complex) (beta : Real)
    (hk : 1 ≤ k) (hβ : 0 < beta) (hm : 0 < m)
    (hphi : PolynomialOn k Finset.univ phi) (hf : DiscValued f)
    (hQ : IsPartition (fun i ↦ (Q i).carrier) Finset.univ)
    (hsize : ∀ i, (Q i).carrier.card ≤ m)
    (hfail : ¬ UniformOnPartition (phaseTwist f phi) 1 beta Q m) :
    ∃ L : Nat, ∃ R : Fin L → ModAP N,
      IsPartition (fun j ↦ (R j).carrier) Finset.univ ∧
      IsRefinement (fun j ↦ (R j).carrier) (fun i ↦ (Q i).carrier) ∧
      (∀ j, (R j).IsProper) ∧
      (L : Real) ≤ section5LocalRefinementConstant k beta *
        (M : Real) ^ (polynomialPartitionConstant k : Real)⁻¹ *
        (N : Real) ^ (1 - (polynomialPartitionConstant k : Real)⁻¹) ∧
      (beta / 2) * N ≤ ∑ j, ‖∑ s ∈ (R j).carrier, f s‖ := by
  obtain ⟨r, hr⟩ := partition_linear_nonuniformity_fourier_bias (phaseTwist f phi) Q beta
    (phaseTwist_discValued hf phi) hβ.le hm hQ hsize hfail
  have hbias : beta * N ≤ ∑ i, ‖∑ s ∈ (Q i).carrier,
      f s * exponential (-(phi s + r i * s))‖ := by
    simpa only [phaseTwist_mul_linear] using hr.le
  exact variable_polynomial_phase_refinement Q (fun i s ↦ phi s + r i * s) f beta hk hβ
    (fun i ↦ hphi.add_linear hk (r i)) hf hQ hbias

end LeanProofs.GowersSzemeredi
