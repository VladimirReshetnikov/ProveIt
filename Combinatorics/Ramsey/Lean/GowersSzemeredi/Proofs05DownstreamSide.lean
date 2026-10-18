import GowersSzemeredi.Proofs05Downstream

/-! Declarations of `Proofs05Downstream` that the final route does not use (moved here so
that the route keeps only what it uses). -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Pointwise ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

/-!
The strengthened local form used in the proof of Lemma 5.14.  Unlike
Corollary 5.7, it retains the additive error estimate before a lower bound on
the original correlation is substituted.
-/

theorem section5_local_phase_refinement_of_corollary_5_6
    (h56 : corollary_5_6) {N k v : Nat} [NeZero N]
    (P : ModAP N) (phi : ZMod N → ZMod N) (eta : Real)
    (hP : P.IsProper) (hk : 1 ≤ k)
    (hphi : PolynomialOn k Finset.univ phi) (heta : 0 < eta)
    (hlarge : max (polynomialPartitionThreshold k : Real)
        ((4 * Real.pi / eta) ^ polynomialPartitionConstant k) < P.length)
    (hv : 1 ≤ v)
    (hvupper : (v : Real) ≤
      (P.length : Real) ^ (polynomialPartitionConstant k : Real)⁻¹) :
    ∃ L : Nat, ∃ R : Fin L → ModAP N,
      IsPartition (fun j => (R j).carrier) P.carrier ∧
      (∀ j, (R j).IsProper ∧ 0 < (R j).length ∧
        ((R j).length = v - 1 ∨ (R j).length = v)) ∧
      ∀ f : ZMod N → Complex, DiscValued f →
        ‖∑ s ∈ P.carrier, f s * exponential (-(phi s))‖ ≤
          (∑ j, ‖∑ s ∈ (R j).carrier, f s‖) +
            eta / 2 * P.carrier.card := by
  obtain ⟨L, R, hrefine, hRproper, hdiam⟩ :=
    section5_local_diameter_refinement_of_corollary_5_6 h56 P phi eta hP hk hphi heta hlarge hv
      hvupper
  exact ⟨L, R, hrefine, hRproper,
    section5_phase_error_of_diameter P.carrier _ phi eta hrefine hdiam⟩

end LeanProofs.GowersSzemeredi
