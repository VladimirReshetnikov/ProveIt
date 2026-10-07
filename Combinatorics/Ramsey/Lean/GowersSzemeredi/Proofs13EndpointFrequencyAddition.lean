import GowersSzemeredi.Proofs13EndpointCocycleTest
import GowersSzemeredi.Proofs13EndpointBilinearCorrection

/-! The dominant-frequency table fails its addition test at most nine
 times the fourth cube defect. Symmetric correction then gives one global
 bilinear frequency map with error at most 162 times that defect. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

theorem endpointFrequencyMap_test {N : Nat} [NeZero N] (g : ZMod N → Complex)
    (hg : ∀ x, ‖g x‖ = 1) (h h' k : ZMod N) :
    (if endpointFrequencyMap g (h + h', k) = endpointFrequencyMap g (h, k) +
      endpointFrequencyMap g (h', k) then (0 : Real) else 1) ≤
      3 * (endpointFrequencyDefect g (h + h', k) +
        endpointFrequencyDefect g (h, k) + endpointFrequencyDefect g (h', k)) := by
  let F (h : ZMod N) := secondDifference g h k
  have hunit (h x : ZMod N) : ‖F h x‖ = 1 := by
    simp only [F, secondDifference, difference, norm_mul, norm_star, hg, mul_one]
  let r (h : ZMod N) := endpointDominantFrequency (F h)
  let z (h : ZMod N) := endpointUnitPhase (endpointFourierCoefficient (F h) (r h))
  have ht := endpoint_character_cocycle_test (F (h + h')) (F h) (F h') (hunit h')
    (z (h + h')) (z h) (z h') (endpointUnitPhase_norm _) (endpointUnitPhase_norm _)
    (endpointUnitPhase_norm _) (r (h + h')) (r h) (r h') h'
    (endpoint_secondDifference_cocycle g hg h h' k)
  have h₀ := endpointApproximatingCharacter_error_le (F (h + h')) (hunit (h + h'))
  have h₁ := endpointApproximatingCharacter_error_le (F h) (hunit h)
  have h₂ := endpointApproximatingCharacter_error_le (F h') (hunit h')
  change endpointL2Error (F (h + h')) (endpointCharacter (z (h + h')) (r (h + h'))) ≤
    2 * endpointFrequencyDefect g (h + h', k) at h₀
  change endpointL2Error (F h) (endpointCharacter (z h) (r h)) ≤
    2 * endpointFrequencyDefect g (h, k) at h₁
  change endpointL2Error (F h') (endpointCharacter (z h') (r h')) ≤
    2 * endpointFrequencyDefect g (h', k) at h₂
  change (if r (h + h') = r h + r h' then (0 : Real) else 1) ≤ _
  linarith only [ht, h₀, h₁, h₂]

theorem endpointFrequencyMap_row_failure {N : Nat} [NeZero N] (g : ZMod N → Complex)
    (hg : ∀ x, ‖g x‖ = 1) (k : ZMod N) :
    endpointAdditiveFailure (fun h => endpointFrequencyMap g (h, k)) ≤
      9 * (𝔼 h : ZMod N, endpointFrequencyDefect g (h, k)) := by
  unfold endpointAdditiveFailure endpointError
  rw [endpoint_expect_prod]
  have ht := Finset.expect_le_expect (fun h (_ : h ∈ (Finset.univ : Finset (ZMod N))) =>
    Finset.expect_le_expect (fun h' (_ : h' ∈ (Finset.univ : Finset (ZMod N))) =>
      endpointFrequencyMap_test g hg h h' k))
  have hadd (h : ZMod N) : (𝔼 h' : ZMod N, endpointFrequencyDefect g (h + h', k)) =
      𝔼 h' : ZMod N, endpointFrequencyDefect g (h', k) :=
    Fintype.expect_equiv (Equiv.addLeft h) _ _ (fun _ => rfl)
  simp_rw [← Finset.mul_expect, Finset.expect_add_distrib, hadd, Fintype.expect_const] at ht
  convert ht using 1 <;> first | rfl | ring

theorem endpointFrequencyMap_addition_failure {N : Nat} [NeZero N] (g : ZMod N → Complex)
    (hg : ∀ x, ‖g x‖ = 1) :
    (𝔼 k : ZMod N, endpointAdditiveFailure (fun h => endpointFrequencyMap g (h, k))) ≤
      9 * (1 - endpointCubeMean g 4) := by
  calc
    _ ≤ 𝔼 k : ZMod N, 9 * (𝔼 h : ZMod N, endpointFrequencyDefect g (h, k)) :=
      Finset.expect_le_expect (fun k _ => endpointFrequencyMap_row_failure g hg k)
    _ = 9 * (𝔼 p : Pair N, endpointFrequencyDefect g p) := by
      rw [← Finset.mul_expect, endpoint_expect_prod, Finset.expect_comm]
    _ = _ := by rw [endpointFrequencyDefect_mean]

theorem endpointFrequencyMap_bilinear_correction {N : Nat} [NeZero N] [Fact N.Prime]
    (g : ZMod N → Complex) (hg : ∀ x, ‖g x‖ = 1) :
    ∃ c : ZMod N, endpointError (endpointFrequencyMap g) (fun p => c * p.1 * p.2) ≤
      162 * (1 - endpointCubeMean g 4) := by
  obtain ⟨c, hc⟩ := endpoint_symmetric_bilinear_correction (endpointFrequencyMap g)
    (9 * (1 - endpointCubeMean g 4)) (endpointFrequencyMap_symmetric g)
    (endpointFrequencyMap_addition_failure g hg)
  refine ⟨c, ?_⟩
  linarith only [hc]

end LeanProofs.GowersSzemeredi
