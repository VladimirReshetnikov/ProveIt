import GowersSzemeredi.Proofs18TheoremOneDegrees
import GowersSzemeredi.Proofs18LinearFourierObstruction
import GowersSzemeredi.Proofs18GeneralPhaseInverseAssembly
import GowersSzemeredi.Proofs05Corollary58
import GowersSzemeredi.Proofs18TheoremOneDegreesSide

/-! Linear inverse helpers and the printed degree-one Theorem 18.1.

The whole-group progression and Fourier identities remain available to
the sharper integer degree-one inverse. The printed statement follows
from quadratic discrepancy at `alpha^2`: Lemma 3.4 transfers a hypothetical
quadratic uniformity bound back to degree one. The fixed quadratic powers
remain far above the printed degree-one exponent. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- The whole group `Z_N` as one progression with start `0` and step `1`. -/
def wholeModAP (N : Nat) : ModAP N := ⟨0, 1, N⟩

theorem wholeModAP_carrier {N : Nat} [NeZero N] :
    (wholeModAP N).carrier = Finset.univ := by
  classical
  apply Finset.eq_univ_of_forall
  intro y
  unfold ModAP.carrier wholeModAP
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  refine ⟨⟨y.val, ZMod.val_lt y⟩, ?_⟩
  simp

theorem wholeModAP_isProper {N : Nat} [NeZero N] : (wholeModAP N).IsProper := by
  show (wholeModAP N).carrier.card = N
  rw [wholeModAP_carrier, Finset.card_univ, ZMod.card]

theorem wholeModAP_partition {N : Nat} [NeZero N] :
    IsPartition (fun _ : Fin 1 => (wholeModAP N).carrier) Finset.univ := by
  refine ⟨fun x => ?_, fun i j hij => absurd (Subsingleton.elim i j) (bne_iff_ne.mp hij)⟩
  simp [wholeModAP_carrier]

/-- A Fourier coefficient is the whole-group sum twisted by a linear phase. -/
theorem fourier_eq_sum_phaseTwist {N : Nat} [NeZero N] (f : ZMod N → Complex) (r : ZMod N) :
    fourier f r = ∑ x, phaseTwist f (fun x => r * x) x := by
  rw [fourier, ZMod.dft_apply]
  apply Finset.sum_congr rfl
  intro x _
  simp only [phaseTwist, exponential, smul_eq_mul]
  first
    | (rw [mul_comm x r, mul_comm]; done)
    | (rw [mul_comm x r]; ring)
    | ring_nf

/-- **Theorem 18.1 at degree one.** -/
theorem theorem_18_1_degree_one : Theorem181At 1 := by
  apply Theorem181At.of_function_discrepancy
  intro alpha ha ha2
  have ha1 : alpha ≤ 1 := by linarith
  have haSq : 0 < alpha ^ 2 := pow_pos ha 2
  have haSqHalf : alpha ^ 2 ≤ 1 / 2 := by nlinarith
  obtain ⟨hb, hs⟩ := quadratic_discrepancy_fixed_power_lower haSq haSqHalf
  have he : section18Exponent alpha 1 ≤ (alpha ^ 2) ^ (49462 : Nat) := by
    unfold section18Exponent
    rw [← pow_mul]
    exact pow_le_pow_of_le_one ha.le ha1
      ((by norm_num : 2 * 49462 ≤ (2 : Nat) ^ 17).trans
        (Nat.pow_le_pow_right (by norm_num) (by norm_num)))
  refine ⟨quadraticDiscrepancyParameter (alpha ^ 2), quadraticDiscrepancyExponent (alpha ^ 2),
    quadraticExponentialThreshold (alpha ^ 2), he.trans hb, he.trans hs, ?_⟩
  intro N _ _ hN f hf hnot
  apply quadratic_function_discrepancy_bound haSq (by linarith) N hN f hf
  intro hu
  apply hnot
  have h := lemma_3_4_holds N 2 f (alpha ^ 2) (by norm_num) hf hu
  simpa only [Nat.reduceSub, ← Real.sqrt_eq_rpow, Real.sqrt_sq ha.le] using h

end LeanProofs.GowersSzemeredi
