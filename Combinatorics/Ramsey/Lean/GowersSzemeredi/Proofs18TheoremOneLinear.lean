import GowersSzemeredi.Proofs18TheoremOneDegrees
import GowersSzemeredi.Proofs18LinearFourierObstruction
import GowersSzemeredi.Proofs18GeneralPhaseInverseAssembly

/-! Theorem 18.1 at degree one.

If a set is not uniform of degree one, its balanced function has a Fourier
coefficient larger than `sqrt(alpha)*N` (`linear_nonuniformity_large_fourier`).
That coefficient is the twisted sum of the balanced function over the whole
group, viewed as one proper progression, twisted by the linear phase
`x ↦ r*x`. The general untwisting theorem
(`polynomial_phase_inverse_partition`, degree one, one cell) then gives a
proper partition with discrepancy `sqrt(alpha)*N/2` and average cell size
at least `N^(1/64)`. Both dominate `section18Exponent alpha 1`. -/
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
  intro alpha hα hα2
  have hα1 : alpha ≤ 1 := by linarith
  let e : Real := 1 / 2
  let beta : Real := Real.sqrt alpha
  have hβ : 0 < beta := Real.sqrt_pos.mpr hα
  have he : (0 : Real) < e := by norm_num [e]
  refine ⟨⌈positivePowerThreshold (phaseInverseConstant 1 beta 1) 1
      (phaseInverseExponent 1 e)⌉₊, fun N _ _ hN A hnot => ?_⟩
  have hNth : positivePowerThreshold (phaseInverseConstant 1 beta 1) 1
      (phaseInverseExponent 1 e) ≤ (N : Real) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hN)
  have hN1 : (1 : Real) ≤ N := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  obtain ⟨r, hr⟩ := linear_nonuniformity_large_fourier (balanced A) alpha hα.le
    (balanced_discValued A) hnot
  have hpoly : ∀ _i : Fin 1, PolynomialOn 1 Finset.univ (fun x : ZMod N => r * x) := by
    intro _
    refine ⟨![0, r], fun x _ => ?_⟩
    simp [Fin.sum_univ_two]
  have hcount : ((1 : Nat) : Real) ≤ 1 * (N : Real) ^ (1 - e) := by
    rw [Nat.cast_one, one_mul]
    exact Real.one_le_rpow hN1 (by norm_num [e])
  have hdis : beta * N ≤ ∑ _i : Fin 1,
      ‖∑ x ∈ (wholeModAP N).carrier, phaseTwist (balanced A) (fun x => r * x) x‖ := by
    rw [Fin.sum_univ_one, wholeModAP_carrier, ← fourier_eq_sum_phaseTwist]
    exact hr.le
  obtain ⟨J, R, hR, hRproper, hsize, hdisR⟩ :=
    polynomial_phase_inverse_partition (k := 1) (K := 1) le_rfl he hβ one_pos (balanced A)
      (balanced_discValued A) (fun _ => wholeModAP N) (fun _ => fun x => r * x) hpoly
      wholeModAP_partition hcount hdis hNth
  have hexp1 : section18Exponent alpha 1 ≤ phaseInverseExponent 1 e := by
    have hpc : phaseInverseExponent 1 e = (1 / 2) ^ (6 : Nat) := by
      norm_num [phaseInverseExponent, polynomialPartitionConstant, e, Nat.factorial]
    have h6 : (6 : Nat) ≤ 2 ^ 2 ^ (1 + 10) :=
      (by norm_num : (6 : Nat) ≤ 2 ^ 3).trans
        (Nat.pow_le_pow_right (by norm_num) (by norm_num))
    rw [hpc]
    unfold section18Exponent
    exact (pow_le_pow_of_le_one hα.le hα1 h6).trans (pow_le_pow_left₀ hα.le hα2 6)
  have hexp2 : section18Exponent alpha 1 ≤ beta / 2 := by
    have hsq : alpha ≤ Real.sqrt alpha := by
      calc alpha = Real.sqrt (alpha ^ 2) := (Real.sqrt_sq hα.le).symm
        _ ≤ Real.sqrt alpha := Real.sqrt_le_sqrt (by nlinarith)
    have h2 : (2 : Nat) ≤ 2 ^ 2 ^ (1 + 10) :=
      (by norm_num : (2 : Nat) ≤ 2 ^ 1).trans
        (Nat.pow_le_pow_right (by norm_num) (by norm_num))
    unfold section18Exponent
    calc alpha ^ 2 ^ 2 ^ (1 + 10) ≤ alpha ^ 2 := pow_le_pow_of_le_one hα.le hα1 h2
      _ ≤ alpha / 2 := by
        rw [pow_two]
        linarith only [mul_le_mul_of_nonneg_left hα2 hα.le]
      _ ≤ beta / 2 := by
        have : alpha ≤ beta := hsq
        linarith
  refine ⟨J, R, hR, hRproper, ?_, ?_⟩
  · exact (Real.rpow_le_rpow_of_exponent_le hN1 hexp1).trans hsize
  · exact (mul_le_mul_of_nonneg_right hexp2 (Nat.cast_nonneg N)).trans hdisR

end LeanProofs.GowersSzemeredi
