import GowersSzemeredi.Proofs05TargetPartition
import GowersSzemeredi.Proofs02Partition

/-!
# The strong degree-one polynomial partition

The linear partition lemma followed by a target-length refinement supplies the
base case for the degree induction in Corollary 5.6. We retain twice the
advertised diameter exponent, as required by simultaneous refinement in 5.9.
The proof explicitly rounds the diameter upwards and refines every long cell.
-/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

/-- An integral diameter parameter with enough length for the target refinement.
Writing r = u^8 makes all rounding estimates elementary. -/
private theorem linear_target_scale {N r v : Nat} (u : Real)
    (hu : 4 ≤ u) (hr : (r : Real) = u ^ 8) (hrN : r ≤ N)
    (hv : (v : Real) ^ 2 ≤ u) :
    ∃ s : Nat, 0 < s ∧ s ≤ N ∧ N ≤ r * s ∧
      (s : Real) ≤ (N : Real) / u ∧
      (v : Real) ^ 2 ≤ Real.sqrt ((r : Real) * s / (16 * N)) := by
  have hu0 : 0 < u := by linarith
  have hu2 : 16 ≤ u ^ 2 := by nlinarith
  have hu16 : 16 * u ^ 2 ≤ u ^ 4 := by linarith [mul_le_mul_of_nonneg_right hu2 (sq_nonneg u)]
  have htwoU : 2 * u ≤ u ^ 4 := by nlinarith [mul_le_mul_of_nonneg_left hu hu0.le]
  have hN : u ^ 4 * u ^ 4 ≤ N := by
    rw [show u ^ 4 * u ^ 4 = r by rw [hr]; ring]
    exact_mod_cast hrN
  have hN0 : (0 : Real) < N := (by positivity : (0 : Real) < u ^ 4 * u ^ 4).trans_le hN
  -- `s = ⌈x⌉` with `x = N / u⁴ ≥ u⁴`, so `x ≤ s < x + 1 ≤ 2x`
  set x : Real := N / u ^ 4
  have hxu : x * u ^ 4 = N := div_mul_cancel₀ _ (by positivity)
  have hx : u ^ 4 ≤ x := (le_div_iff₀ (by positivity)).mpr hN
  have hx0 : 0 ≤ x := by linarith
  obtain ⟨s, hslo, hshi⟩ : ∃ s : Nat, x ≤ s ∧ (s : Real) < x + 1 :=
    ⟨⌈x⌉₊, Nat.le_ceil x, Nat.ceil_lt_add_one hx0⟩
  have hscale : u ^ 4 * N ≤ r * s := by
    rw [hr, ← hxu]
    linarith [mul_le_mul_of_nonneg_left hslo (by positivity : (0 : Real) ≤ u ^ 8)]
  refine ⟨s, by exact_mod_cast (show (0 : Real) < s by linarith), ?_, ?_, ?_, ?_⟩
  · exact_mod_cast (show (s : Real) ≤ N by
      linarith [mul_le_mul_of_nonneg_left (show (2 : Real) ≤ u ^ 4 by linarith) hx0])
  · exact_mod_cast (show (N : Real) ≤ r * s by
      linarith [mul_le_mul_of_nonneg_right (show (1 : Real) ≤ u ^ 4 by linarith) hN0.le])
  · rw [le_div_iff₀ hu0]
    linarith [mul_le_mul_of_nonneg_right (show (s : Real) ≤ 2 * x by linarith) hu0.le,
      mul_le_mul_of_nonneg_left htwoU hx0]
  · refine Real.le_sqrt_of_sq_le ((le_div_iff₀ (by positivity)).mpr ?_)
    linarith [mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (sq_nonneg _) hv 2)
      (by positivity : (0 : Real) ≤ 16 * N), mul_le_mul_of_nonneg_right hu16 hN0.le]

/-- The linear partition, with prescribed target lengths and the stronger
r^(-1/8) diameter, already holds above the modest threshold 65536. -/
theorem section5_strong_linear_partition (N r v : Nat) [NeZero N]
    (phi : ZMod N → ZMod N) (hphi : PolynomialOn 1 Finset.univ phi)
    (hrlarge : 65536 ≤ r) (hrN : r ≤ N) (hv : 1 ≤ v)
    (hvupper : (v : Real) ≤ (r : Real) ^ ((1 : Real) / 16)) :
    ∃ M : Nat, ∃ P : Fin M → NatAP,
      0 < M ∧ IsNatAPPartition P (Finset.range r) ∧
      (∀ j, (P j).IsProper ∧ 0 < (P j).length ∧
        ((P j).length = v - 1 ∨ (P j).length = v)) ∧
      ∀ j, diameterAtMostReal
        ((P j).carrier.image fun x : Nat => phi (x : ZMod N))
        ((r : Real) ^ (-((1 : Real) / 8)) * N) := by
  have hr : 0 < r := by omega
  have hr0 : (0 : Real) < r := by exact_mod_cast hr
  -- the diameter scale `u = r^(1/8) ≥ 4`, with `r = u^8` and `v² ≤ u`
  set u : Real := (r : Real) ^ ((1 : Real) / 8) with hudef
  have hu8 : (r : Real) = u ^ 8 := by
    rw [hudef, ← Real.rpow_natCast, ← Real.rpow_mul hr0.le]
    norm_num
  have hu : 4 ≤ u := (pow_le_pow_iff_left₀ (by norm_num) (by positivity) (by norm_num : 8 ≠ 0)).mp
    (by rw [← hu8]; exact_mod_cast hrlarge)
  have hvu : (v : Real) ^ 2 ≤ u := by
    calc (v : Real) ^ 2 ≤ ((r : Real) ^ ((1 : Real) / 16)) ^ 2 := by gcongr
      _ = u := by rw [hudef, ← Real.rpow_natCast, ← Real.rpow_mul hr0.le]; norm_num
  obtain ⟨s, hs, hsN, hrs, hsdiam, hlen⟩ := linear_target_scale u hu hu8 hrN hvu
  -- the linear partition at scale `s`, then the target-length refinement
  have hlin : NatToZModLinear r (fun x : Nat => phi (x : ZMod N)) := by
    obtain ⟨c, hc⟩ := hphi
    exact ⟨c 1, c 0, fun x _ => by
      simpa [Fin.sum_univ_two, add_comm] using hc (x : ZMod N) (Finset.mem_univ _)⟩
  obtain ⟨m, Q, hQpart, hQcells⟩ :=
    lemma_2_3_holds N r s (NeZero.pos N) hr hs hrN hsN hrs _ hlin
  obtain ⟨M, P, hM, hpart, hcells, hsub⟩ :=
    section5_refine_target_lengths Q hr hv hQpart (fun j => (hQcells j).1)
      fun j => by exact_mod_cast hlen.trans (hQcells j).2.2.1
  refine ⟨M, P, hM, hpart, hcells, fun j => ?_⟩
  obtain ⟨i, hi⟩ := hsub j
  obtain ⟨a, ha⟩ := (hQcells i).2.1
  refine ⟨s, ⟨a, (Finset.image_mono _ hi).trans ha⟩, hsdiam.trans_eq ?_⟩
  rw [Real.rpow_neg hr0.le]
  simp [u, div_eq_mul_inv, mul_comm]

/-- The exact degree-one specialization of the strong Corollary 5.6 API. -/
theorem corollary_5_6_strong_diameter_degree_one
    (N r v : Nat) [NeZero N] (phi : ZMod N → ZMod N)
    (hphi : PolynomialOn 1 Finset.univ phi)
    (hthreshold : polynomialPartitionThreshold 1 < r) (hrN : r ≤ N)
    (hv : 1 ≤ v)
    (hvupper : (v : Real) ≤ (r : Real) ^ (polynomialPartitionConstant 1 : Real)⁻¹) :
    ∃ M : Nat, ∃ P : Fin M → NatAP,
      0 < M ∧ IsNatAPPartition P (Finset.range r) ∧
      (∀ j, (P j).IsProper ∧ 0 < (P j).length ∧
        ((P j).length = v - 1 ∨ (P j).length = v)) ∧
      ∀ j, diameterAtMostReal
        ((P j).carrier.image fun x : Nat => phi (x : ZMod N))
        ((r : Real) ^ (-(2 * (polynomialPartitionConstant 1 : Real)⁻¹)) * N) := by
  have hlarge : 65536 ≤ r := by
    have hbase : 65536 ≤ weylThreshold 1 := by
      change 2 ^ 16 ≤ 2 ^ (2 ^ (40 * 1 ^ 3))
      apply Nat.pow_le_pow_right (by norm_num)
      norm_num
    exact hbase.trans ((weylThreshold_le_polynomialPartitionThreshold 1).trans hthreshold.le)
  have hconst : polynomialPartitionConstant 1 = 16 := by norm_num [polynomialPartitionConstant]
  simpa only [hconst, Nat.cast_ofNat, show (16 : Real)⁻¹ = 1 / 16 from by norm_num,
    show (2 : Real) * (1 / 16) = 1 / 8 from by norm_num] using
    section5_strong_linear_partition N r v phi hphi hlarge hrN hv (by simpa [hconst] using hvupper)

end LeanProofs.GowersSzemeredi
