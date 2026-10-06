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
  have hu1 : 1 ≤ u := by linarith
  have hu4 : 0 < u ^ 4 := pow_pos hu0 _
  have hu4one : 1 ≤ u ^ 4 := one_le_pow₀ hu1
  have hu4N : u ^ 4 ≤ (N : Real) := by
    calc
      u ^ 4 ≤ u ^ 8 := pow_le_pow_right₀ hu1 (by omega)
      _ = r := hr.symm
      _ ≤ N := by exact_mod_cast hrN
  have hN : (0 : Real) < N := hu4.trans_le hu4N
  have ht : 1 ≤ (N : Real) / u ^ 4 := (le_div_iff₀ hu4).2 (by simpa using hu4N)
  let s := Nat.ceil ((N : Real) / u ^ 4)
  have hslo : (N : Real) / u ^ 4 ≤ s := Nat.le_ceil _
  have hshi : (s : Real) ≤ 2 * ((N : Real) / u ^ 4) := by
    have h := Nat.ceil_lt_add_one (show 0 ≤ (N : Real) / u ^ 4 by positivity)
    change (s : Real) < (N : Real) / u ^ 4 + 1 at h
    linarith
  have hspos : 0 < s := by
    have hs : (0 : Real) < s := lt_of_lt_of_le (by positivity) hslo
    exact_mod_cast hs
  have hsN : s ≤ N := by
    apply Nat.ceil_le.mpr
    apply (div_le_iff₀ hu4).2
    nlinarith
  have hu2 : 16 ≤ u ^ 2 := by nlinarith
  have hu16 : 16 * u ^ 2 ≤ u ^ 4 := by nlinarith [sq_nonneg (u ^ 2 - 16)]
  have htwoU : 2 * u ≤ u ^ 4 := by nlinarith [sq_nonneg (u - 4)]
  have hsdiam : (s : Real) ≤ (N : Real) / u := by
    apply hshi.trans
    apply (le_div_iff₀ hu0).2
    have hscaled := mul_le_mul_of_nonneg_left htwoU (div_nonneg hN.le hu4.le)
    calc
      (2 * ((N : Real) / u ^ 4)) * u = ((N : Real) / u ^ 4) * (2 * u) := by ring
      _ ≤ ((N : Real) / u ^ 4) * u ^ 4 := hscaled
      _ = N := div_mul_cancel₀ _ hu4.ne'
  have hscale : u ^ 4 * (N : Real) ≤ (r : Real) * s := by
    have h := (div_le_iff₀ hu4).mp hslo
    have hmul := mul_le_mul_of_nonneg_left h hu4.le
    calc
      u ^ 4 * (N : Real) ≤ u ^ 4 * ((s : Real) * u ^ 4) := hmul
      _ = (r : Real) * s := by rw [hr]; ring
  have hrs : N ≤ r * s := by
    have h : (N : Real) ≤ (r : Real) * s := by nlinarith
    exact_mod_cast h
  have hv4 : ((v : Real) ^ 2) ^ 2 ≤ u ^ 2 :=
    pow_le_pow_left₀ (sq_nonneg _) hv 2
  have hlen : (v : Real) ^ 2 ≤ Real.sqrt ((r : Real) * s / (16 * N)) := by
    apply Real.le_sqrt_of_sq_le
    apply (le_div_iff₀ (by positivity : (0 : Real) < 16 * N)).2
    calc
      ((v : Real) ^ 2) ^ 2 * (16 * N) ≤ u ^ 2 * (16 * N) :=
        mul_le_mul_of_nonneg_right hv4 (by positivity)
      _ = (16 * u ^ 2) * N := by ring
      _ ≤ u ^ 4 * N := mul_le_mul_of_nonneg_right hu16 hN.le
      _ ≤ (r : Real) * s := hscale
  exact ⟨s, hspos, hsN, hrs, hsdiam, hlen⟩

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
  classical
  have hr : 0 < r := by omega
  have hr0 : (0 : Real) < r := by exact_mod_cast hr
  let u : Real := (r : Real) ^ ((1 : Real) / 8)
  have hu : 4 ≤ u := by
    have hbase : (4 : Real) ^ (8 : Nat) ≤ r := by exact_mod_cast hrlarge
    have h := Real.rpow_le_rpow (by positivity) hbase (by norm_num : (0 : Real) ≤ 1 / 8)
    have hfour : ((4 : Real) ^ (8 : Nat)) ^ ((1 : Real) / 8) = 4 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      norm_num
    simpa only [hfour, u] using h
  have hu8 : (r : Real) = u ^ 8 := by
    dsimp only [u]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr0.le]
    norm_num
  have hvu : (v : Real) ^ 2 ≤ u := by
    have h := pow_le_pow_left₀ (Nat.cast_nonneg v) hvupper 2
    have heq : ((r : Real) ^ ((1 : Real) / 16)) ^ (2 : Nat) = u := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hr0.le]
      norm_num [u]
    exact h.trans_eq heq
  obtain ⟨s, hs, hsN, hrs, hsdiam, hlen⟩ := linear_target_scale u hu hu8 hrN hvu
  have hlin : NatToZModLinear r (fun x : Nat => phi (x : ZMod N)) := by
    obtain ⟨c, hc⟩ := hphi
    refine ⟨c 1, c 0, ?_⟩
    intro x hx
    simpa [Fin.sum_univ_two, add_comm] using hc (x : ZMod N) (Finset.mem_univ _)
  obtain ⟨m, Q, hQpart, hQcells⟩ :=
    lemma_2_3_holds N r s (NeZero.pos N) hr hs hrN hsN hrs _ hlin
  have hlong (j : Fin m) : v ^ 2 ≤ (Q j).length := by
    have h := hlen.trans (hQcells j).2.2.1
    exact_mod_cast h
  obtain ⟨M, P, hM, hpart, hcells, hsub⟩ :=
    section5_refine_target_lengths Q hr hv hQpart (fun j => (hQcells j).1) hlong
  refine ⟨M, P, hM, hpart, hcells, ?_⟩
  intro j
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
