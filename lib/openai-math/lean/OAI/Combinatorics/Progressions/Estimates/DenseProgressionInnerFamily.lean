/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Estimates.FiniteInnerProgressionFamily
import OAI.Combinatorics.Progressions.Fourier.UniformSpectrumSize
import OAI.Combinatorics.Progressions.Lattices.AffineWindowGoodKernelBound

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem balanced_product_side_power {J : Type*} [Fintype J] (L : J → ℝ)
    {K D B : ℝ} (hD : 0 ≤ D) (hL : ∀ j, 0 ≤ L j)
    (hvolume : K ≤ D * ∏ j, L j) (j : J) (hbalance : ∀ i, L i ≤ B * L j) :
    K ≤ (D * B ^ Fintype.card J) * (L j) ^ Fintype.card J := by
  calc
    _ ≤ D * ∏ i, L i := hvolume
    _ ≤ D * ∏ _i : J, B * L j := mul_le_mul_of_nonneg_left
      (Finset.prod_le_prod₀ (fun i _ => hL i) (fun i _ => hbalance i)) hD
    _ = _ := by simp only [Finset.prod_const, Finset.card_univ, mul_pow]; ring

theorem side_power_after_width_loss {K X L B D : ℝ} {s : ℕ}
    (hD : 0 ≤ D) (hX : 0 ≤ X) (hK : K ≤ D * X ^ s) (hwidth : X ≤ B * L) :
    K ≤ (D * B ^ s) * L ^ s := by
  calc
    _ ≤ D * X ^ s := hK
    _ ≤ D * (B * L) ^ s := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hX hwidth s) hD
    _ = _ := by rw [mul_pow]; ring

theorem moderate_coefficient_side_power {A L K : ℝ} {C D h : ℕ}
    (hA : 1 ≤ A) (hL : 0 ≤ L) (hh : 0 < h)
    (hscale : K ≤ L ^ C) (hrange : L ≤ A ^ D) (hcoefficient : A ^ h ≤ K / L ^ h) :
    K ≤ (K / L ^ h) ^ (D * C) := by
  have hA0 : 0 ≤ A := le_trans (by norm_num) hA
  have hAh : A ≤ A ^ h := by
    simpa only [pow_one] using pow_le_pow_right₀ hA hh
  have ha : A ≤ K / L ^ h := hAh.trans hcoefficient
  have hl : L ≤ (K / L ^ h) ^ D :=
    hrange.trans (pow_le_pow_left₀ hA0 ha D)
  calc
    _ ≤ L ^ C := hscale
    _ ≤ ((K / L ^ h) ^ D) ^ C := pow_le_pow_left₀ hL hl C
    _ = _ := (pow_mul _ D C).symm

theorem log_scale_range_power {A L : ℝ} (hA : 0 < A) (hL : 0 < L) (D : ℕ)
    (hrange : Real.log L ≤ D * Real.log A) : L ≤ A ^ D := by
  apply (Real.log_le_log_iff hL (pow_pos hA D)).mp
  simpa only [Real.log_pow] using hrange

theorem exists_minimum_side_power {J : Type*} [Fintype J] [Nonempty J]
    (L : J → ℕ) {K E : ℝ} {s : ℕ} (hL : ∀ j, 0 < L j)
    (hpower : ∀ j, K ≤ E * (L j : ℝ) ^ s) :
    ∃ m : ℕ, 0 < m ∧ (∀ j, m ≤ L j) ∧ K ≤ E * (m : ℝ) ^ s := by
  obtain ⟨j, _, hj⟩ := Finset.exists_min_image Finset.univ L Finset.univ_nonempty
  exact ⟨L j, hL j, fun i => hj i (Finset.mem_univ i), hpower j⟩

theorem scaled_grid_volume_bound {R K P D : ℝ} (hR : 0 ≤ R) (hP : 0 < P)
    (hvolume : K ≤ D * P) : (R * K) / P ≤ R * D := by
  apply (div_le_iff₀ hP).mpr
  nlinarith only [mul_le_mul_of_nonneg_left hvolume hR]

end Erdos3

end

section

namespace Erdos3

theorem card_integerProgressionSupport (c : ℤ) (m H : ℕ) (hm : 0 < m) :
    (integerProgressionSupport c (m : ℤ) H).card = H := by
  unfold integerProgressionSupport
  rw [card_translateSupport, Finset.card_image_of_injective]
  · simp
  · intro x y h
    apply mul_left_cancel₀ (by exact_mod_cast hm.ne' : (m : ℤ) ≠ 0)
    exact h

theorem integerProgressionSupport_point (c : ℤ) (m H : ℕ) (hm : 0 < m) (j : ℕ) (hj : j < H) :
    c + (m : ℤ) * j ∈ integerProgressionSupport c (m : ℤ) H := by
  apply (mem_integerProgressionSupport_iff c m H hm _).mpr
  have hm' : (0 : ℤ) < m := by exact_mod_cast hm
  have hj' : (j : ℤ) < H := by exact_mod_cast hj
  refine ⟨?_, ?_, ?_⟩
  · have := mul_nonneg hm'.le (Int.natCast_nonneg j)
    omega
  · push_cast
    nlinarith
  · simp

theorem progression_endpoint_bounds {L m H : ℕ} {c δ : ℝ}
    (hL : 0 < L) (hm : 0 < m) (hH : 2 ≤ H) (hδ : 0 < δ)
    (hc : 0 ≤ c) (hlast : c + (m : ℝ) * ((H : ℝ) - 1) < L)
    (hdense : δ * L ≤ H) :
    δ * L ≤ (m * H : ℕ) ∧ ((m * H : ℕ) : ℝ) < 2 * L ∧
      m ≤ ⌈2 / δ⌉₊ ∧ |c| ≤ δ⁻¹ * (m * H : ℕ) := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hH2 : (2 : ℝ) ≤ H := by exact_mod_cast hH
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  have hmlast : (m : ℝ) * ((H : ℝ) - 1) < L := by linarith
  have hmL : (m : ℝ) < L := by nlinarith
  have hwidth : (m : ℝ) * H < 2 * L := by nlinarith
  have hlower : δ * L ≤ (m : ℝ) * H := hdense.trans (by nlinarith [Nat.cast_nonneg (α := ℝ) H])
  have hprod : ((m : ℝ) * δ) * L < 2 * L := by
    have he := mul_le_mul_of_nonneg_left hdense (Nat.cast_nonneg (α := ℝ) m)
    nlinarith only [he, hwidth]
  have hstride : (m : ℝ) < 2 / δ :=
    (lt_div_iff₀ hδ).mpr ((mul_lt_mul_iff_left₀ hL0).mp hprod)
  have hcL : c ≤ L := by nlinarith
  have hLwidth : (L : ℝ) ≤ ((m : ℝ) * H) / δ := (le_div_iff₀ hδ).mpr (by nlinarith only [hlower])
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [Nat.cast_mul] using hlower
  · simpa only [Nat.cast_mul] using hwidth
  · exact_mod_cast hstride.le.trans (Nat.le_ceil (2 / δ))
  · rw [abs_of_nonneg hc]
    simpa only [Nat.cast_mul, div_eq_mul_inv, mul_comm] using hcL.trans hLwidth

theorem progression_slice_geometry {L m H : ℕ} (c : ℤ)
    (hL : 0 < L) (hm : 0 < m) (hH : 2 ≤ H) {δ : ℝ} (hδ : 0 < δ)
    (hsubset : integerProgressionSupport c (m : ℤ) H ⊆ Finset.Ico (0 : ℤ) (L : ℤ))
    (hdense : δ * L ≤ ((integerProgressionSupport c (m : ℤ) H).card : ℝ)) :
    δ * L ≤ (m * H : ℕ) ∧ ((m * H : ℕ) : ℝ) < 2 * L ∧
      m ≤ ⌈2 / δ⌉₊ ∧ |(c : ℝ)| ≤ δ⁻¹ * (m * H : ℕ) := by
  have hbase := hsubset (integerProgressionSupport_point c m H hm 0 (by omega))
  have hlast := hsubset (integerProgressionSupport_point c m H hm (H - 1) (by omega))
  have hc0 : 0 ≤ c := by simpa only [Nat.cast_zero, mul_zero, add_zero] using (Finset.mem_Ico.mp hbase).1
  have hh : (c : ℝ) + (m : ℝ) * ((H - 1 : ℕ) : ℝ) < L := by
    exact_mod_cast (Finset.mem_Ico.mp hlast).2
  rw [Nat.cast_sub (by omega : 1 ≤ H), Nat.cast_one] at hh
  rw [card_integerProgressionSupport c m H hm] at hdense
  exact progression_endpoint_bounds hL hm hH hδ (by exact_mod_cast hc0) hh hdense

end Erdos3

end

section

namespace Erdos3

theorem integerProgressionSupport_reindex (r m a H : ℕ) :
    integerProgressionSupport ((r : ℤ) + m * a) m H =
      (Finset.Ico (a : ℤ) (a + H)).image (fun x => (r : ℤ) + m * x) := by
  have he : Finset.Ico (a : ℤ) (a + H) =
      (Finset.Ico (0 : ℤ) H).image (fun x => (a : ℤ) + x) := by
    simpa only [add_zero] using (Finset.image_add_left_Ico (0 : ℤ) H (a : ℤ)).symm
  rw [he, Finset.image_image]
  unfold integerProgressionSupport translateSupport
  rw [Finset.image_image]
  congr 1
  funext x
  change (r : ℤ) + m * a + m * x = r + m * (a + x)
  ring

theorem exists_bounded_progression_reindex {N m H : ℕ} (c : ℤ)
    (hm : 0 < m) (hH : 0 < H) {δ : ℝ} (hδ : 0 < δ) (hδone : δ ≤ 1)
    (hsub : integerProgressionSupport c m H ⊆ Finset.Ico (0 : ℤ) N)
    (hdense : δ * N ≤ (H : ℝ)) :
    ∃ d r a : ℕ, 0 < d ∧ d ≤ ⌈2 / δ⌉₊ ∧ r < ⌈2 / δ⌉₊ ∧ a + H ≤ N ∧
      integerProgressionSupport c m H =
        (Finset.Ico (a : ℤ) (a + H)).image (fun x => (r : ℤ) + d * x) := by
  have hbase := hsub (integerProgressionSupport_point c m H hm 0 hH)
  simp only [Nat.cast_zero, mul_zero, add_zero, Finset.mem_Ico] at hbase
  have hc : (c.toNat : ℤ) = c := Int.toNat_of_nonneg hbase.1
  have hcN : c.toNat < N := by omega
  have hN : 0 < N := by omega
  have hM : 1 ≤ ⌈2 / δ⌉₊ := by
    have h1 : (1 : ℝ) ≤ 2 / δ := (le_div_iff₀ hδ).mpr (by linarith)
    exact_mod_cast h1.trans (Nat.le_ceil _)
  by_cases hsingle : H = 1
  · subst H
    refine ⟨1, 0, c.toNat, by omega, hM, by omega, by omega, ?_⟩
    have he := integerProgressionSupport_reindex 0 1 c.toNat 1
    simp only [Nat.cast_zero, Nat.cast_one, one_mul, zero_add, hc] at he
    simp only [Nat.cast_zero, Nat.cast_one, one_mul, zero_add, hc]
    rw [← he]
    have hz : Finset.Ico (0 : ℤ) 1 = {0} := by
      ext x
      simp only [Finset.mem_Ico, Finset.mem_singleton]
      omega
    simp [integerProgressionSupport, translateSupport, hz, integerStrideHom]
  · have hgeom := progression_slice_geometry c hN hm (by omega) hδ hsub
      (by simpa only [card_integerProgressionSupport c m H hm] using hdense)
    let a := c.toNat / m
    let r := c.toNat % m
    have hmM := hgeom.2.2.1
    have hr : r < m := Nat.mod_lt _ hm
    have ha : a ≤ c.toNat := Nat.div_le_self _ _
    have hlast := hsub (integerProgressionSupport_point c m H hm (H - 1) (by omega))
    have hlastN : c.toNat + m * (H - 1) < N := by
      have ht := (Finset.mem_Ico.mp hlast).2
      rw [← hc] at ht
      exact_mod_cast ht
    have hmul : H - 1 ≤ m * (H - 1) := by nlinarith
    have hrepr : c = (r : ℤ) + m * a := by
      rw [← hc]
      exact_mod_cast (Nat.mod_add_div c.toNat m).symm
    refine ⟨m, r, a, hm, hmM, hr.trans_le hmM, by omega, ?_⟩
    rw [hrepr]
    exact integerProgressionSupport_reindex r m a H

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem progressionFamily_geometric_bounds {g : ℕ} (L m H : Fin g → ℕ) (c : Fin g → ℤ)
    (hL : ∀ j, 0 < L j) (hm : ∀ j, 0 < m j) (hH : ∀ j, 2 ≤ H j) {δ : ℝ} (hδ : 0 < δ)
    (hsubset : ∀ j, integerProgressionSupport (c j) (m j : ℤ) (H j) ⊆ Finset.Ico (0 : ℤ) (L j : ℤ))
    (hdense : ∀ j, δ * L j ≤ ((integerProgressionSupport (c j) (m j : ℤ) (H j)).card : ℝ))
    {K F D E : ℝ} (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hupper : (∏ j, (L j : ℝ)) ≤ F * K) (hlower : K ≤ D * ∏ j, (L j : ℝ))
    (p : ℕ) (hpower : ∀ j, K ≤ E * (L j : ℝ) ^ p) :
    (∀ j, m j ≤ ⌈2 / δ⌉₊) ∧
    (∀ j, |(c j : ℝ)| ≤ δ⁻¹ * (m j * H j : ℕ)) ∧
    (∏ j, ((m j * H j : ℕ) : ℝ)) ≤ ((2 : ℝ) ^ g * F) * K ∧
    K ≤ (D * (δ⁻¹) ^ g) * (∏ j, ((m j * H j : ℕ) : ℝ)) ∧
    ∀ j, K ≤ (E * (δ⁻¹) ^ p) * ((m j * H j : ℕ) : ℝ) ^ p := by
  have hs j := progression_slice_geometry (c j) (hL j) (hm j) (hH j) hδ (hsubset j) (hdense j)
  have hside (j) : (L j : ℝ) ≤ δ⁻¹ * (m j * H j : ℕ) := by
    have hh : (L j : ℝ) ≤ ((m j * H j : ℕ) : ℝ) / δ :=
      (le_div_iff₀ hδ).mpr (by simpa only [mul_comm] using (hs j).1)
    simpa only [div_eq_mul_inv, mul_comm] using hh
  refine ⟨fun j => (hs j).2.2.1, fun j => (hs j).2.2.2, ?_, ?_, ?_⟩
  · calc
      _ ≤ ∏ j, 2 * (L j : ℝ) := Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _)
        (fun j _ => (hs j).2.1.le)
      _ = (2 : ℝ) ^ g * ∏ j, (L j : ℝ) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ ≤ (2 : ℝ) ^ g * (F * K) := mul_le_mul_of_nonneg_left hupper (by positivity)
      _ = _ := by ring
  · calc
      _ ≤ D * ∏ j, (L j : ℝ) := hlower
      _ ≤ D * ∏ j, δ⁻¹ * ((m j * H j : ℕ) : ℝ) := mul_le_mul_of_nonneg_left
        (Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) (fun j _ => hside j)) hD
      _ = _ := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        ring
  · intro j
    exact side_power_after_width_loss hE (Nat.cast_nonneg _) (hpower j) (hside j)

end Erdos3

end

section

namespace Erdos3

theorem progression_slice_endpoint_geometry {L step H : ℕ} (c : ℤ)
    (hL : 0 < L) (hstep : 0 < step) (hH : 2 ≤ H) {δ : ℝ} (hδ : 0 < δ)
    (hsubset : integerProgressionSupport c (step : ℤ) H ⊆ Finset.Ico (0 : ℤ) (L : ℤ))
    (hdense : δ * L ≤ ((integerProgressionSupport c (step : ℤ) H).card : ℝ)) :
    let lower := (c : ℝ) / L
    let width := (step : ℝ) * ((H : ℝ) - 1) / L
    0 ≤ lower ∧ δ / 2 ≤ width ∧ |lower| + |width| ≤ 1 ∧
      (step : ℝ) / L ≤ 2 / ((H : ℝ) - 1) := by
  have hbase := hsubset (integerProgressionSupport_point c step H hstep 0 (by omega))
  have hlast := hsubset (integerProgressionSupport_point c step H hstep (H - 1) (by omega))
  have hc : (0 : ℝ) ≤ c := by
    have hh : 0 ≤ c := by simpa using (Finset.mem_Ico.mp hbase).1
    exact_mod_cast hh
  have hh : (c : ℝ) + (step : ℝ) * ((H : ℝ) - 1) < L := by
    have hh := (Finset.mem_Ico.mp hlast).2
    have he : (c : ℝ) + (step : ℝ) * ((H - 1 : ℕ) : ℝ) < L := by exact_mod_cast hh
    simpa only [Nat.cast_sub (by omega : 1 ≤ H), Nat.cast_one] using he
  have hLp : (0 : ℝ) < L := by exact_mod_cast hL
  have hstep1 : (1 : ℝ) ≤ step := by exact_mod_cast hstep
  have hH2 : (2 : ℝ) ≤ H := by exact_mod_cast hH
  rw [card_integerProgressionSupport c step H hstep] at hdense
  have hwidth : δ / 2 ≤ (step : ℝ) * ((H : ℝ) - 1) / L := by
    apply (le_div_iff₀ hLp).mpr
    have h1 : (H : ℝ) / 2 ≤ (H : ℝ) - 1 := by linarith
    have h2 : (H : ℝ) - 1 ≤ (step : ℝ) * ((H : ℝ) - 1) := by nlinarith
    nlinarith
  have hw0 : 0 ≤ (step : ℝ) * ((H : ℝ) - 1) / L := (half_pos hδ).le.trans hwidth
  refine ⟨div_nonneg hc hLp.le, hwidth, ?_, ?_⟩
  · rw [abs_of_nonneg (div_nonneg hc hLp.le), abs_of_nonneg hw0, ← add_div]
    exact (div_le_one hLp).mpr hh.le
  · apply (le_div_iff₀ (by linarith : 0 < (H : ℝ) - 1)).mpr
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hLp).mpr
    linarith

theorem progression_slice_step_le_inverse_density {L step H : ℕ} (c : ℤ)
    (hL : 0 < L) (hstep : 0 < step) (hH : 2 ≤ H) {δ : ℝ} (hδ : 0 < δ)
    (hsubset : integerProgressionSupport c (step : ℤ) H ⊆ Finset.Ico (0 : ℤ) (L : ℤ))
    (hdense : δ * L ≤ ((integerProgressionSupport c (step : ℤ) H).card : ℝ)) :
    (step : ℝ) ≤ 4 / δ := by
  have hg := (progression_slice_endpoint_geometry c hL hstep hH hδ hsubset hdense).2.2.2
  have hLp : (0 : ℝ) < L := by exact_mod_cast hL
  have hH2 : (2 : ℝ) ≤ H := by exact_mod_cast hH
  have hstep0 : (0 : ℝ) ≤ step := Nat.cast_nonneg _
  have he := (le_div_iff₀ (by linarith : 0 < (H : ℝ) - 1)).mp hg
  rw [div_mul_eq_mul_div] at he
  have he' := (div_le_iff₀ hLp).mp he
  rw [card_integerProgressionSupport c step H hstep] at hdense
  have hh := mul_le_mul_of_nonneg_left (show (H : ℝ) ≤ 2 * ((H : ℝ) - 1) by linarith) hstep0
  have hd := mul_le_mul_of_nonneg_left hdense hstep0
  apply (le_div_iff₀ hδ).mpr
  apply (mul_le_mul_iff_left₀ hLp).mp
  nlinarith only [he', hh, hd]

theorem progression_slice_stride_period_le_exp {L step H period : ℕ} (c : ℤ)
    (hL : 0 < L) (hstep : 0 < step) (hH : 2 ≤ H) {δ F T : ℝ} (hδ : 0 < δ)
    (hsubset : integerProgressionSupport c (step : ℤ) H ⊆ Finset.Ico (0 : ℤ) (L : ℤ))
    (hdense : δ * L ≤ ((integerProgressionSupport c (step : ℤ) H).card : ℝ))
    (hδF : δ⁻¹ ≤ Real.exp F) (hperiod : (period : ℝ) ≤ Real.exp T) :
    ((step * period : ℕ) : ℝ) ≤ Real.exp (F + T + 4) := by
  have hs := progression_slice_step_le_inverse_density c hL hstep hH hδ hsubset hdense
  rw [div_eq_mul_inv] at hs
  rw [Nat.cast_mul]
  calc
    _ ≤ (4 * Real.exp F) * Real.exp T := mul_le_mul
      (hs.trans (mul_le_mul_of_nonneg_left hδF (by norm_num))) hperiod
      (Nat.cast_nonneg _) (by positivity)
    _ ≤ (Real.exp 4 * Real.exp F) * Real.exp T := by
      gcongr
      linarith [Real.add_one_le_exp (4 : ℝ)]
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

theorem progression_endpoint_index_error {H : ℕ} (hH : 2 ≤ H) (j : Fin H) :
    |(j.val : ℝ) / (H : ℝ) - (j.val : ℝ) / ((H : ℝ) - 1)| ≤ 1 / (H : ℝ) := by
  have hH2 : (2 : ℝ) ≤ H := by exact_mod_cast hH
  have hH0 : (0 : ℝ) < H := by linarith
  have hH1 : 0 < (H : ℝ) - 1 := by linarith
  have hj0 : (0 : ℝ) ≤ j.val := Nat.cast_nonneg _
  have hj : (j.val : ℝ) ≤ (H : ℝ) - 1 := by
    have he : j.val + 1 ≤ H := j.isLt
    have he' : (j.val : ℝ) + 1 ≤ H := by exact_mod_cast he
    linarith
  have he : (j.val : ℝ) / (H : ℝ) - (j.val : ℝ) / ((H : ℝ) - 1) =
      -(j.val : ℝ) / ((H : ℝ) * ((H : ℝ) - 1)) := by field_simp; ring
  rw [he, abs_div, abs_neg, abs_of_nonneg hj0, abs_of_pos (mul_pos hH0 hH1)]
  apply (div_le_div_iff₀ (mul_pos hH0 hH1) hH0).mpr
  nlinarith

theorem progression_slice_endpoint_evaluation {L step H : ℕ} (hH : 2 ≤ H) (c : ℤ) (j : Fin H) :
    (c : ℝ) / L + ((step : ℝ) * ((H : ℝ) - 1) / L) *
      ((j.val : ℝ) / ((H : ℝ) - 1)) = ((c : ℝ) + (step : ℝ) * j.val) / L := by
  have hH1 : (H : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ H := by exact_mod_cast hH
    linarith
  field_simp

end Erdos3

end

section

namespace Erdos3

theorem integerProgressionSupport_singleton (c m : ℤ) :
    integerProgressionSupport c m 1 = {c} := by
  have hz : Finset.Ico (0 : ℤ) 1 = {0} := by
    ext x
    simp only [Finset.mem_Ico, Finset.mem_singleton]
    omega
  simp [integerProgressionSupport, translateSupport, hz, integerStrideHom]

theorem exists_same_stride_progression_reindex {N m H : ℕ} (c : ℤ)
    (hm : 0 < m) (hH : 0 < H)
    (hsub : integerProgressionSupport c m H ⊆ Finset.Ico (0 : ℤ) N) :
    ∃ r a : ℕ, r < m ∧ a + H ≤ N ∧
      integerProgressionSupport c m H =
        (Finset.Ico (a : ℤ) (a + H)).image (fun x => (r : ℤ) + m * x) := by
  have hbase := hsub (integerProgressionSupport_point c m H hm 0 hH)
  simp only [Nat.cast_zero, mul_zero, add_zero, Finset.mem_Ico] at hbase
  have hc : (c.toNat : ℤ) = c := Int.toNat_of_nonneg hbase.1
  let a := c.toNat / m
  let r := c.toNat % m
  have ha : a ≤ c.toNat := Nat.div_le_self _ _
  have hlast := hsub (integerProgressionSupport_point c m H hm (H - 1) (by omega))
  have hlastN : c.toNat + m * (H - 1) < N := by
    have ht := (Finset.mem_Ico.mp hlast).2
    rw [← hc] at ht
    exact_mod_cast ht
  have hmul : H - 1 ≤ m * (H - 1) := by nlinarith
  have hrepr : c = (r : ℤ) + m * a := by
    rw [← hc]
    exact_mod_cast (Nat.mod_add_div c.toNat m).symm
  refine ⟨r, a, Nat.mod_lt _ hm, by omega, ?_⟩
  rw [hrepr]
  exact integerProgressionSupport_reindex r m a H

theorem exists_bounded_common_stride_reindex {I : Type*} (N H : I → ℕ) (c : I → ℤ)
    {m : ℕ} (hm : 0 < m) (hH : ∀ i, 0 < H i) {δ : ℝ} (hδ : 0 < δ) (hδone : δ ≤ 1)
    (hsub : ∀ i, integerProgressionSupport (c i) m (H i) ⊆ Finset.Ico (0 : ℤ) (N i))
    (hdense : ∀ i, δ * N i ≤ (H i : ℝ)) :
    ∃ d : ℕ, ∃ r a : I → ℕ, 0 < d ∧ d ≤ ⌈2 / δ⌉₊ ∧
      ∀ i, r i < ⌈2 / δ⌉₊ ∧ a i + H i ≤ N i ∧
        integerProgressionSupport (c i) m (H i) =
          (Finset.Ico (a i : ℤ) (a i + H i)).image (fun x => (r i : ℤ) + d * x) := by
  classical
  by_cases hlong : ∃ i, 2 ≤ H i
  · obtain ⟨i, hi⟩ := hlong
    have hbase := hsub i (integerProgressionSupport_point (c i) m (H i) hm 0 (hH i))
    have hNi : 0 < N i := by
      simp only [Nat.cast_zero, mul_zero, add_zero, Finset.mem_Ico] at hbase
      omega
    have hgeom := progression_slice_geometry (c i) hNi hm hi hδ (hsub i)
      (by simpa only [card_integerProgressionSupport (c i) m (H i) hm] using hdense i)
    choose r a hr ha he using fun i => exists_same_stride_progression_reindex (c i) hm (hH i) (hsub i)
    exact ⟨m, r, a, hm, hgeom.2.2.1, fun i => ⟨(hr i).trans_le hgeom.2.2.1, ha i, he i⟩⟩
  · have hsingle (i : I) : H i = 1 := by have := hH i; have := not_exists.mp hlong i; omega
    have he (i : I) : integerProgressionSupport (c i) m (H i) =
        integerProgressionSupport (c i) 1 (H i) := by simp only [hsingle i, integerProgressionSupport_singleton]
    have hsub1 (i : I) : integerProgressionSupport (c i) 1 (H i) ⊆ Finset.Ico (0 : ℤ) (N i) :=
      he i ▸ hsub i
    choose r a hr ha he' using fun i => exists_same_stride_progression_reindex (m := 1)
      (c i) zero_lt_one (hH i) (hsub1 i)
    have hM : 1 ≤ ⌈2 / δ⌉₊ := by
      have h1 : (1 : ℝ) ≤ 2 / δ := (le_div_iff₀ hδ).mpr (by linarith)
      exact_mod_cast h1.trans (Nat.le_ceil _)
    exact ⟨1, r, a, zero_lt_one, hM, fun i => ⟨(hr i).trans_le hM, ha i, (he i).trans (he' i)⟩⟩

end Erdos3

end

section

namespace Erdos3

theorem exists_dense_progression_inner_family {p : ℝ} (hp : 0 ≤ p) (N : ℕ) :
    ∃ D : Finset (Finset ℤ),
      (D.card : ℝ) ≤ Real.exp (6 * p + 22) ∧
      (∀ A ∈ D, ∃ c : ℤ, ∃ m H : ℕ, 0 < m ∧ A = integerProgressionSupport c m H) ∧
      ∀ (c : ℤ) (m H : ℕ), 0 < m → 0 < H →
        integerProgressionSupport c m H ⊆ Finset.Ico (0 : ℤ) N →
        Real.exp (-p) * N ≤ (H : ℝ) →
        ∃ A ∈ D, A.Nonempty ∧ A ⊆ integerProgressionSupport c m H ∧
          (H : ℝ) ≤ 2 * A.card ∧
          2 * (1 - (A.card : ℝ) / H) ≤ Real.exp (-p) := by
  obtain ⟨D, hcount, hshape, hcover⟩ :=
    exists_finite_inner_progression_family hp N ⌈2 / Real.exp (-p)⌉₊
  have hM : (⌈2 / Real.exp (-p)⌉₊ : ℝ) ≤ Real.exp (p + 2) := by
    rw [Real.exp_neg, div_inv_eq_mul]
    have hceil := (Nat.ceil_lt_add_one (show 0 ≤ 2 / Real.exp (-p) by positivity)).le
    rw [Real.exp_neg, div_inv_eq_mul] at hceil
    have h1 := Real.one_le_exp hp
    have h3 : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
    calc
      _ ≤ 3 * Real.exp p := by linarith
      _ ≤ Real.exp 2 * Real.exp p := mul_le_mul_of_nonneg_right h3 (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add, add_comm]
  refine ⟨D, ?_, ?_, ?_⟩
  · apply hcount.trans
    calc
      _ ≤ Real.exp (p + 2) ^ 2 * Real.exp (4 * p + 18) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hM 2) (Real.exp_nonneg _)
      _ = _ := by rw [pow_two, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  · intro A hA
    obtain ⟨m, r, a, b, hm, _, _, rfl⟩ := hshape A hA
    refine ⟨(r : ℤ) + m * a, m, b - a, hm, ?_⟩
    by_cases hab : a ≤ b
    · have he : (a : ℤ) + (b - a : ℕ) = b := by omega
      rw [integerProgressionSupport_reindex, he]
    · have hi : Finset.Ico (a : ℤ) (b : ℤ) = ∅ := Finset.Ico_eq_empty_of_le (by omega)
      simp [Nat.sub_eq_zero_of_le (by omega : b ≤ a), hi, integerProgressionSupport,
        translateSupport]
  · intro c m H hm hH hsub hdense
    obtain ⟨d, r, a, hd, hdM, hr, hend, he⟩ := exists_bounded_progression_reindex c hm hH
      (Real.exp_pos _) (Real.exp_le_one_iff.mpr (by linarith)) hsub hdense
    obtain ⟨A, hA, hAn, hAS, hhalf, herr⟩ := hcover a H d r hend hH hd hdM hr hdense
    exact ⟨A, hA, hAn, he.symm ▸ hAS, hhalf, herr⟩

end Erdos3

end

end OAI
