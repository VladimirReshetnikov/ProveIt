import GowersSzemeredi.Proofs05VariablePhaseRefinement
import GowersSzemeredi.Proofs05RefinementConstantBounds
import GowersSzemeredi.Proofs18ExceptionalCellSelection

/-! Refining a progression partition into cells of small modular diameter,
while preserving discrepancy and a quantitative bound on the cell count. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- Convert a common-cell-length count into a power of the original modulus. -/
theorem partition_count_power_of_length {N l J : Nat} [NeZero N]
    {e t D c : Real} (ht : 0 ≤ t) (hD : 0 ≤ D) (hc : 0 < c)
    (hl : (N : Real) ^ e / c ≤ l)
    (hcount : (J : Real) ≤ D * N / (l : Real) ^ t) :
    (J : Real) ≤ (D * c ^ t) * (N : Real) ^ (1 - e * t) := by
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hbase : 0 < (N : Real) ^ e / c := by positivity
  have hpow := Real.rpow_le_rpow hbase.le hl ht
  calc
    (J : Real) ≤ D * N / (l : Real) ^ t := hcount
    _ ≤ D * N / ((N : Real) ^ e / c) ^ t :=
      div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos hbase t) hpow
    _ = _ := by
      rw [Real.div_rpow (Real.rpow_nonneg hN.le _) hc.le,
        ← Real.rpow_mul hN.le, Real.rpow_sub hN, Real.rpow_one]
      field_simp

/-- Count constant for a modular-diameter tolerance epsilon*N. -/
def boundaryRefinementConstant (epsilon : Real) : Real :=
  section5LocalRefinementConstant 1 (4 * Real.pi * epsilon)

/-- Keep the fixed refinement constant as a prefactor; the density exponent
is seventeen times the inverse-gain exponent, plus the fixed scale reserve. -/
theorem interval_length_factor_inv_le_scaled {X beta : Real} {n : Nat}
    (hX : 2 ≤ X) (hb : 0 < beta) (hbi : beta⁻¹ ≤ X ^ n) :
    (beta / (8 * boundaryRefinementConstant (beta / 64)))⁻¹ ≤
      (8 * section5LocalRefinementConstant 1 1) * X ^ (17 * n + 64) := by
  have h16 : 16 / Real.pi ≤ X ^ 4 :=
    (div_le_self (by norm_num) (by linarith [Real.pi_gt_three])).trans
      (by linarith [pow_le_pow_left₀ (by norm_num : (0 : Real) ≤ 2) hX 4])
  have hscaled := section5LocalRefinementConstant_le_scaled 1 (4 * Real.pi * (beta / 64))
    (X ^ (4 + n)) (by positivity) (one_le_pow₀ (by linarith)) (by
      rw [pow_add, show (4 * Real.pi * (beta / 64))⁻¹ = 16 / Real.pi * beta⁻¹ by field_simp; ring]
      gcongr)
  rw [show polynomialPartitionConstant 1 = 16 by norm_num [polynomialPartitionConstant]] at hscaled
  have := section5LocalRefinementConstant_pos 1 1
  calc
    _ = 8 * boundaryRefinementConstant (beta / 64) * beta⁻¹ := by rw [inv_div, div_eq_mul_inv]
    _ ≤ 8 * (section5LocalRefinementConstant 1 1 * (X ^ (4 + n)) ^ 16) * X ^ n :=
      mul_le_mul (mul_le_mul_of_nonneg_left hscaled (by norm_num)) hbi (by positivity)
        (by positivity)
    _ = _ := by ring

/-- Absorb the fixed refinement constant as well, and retain the positive
unit range of the interval-length coefficient. -/
theorem interval_length_factor_bounds_of_powers {X beta : Real} {m n : Nat}
    (hX : 2 ≤ X) (hb : 0 < beta) (hb1 : beta ≤ 1)
    (hbi : beta⁻¹ ≤ X ^ n) (hfixed : section5LocalRefinementConstant 1 1 ≤ X ^ m) :
    0 < beta / (8 * boundaryRefinementConstant (beta / 64)) ∧
      beta / (8 * boundaryRefinementConstant (beta / 64)) ≤ 1 ∧
      (beta / (8 * boundaryRefinementConstant (beta / 64)))⁻¹ ≤ X ^ (m + 17 * n + 67) := by
  have hC4 : 4 ≤ boundaryRefinementConstant (beta / 64) :=
    section5LocalRefinementConstant_ge_four _ _
  refine ⟨by positivity, ?_, (interval_length_factor_inv_le_scaled hX hb hbi).trans ?_⟩
  · rw [div_le_one (by positivity)]; linarith only [hb1, hC4]
  · have h8 : (8 : Real) ≤ X ^ 3 :=
      (show (8 : Real) ≤ 2 ^ 3 by norm_num).trans (pow_le_pow_left₀ (by norm_num) hX 3)
    calc
      _ ≤ (X ^ 3 * X ^ m) * X ^ (17 * n + 64) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul h8 hfixed (section5LocalRefinementConstant_pos _ _).le (by positivity)) (by positivity)
      _ = X ^ (m + 17 * n + 67) := by rw [← pow_add, ← pow_add]; congr 1; omega

/-- A proper progression has a small-diameter refinement with a sublinear
cell count, including the short-progression and empty cases. -/
theorem ModAP.small_diameter_refinement {N : Nat} [NeZero N]
    (P : ModAP N) (hP : P.IsProper) (epsilon : Real) (hε : 0 < epsilon) :
    ∃ L : Nat, ∃ R : Fin L → ModAP N,
      IsPartition (fun j ↦ (R j).carrier) P.carrier ∧
      (∀ j, (R j).IsProper) ∧
      (L : Real) ≤ boundaryRefinementConstant epsilon * (P.carrier.card : Real) ^ (15 / 16 : Real) ∧
      ∀ j, diameterAtMostReal (R j).carrier (epsilon * N) := by
  have hid : PolynomialOn 1 Finset.univ (id : ZMod N → ZMod N) := by
    refine ⟨![0, 1], fun x _ ↦ ?_⟩
    simp [Fin.sum_univ_two]
  obtain ⟨L, R, hpart, hproper, hcount, hdiam⟩ :=
    section5_efficient_diameter_refinement_of_corollary_5_6 corollary_5_6_holds
      P id (4 * Real.pi * epsilon) hP (by omega) hid (by positivity)
  have hK : (1 : Real) - (polynomialPartitionConstant 1 : Real)⁻¹ = 15 / 16 := by
    norm_num [polynomialPartitionConstant, Nat.factorial]
  have hscale : 4 * Real.pi * epsilon * N / (4 * Real.pi) = epsilon * N := by
    field_simp
  refine ⟨L, R, hpart, hproper, ?_, ?_⟩
  · simpa only [boundaryRefinementConstant, hK] using hcount
  · intro j
    simpa only [Finset.image_id, hscale] using hdiam j

/-- A global small-diameter refinement preserves the total discrepancy of
every function, and retains the usual Jensen cell-count exponent. -/
theorem small_diameter_partition_refinement {N M : Nat} [NeZero N]
    (Q : Fin M → ModAP N) (epsilon : Real) (hε : 0 < epsilon)
    (hQ : IsPartition (fun i ↦ (Q i).carrier) Finset.univ)
    (hproper : ∀ i, (Q i).IsProper) :
    ∃ L : Nat, ∃ R : Fin L → ModAP N,
      IsPartition (fun j ↦ (R j).carrier) Finset.univ ∧
      IsRefinement (fun j ↦ (R j).carrier) (fun i ↦ (Q i).carrier) ∧
      (∀ j, (R j).IsProper) ∧
      (L : Real) ≤ boundaryRefinementConstant epsilon * (M : Real) ^ (1 / 16 : Real) *
        (N : Real) ^ (15 / 16 : Real) ∧
      (∀ j, diameterAtMostReal (R j).carrier (epsilon * N)) ∧
      ∀ f : ZMod N → Complex,
        (∑ i, ‖∑ x ∈ (Q i).carrier, f x‖) ≤ ∑ j, ‖∑ x ∈ (R j).carrier, f x‖ := by
  choose L R hpart hRproper hcount hdiam using
    fun i ↦ (Q i).small_diameter_refinement (hproper i) epsilon hε
  refine ⟨∑ i, L i, section5Flatten L R, section5Flatten_partition Q L R hQ hpart,
    section5Flatten_refinement Q L R hQ hpart, section5Flatten_isProper L R hRproper, ?_,
    fun j ↦ hdiam _ _, fun f ↦ ?_⟩
  · have hj := section5_sum_rpow_le (by norm_num : 0 < 16) (fun i ↦ (Q i).carrier.card)
      (by simpa using hQ.sum_card : ∑ i, (Q i).carrier.card = N)
    norm_num only [Nat.cast_ofNat] at hj
    rw [Nat.cast_sum, mul_assoc]
    refine (Finset.sum_le_sum fun i _ ↦ hcount i).trans ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (by simpa only [one_div] using hj)
      (section5LocalRefinementConstant_pos _ _).le
  · rw [section5Flatten_sum L R (fun P ↦ ‖∑ x ∈ P.carrier, f x‖)]
    exact Finset.sum_le_sum fun i _ ↦ (hpart i).sum_weights f ▸ norm_sum_le _ _

end LeanProofs.GowersSzemeredi
