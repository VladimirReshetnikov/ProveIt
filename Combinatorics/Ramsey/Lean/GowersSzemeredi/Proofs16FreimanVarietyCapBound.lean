import GowersSzemeredi.Proofs16DeepVarietyCover

/-! Quantitative lower bounds for the capped Freiman-variety exponent.

The exponential radius threshold enters the cap only through its logarithm.
The resulting exponent has inverse-polynomial dependence on the structure
budget, rather than inverse-exponential dependence on that budget.
-/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- An exponential radius lower bound costs only a linear factor in its
logarithmic budget when passing from large boxes to all boxes. -/
theorem section16FreimanVariety_capped_lower {C p : Nat} (hC : 2 ≤ C) (hp : 0 < p)
    (s r : Nat) {B : Real} (hB : 0 ≤ B) :
    1 / (4 * section16FreimanVarietyDegree p s r *
      ((C : Real) * (s + r + 1) + 17 + B)) ≤
    section16CappedWidthExponent (section16FreimanVarietyExponent p s r)
      (section16FreimanVarietyThreshold C p s r (Real.exp (-B))) := by
  let d := section16FreimanVarietyDegree p s r
  let A := C * (s + r + 1)
  let M := max A (Nat.ceil (16 / Real.exp (-B)))
  have hd : 0 < (d : Real) := by
    exact_mod_cast section16FreimanVarietyDegree_pos hp s r
  have hA : 2 ≤ A := by dsimp [A]; nlinarith
  have hM : 2 ≤ M := hA.trans (le_max_left _ _)
  have hMR : (1 : Real) < M := by exact_mod_cast (show 1 < M by omega)
  have hE : 1 ≤ Real.exp B := Real.one_le_exp hB
  have hceil : (Nat.ceil (16 / Real.exp (-B)) : Real) ≤ 17 * Real.exp B := by
    have h := (Nat.ceil_lt_add_one (by positivity : (0 : Real) ≤ 16 / Real.exp (-B))).le
    rw [Real.exp_neg, div_inv_eq_mul] at h ⊢
    nlinarith
  have hMupper : (M : Real) ≤ ((A : Real) + 17) * Real.exp B := by
    dsimp only [M]
    rw [Nat.cast_max]
    apply max_le
    · nlinarith [mul_le_mul_of_nonneg_left hE (Nat.cast_nonneg A)]
    · exact hceil.trans (by nlinarith [mul_nonneg (Nat.cast_nonneg A) (Real.exp_pos B).le])
  have hlogM : Real.log (M : Real) ≤ (A : Real) + 17 + B := by
    have h := Real.log_le_log (by positivity : (0 : Real) < M) hMupper
    rw [Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_exp] at h
    have ha := Real.log_le_sub_one_of_pos (by positivity : (0 : Real) < (A : Real) + 17)
    linarith
  have hpow : (2 : Real) ≤ (M : Real) ^ (2 * d) := by
    have hn : 0 < 2 * d := by exact_mod_cast (show (0 : Real) < 2 * d by positivity)
    exact (show (2 : Real) ≤ M by exact_mod_cast hM).trans (le_self_pow₀ hMR.le (by omega : 2 * d ≠ 0))
  have hlogT : Real.log (max 2 ((M : Real) ^ (2 * d))) ≤
      (2 * d : Real) * ((A : Real) + 17 + B) := by
    rw [max_eq_right hpow, Real.log_pow]
    push_cast
    exact mul_le_mul_of_nonneg_left hlogM (by positivity)
  have hL : 1 ≤ (A : Real) + 17 + B := by nlinarith [show (0 : Real) ≤ A from Nat.cast_nonneg A]
  have hlog2 : (1 / 2 : Real) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : Real) < 2)
    norm_num at h ⊢
    exact h
  change 1 / (4 * (d : Real) * ((C : Real) * (s + r + 1) + 17 + B)) ≤ _
  have hcastA : (A : Real) = (C : Real) * (s + r + 1) := by dsimp [A]; push_cast; rfl
  rw [← hcastA]
  change _ ≤ min (((2 * d : Nat) : Real)⁻¹)
    (Real.log 2 / Real.log (max 2 ((M ^ (2 * d) : Nat) : Real)))
  push_cast
  apply le_min
  · rw [← one_div]
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    nlinarith
  · apply (le_div_iff₀ (Real.log_pos (lt_of_lt_of_le (by norm_num) (le_max_left _ _)))).mpr
    have h := mul_le_mul_of_nonneg_left hlogT
      (by positivity : 0 ≤ 1 / (4 * (d : Real) * ((A : Real) + 17 + B)))
    have heq : 1 / (4 * (d : Real) * ((A : Real) + 17 + B)) *
        (2 * d * ((A : Real) + 17 + B)) = (1 / 2 : Real) := by
      field_simp
      ring
    rw [heq] at h
    exact h.trans hlog2

/-- The all-box exponent is inverse-polynomial of degree seventeen in the
structure budget, with explicit dependence on the universal constants. -/
theorem section16DeepVarietyCoverExponent_lower {C p : Nat} (hC : 2 ≤ C) (hp : 0 < p)
    (D : Nat) {c : Real} (hc : 0 < c) (hc1 : c ≤ 1) :
    1 / (1024 * (p : Real)^2 * (4 * C + 18) * (milicevicBound D c + 2)^17) ≤
      section16DeepVarietyCoverExponent C p D c := by
  let B := milicevicBound D c
  let R := Nat.ceil B
  have hB : 0 ≤ B := by
    have h := two_le_milicevic_base hc hc1
    exact pow_nonneg (by linarith) D
  have hR : (R : Real) ≤ B + 1 := (Nat.ceil_lt_add_one hB).le
  have hR1 : (R : Real) + 1 ≤ B + 2 := by linarith
  have hR2 : (2 * R : Nat) + (1 : Real) ≤ 2 * (B + 2) := by
    push_cast
    linarith
  have hd : (section16FreimanVarietyDegree p (2 * R) R : Real) ≤
      256 * (p : Real)^2 * (B + 2)^16 := by
    have h1 := pow_le_pow_left₀ (by positivity : (0 : Real) ≤ R + 1) hR1 8
    have h2 := pow_le_pow_left₀ (by positivity : (0 : Real) ≤ (2 * R : Nat) + 1) hR2 8
    have h := mul_le_mul h1 h2 (by positivity) (by positivity)
    have h' := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ (p : Real)^2)
    unfold section16FreimanVarietyDegree
    push_cast at *
    nlinarith only [h']
  have hL : (C : Real) * ((2 * R : Nat) + R + 1) + 17 + B ≤
      (4 * C + 18) * (B + 2) := by
    push_cast
    have h := mul_le_mul_of_nonneg_left hR (Nat.cast_nonneg C : (0 : Real) ≤ C)
    nlinarith [mul_nonneg (Nat.cast_nonneg C : (0 : Real) ≤ C) hB]
  have hdpos : (0 : Real) < section16FreimanVarietyDegree p (2 * R) R := by
    exact_mod_cast section16FreimanVarietyDegree_pos hp (2 * R) R
  apply le_trans _ (section16FreimanVariety_capped_lower hC hp (2 * R) R hB)
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  have h := mul_le_mul hd hL (by positivity) (by positivity)
  convert mul_le_mul_of_nonneg_left h (by norm_num : (0 : Real) ≤ 4) using 1 <;> ring

/-- A conditional dense graph piece with an explicit inverse-polynomial
cover exponent; the underlying deep structure is still a hypothesis. -/
theorem exists_deep_variety_polynomial_graph_cover :
  ∃ C p : Nat, 2 ≤ C ∧ 0 < p ∧
  ∀ D : Nat, MilicevicDeepVarietyStructure D →
    ∀ (N : Nat) [NeZero N] [Fact N.Prime] (A : Finset (ZMod N × ZMod N))
      (phi : ZMod N × ZMod N → ZMod N) (c : Real),
      0 < c → c ≤ 1 → c * (N : Real)^2 ≤ A.card → IsEBihomomorphism A phi {0} →
      ∃ G : Finset (Point N 2 × ZMod N),
        IsGraphOver G A phi ∧
        Real.exp (-milicevicBound D c) * (N : Real)^2 ≤ G.card ∧
        MultiplyLinearWith (fun _ => 9)
          (fun _ => 1 / (1024 * (p : Real)^2 * (4 * C + 18) *
            (milicevicBound D c + 2)^17)) G := by
  obtain ⟨C, p, hC, hp, hcover⟩ := exists_deep_variety_graph_cover
  refine ⟨C, p, hC, hp, ?_⟩
  intro D hD N _ _ A phi c hc hc1 hA hphi
  obtain ⟨G, hG, hmass, hML⟩ := hcover D hD N A phi c hc hA hphi
  refine ⟨G, hG, hmass, hML.weaken (by intros; exact le_rfl) ?_ ?_⟩
  · intros
    have hbase := two_le_milicevic_base hc hc1
    have hB : 0 ≤ milicevicBound D c := pow_nonneg (by linarith) D
    positivity
  · intros
    exact section16DeepVarietyCoverExponent_lower hC hp D hc hc1

end LeanProofs.GowersSzemeredi
