import GowersSzemeredi.Proofs18UniformCovers
import GowersSzemeredi.Proofs16SplitStepFejer

/-! **The class covers at degree `2^(23·2^l)` under the Fejér θ₁** (Notes L.16d).

The Fejér analogue of `Proofs18TightClasses`. The split classes of
`splitUniformClass_all_fejer` have degrees `(a_l, D_l)` with
`2^(l+6)·a_l ≤ 2^(14·2^l)` and `D_l ≤ 2^(22·2^l)`
(`split_pair_with_bounds 14`, `split_pair_fejer_bound`), against the printed
`68·2^l`. So:
* `uDeg23 l = 2^(23·2^l)` and `split_pair_fejer_le_uDeg23`:
  `a_l + D_l + l + 1 ≤ uDeg23 l`;
* `polyCoverAt_one_uniform_low`: the dimension-one cover at any degree
  `D ≥ 2^17`. The printed `polyCoverAt_one_uniform` asks for `2^132`, the
  dimension-two exponent; in dimension one the count is at most `w^(2^15)`
  and the inverse exponent at most `w^(2^17)`;
* `polyCoverAt_class23`: **the class cover in dimension `l` at degree
  `uDeg23 l`**, the input of the Section 18 envelope.

`polyCoverAt_class23` and `split_pair_fejer_le_uDeg23` are in
`Proofs18TightClassesFejerSide`, outside the final route. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- **The dimension-one cover at any degree `D ≥ 2^17`.** -/
theorem polyCoverAt_one_uniform_low {V : Real} (hV : 1 ≤ V) {D : Nat} (hD : 2 ^ 17 ≤ D) :
    PolyCoverAt 1 (uCount V D) (uExp V D) := by
  have hbase : ∀ gamma theta rho : Real, 0 < gamma → gamma ≤ 1 → 0 < theta → theta ≤ 1 →
      0 < rho → rho ≤ 1 →
      (2 : Real) ≤ 2 / (gamma * theta * rho) ∧ rho⁻¹ ≤ (2 / (gamma * theta * rho)) ^ 1 ∧
      (section16BaseFamilyBound gamma theta : Real) ≤
        (2 / (gamma * theta * rho)) ^ ((2 : Nat) ^ 14) ∧
      ∀ n : Nat, n ≤ 2 ^ 17 → (2 / (gamma * theta * rho)) ^ n ≤ uCount V D gamma theta rho := by
    intro gamma theta rho hg hg1 ht ht1 hr hr1
    obtain ⟨hv2, hvw, hrw⟩ := prod_scale_radius_bounds hg hg1 ht ht1 hr hr1
    have hw := two_div_le_uniformBase hV hg ht hr
    refine ⟨hv2.trans hvw, by simpa only [pow_one] using hrw,
      (section16BaseFamilyBound_le_dyadic_power hg hg1 ht ht1).trans
        (pow_le_pow_left₀ (by positivity) hvw _), fun n hn => le_max_of_le_right ?_⟩
    exact (pow_le_pow_left₀ (by positivity) hw _).trans
      (pow_le_pow_right₀ (one_le_two.trans ((hv2.trans hvw).trans hw)) (hn.trans hD))
  refine polyCoverAt_one.weaken (fun gamma theta rho hg hg1 ht ht1 hr hr1 => ?_)
    (fun gamma theta rho hg hg1 ht ht1 hr hr1 => (uExp_pos hV D hg hg1 ht ht1 hr hr1).1)
    (fun gamma theta rho hg hg1 ht ht1 hr hr1 => ?_)
  · obtain ⟨hw2, -, hB, hmono⟩ := hbase gamma theta rho hg hg1 ht ht1 hr hr1
    exact ((Nat.cast_mul _ _).trans_le (le_pow_mono hw2 (by norm_num) (const_mul_le_pow (j := 2)
      hw2 (Nat.cast_nonneg _) (by norm_num) (Nat.cast_nonneg _) hB))).trans
      (hmono (2 ^ 15) (by norm_num))
  · obtain ⟨hw2, hri, hB, hmono⟩ := hbase gamma theta rho hg hg1 ht ht1 hr hr1
    have hq := section16BaseFamilyBound_pos gamma theta
    exact inv_le_of_inv_le₀ (cubicBaseExponent_pos hq hr) ((cubicBaseExponent_inv_le hw2 hq hB hr
      hri).trans ((pow_le_pow_right₀ (one_le_two.trans hw2) (by norm_num)).trans (hmono _ le_rfl)))

/-- The class degree in dimension `l` under the Fejér θ₁. -/
def uDeg23 (l : Nat) : Nat := 2 ^ (23 * 2 ^ l)

end LeanProofs.GowersSzemeredi
