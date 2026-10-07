import GowersSzemeredi.Proofs16FaceInduction

/-! Increasing the multiple-linearity parameter weakens both quantitative
requirements. This permits a common parameter for faces of different dimensions. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem multipleCover_controls_mono (k : Nat) {gamma theta r s : Real}
    (hg : 0 < gamma) (hg1 : gamma ≤ 1) (ht : 0 < theta) (ht1 : theta ≤ 1)
    (hr : 1 ≤ r) (hrs : r ≤ s) :
    (multipleC (s⁻¹ * theta) gamma k) ^ s ≤ (multipleC (r⁻¹ * theta) gamma k) ^ r ∧
    (multipleQ (r⁻¹ * theta) gamma k) ^ r ≤ (multipleQ (s⁻¹ * theta) gamma k) ^ s := by
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hs0 : 0 < s := hr0.trans_le hrs
  have hbr : 0 < gamma * (r⁻¹ * theta) := by positivity
  have hbs : 0 < gamma * (s⁻¹ * theta) := by positivity
  have hbase : gamma * (s⁻¹ * theta) ≤ gamma * (r⁻¹ * theta) := by
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (inv_anti₀ hr0 hrs) ht.le) hg.le
  have hbr1 : gamma * (r⁻¹ * theta) ≤ 1 := by
    calc
      _ ≤ 1 * (1 * 1) := mul_le_mul hg1
        (mul_le_mul (inv_le_one_of_one_le₀ hr) ht1 ht.le (by norm_num))
        (by positivity) (by norm_num)
      _ = 1 := by norm_num
  have hcr : 0 < multipleC (r⁻¹ * theta) gamma k := pow_pos hbr _
  have hcs : 0 < multipleC (s⁻¹ * theta) gamma k := pow_pos hbs _
  have hcr1 : multipleC (r⁻¹ * theta) gamma k ≤ 1 := pow_le_one₀ hbr.le hbr1
  have hcc : multipleC (s⁻¹ * theta) gamma k ≤ multipleC (r⁻¹ * theta) gamma k := by
    exact pow_le_pow_left₀ hbs.le hbase _
  have hqq : multipleQ (r⁻¹ * theta) gamma k ≤ multipleQ (s⁻¹ * theta) gamma k :=
    inv_anti₀ hcs hcc
  have hqr : 1 ≤ multipleQ (r⁻¹ * theta) gamma k := (one_le_inv₀ hcr).mpr hcr1
  constructor
  · exact (Real.rpow_le_rpow hcs.le hcc hs0.le).trans
      (Real.rpow_le_rpow_of_exponent_ge hcr hcr1 hrs)
  · exact (Real.rpow_le_rpow (by positivity : 0 ≤ multipleQ (r⁻¹ * theta) gamma k) hqq hr0.le).trans
      (Real.rpow_le_rpow_of_exponent_le (hqr.trans hqq) hrs)

theorem MultiplyLinear.mono_parameter {N k : Nat} [NeZero N]
    {Gamma : Finset (Point N k × ZMod N)} {gamma r s : Real}
    (h : MultiplyLinear gamma r Gamma) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (hr : 1 ≤ r) (hrs : r ≤ s) : MultiplyLinear gamma s Gamma := by
  intro theta ht ht1 P hP
  obtain ⟨M, q, H, Q, mu, hH, hHcard, hpart, hproper, hq, hw, hmu, hcover⟩ :=
    h theta ht ht1 P hP
  obtain ⟨hcc, hqq⟩ := multipleCover_controls_mono k hg hg1 ht ht1 hr hrs
  refine ⟨M, q, H, Q, mu, hH, hHcard, hpart, hproper, hq.trans hqq, ?_, hmu, hcover⟩
  intro j
  by_cases hwidth : P.width = 0
  · have hs0 : 0 < s := (zero_lt_one.trans_le hr).trans_le hrs
    have hc : 0 < multipleC (s⁻¹ * theta) gamma k := pow_pos (by positivity) _
    have ha : 0 < (multipleC (s⁻¹ * theta) gamma k) ^ s := Real.rpow_pos_of_pos hc _
    simp only [hwidth, Nat.cast_zero, Real.zero_rpow ha.ne']
    positivity
  · have hp : (1 : Real) ≤ P.width := by exact_mod_cast (show 1 ≤ P.width by omega)
    exact (Real.rpow_le_rpow_of_exponent_le hp hcc).trans (hw j)

theorem MultiplyLinearFunction.mono_parameter {N k : Nat} [NeZero N]
    {B : Finset (Point N k)} {phi : Point N k → ZMod N} {gamma r s : Real}
    (h : MultiplyLinearFunction gamma r B phi) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (hr : 1 ≤ r) (hrs : r ≤ s) : MultiplyLinearFunction gamma s B phi :=
  MultiplyLinear.mono_parameter h hg hg1 hr hrs

theorem multipleS_mono_dimension {theta gamma : Real} {l k : Nat}
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (hlk : l ≤ k) : multipleS theta gamma l ≤ multipleS theta gamma k := by
  have htg : 0 < theta * gamma := mul_pos ht hg
  have htg1 : theta * gamma ≤ 1 := mul_le_one₀ ht1 hg.le hg1
  have hbase : (1 : Real) ≤ 2 / (theta * gamma) := (le_div_iff₀ htg).mpr (by linarith)
  apply pow_le_pow_right₀ hbase
  apply Nat.pow_le_pow_right (by omega : 1 ≤ 2)
  apply Nat.pow_le_pow_right (by omega : 1 ≤ 2)
  omega

theorem one_le_multipleS {theta gamma : Real} (k : Nat)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    1 ≤ multipleS theta gamma k := by
  have htg : 0 < theta * gamma := mul_pos ht hg
  have htg1 : theta * gamma ≤ 1 := mul_le_one₀ ht1 hg.le hg1
  exact one_le_pow₀ ((le_div_iff₀ htg).mpr (by linarith))

end LeanProofs.GowersSzemeredi
