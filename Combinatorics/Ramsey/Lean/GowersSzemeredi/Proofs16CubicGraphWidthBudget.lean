import GowersSzemeredi.Proofs16CubicSourceWidth

/-! The product of graph count and algebraic width control is at most one.
Thus a lower bound for the width also supplies the required graph budget. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem section16_cubic_scalar_graph_width {M q V sigma e : Real}
    (hM : 0 < M) (hq : 1 ≤ q) (hV : 1 ≤ V)
    (hs : 0 ≤ sigma) (hs1 : sigma ≤ 1) (he1 : e ≤ 1) :
    (9 * M^4 * q^2) * ((e * ((2 : Real)^(-(27 : Real)) * sigma^3 / (M*q)^4) / 4) /
      (10 * V)) ≤ 1 := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hV0 : 0 < V := zero_lt_one.trans_le hV
  have hc : (2 : Real)^(-(27 : Real)) ≤ 1 := by norm_num [Real.rpow_neg, Real.rpow_ofNat]
  have hc0 : 0 ≤ (2 : Real)^(-(27 : Real)) := by positivity
  have hs3 : sigma^3 ≤ 1 := pow_le_one₀ hs hs1
  have hnum : e * (2 : Real)^(-(27 : Real)) * sigma^3 ≤ 1 :=
    mul_le_one₀ (mul_le_one₀ he1 hc0 hc) (pow_nonneg hs 3) hs3
  have hden : 1 ≤ V * q^2 := one_le_mul_of_one_le_of_one_le hV (one_le_pow₀ hq)
  have hid : (9 * M^4 * q^2) * ((e * ((2 : Real)^(-(27 : Real)) * sigma^3 / (M*q)^4) / 4) /
      (10 * V)) = (9 / 40 : Real) * (e * (2 : Real)^(-(27 : Real)) * sigma^3) / (V*q^2) := by
    field_simp
    ring
  rw [hid]
  apply (div_le_one (by positivity)).mpr
  calc
    _ ≤ (9 / 40 : Real) * 1 := mul_le_mul_of_nonneg_left hnum (by norm_num)
    _ ≤ 1 := by norm_num
    _ ≤ _ := hden

theorem section16_cubic_graph_width_budget {theta gamma rho : Real} {q : Nat}
    (hq : 0 < q) (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (hr : 0 < rho) (hr1 : rho ≤ 1) :
    section16CubicTwoGraphBound q theta gamma rho *
      section16CubicTwoAlgebraicExponent q theta gamma rho ≤ 1 := by
  let M := section16UniformSampleCount (rho / 4) theta gamma 1
  let Qd := fun _ : Real => ((3 * section16CubicSpectrumCount theta gamma : Nat) : Real)
  let Ed := cubicBaseExponent (section16CubicSpectrumCount theta gamma)
  let e := lemma9WidthWithExponent ⌈Qd (rho / 4 / 2)⌉₊ 1 (rho / 4) theta gamma (Ed (rho / 4 / 2))
  have hspec := section16CubicSpectrumCount_pos theta gamma
  have hEd : 0 < Ed (rho / 4 / 2) := cubicBaseExponent_pos hspec (by positivity)
  have hEd1 : Ed (rho / 4 / 2) ≤ 1 := cubicBaseExponent_le_one hspec (by positivity) (by linarith)
  have he : 0 < e := lemma9WidthWithExponent_pos (by decide) (by positivity) ht hg hEd _
  have hR : 1 ≤ section16Lemma9R theta gamma 1 := by
    have hh := (section16_face_parameter_lift_reserve 1 ht ht1 hg hg1).1
    norm_num [section16Lemma9R] at hh ⊢
    linarith
  have he1 : e ≤ 1 := lemma9WidthWithExponent_le_one (by positivity) (by linarith) hg hg1 hEd hEd1 hR
  have hM : (0 : Real) < M := by
    exact_mod_cast section16UniformSampleCount_pos
      (theta := theta) (gamma := gamma) 1 (by positivity : 0 < rho / 4)
  have hM1 : (1 : Real) ≤ M := by exact_mod_cast (show 1 ≤ M by exact_mod_cast hM)
  have hq1 : (1 : Real) ≤ q := by exact_mod_cast hq
  have hV := one_le_multipleS 1 ht ht1 hg hg1
  have hgraph : (9 : Real) ≤ 9 * (M : Real)^4 * (q : Real)^2 := by
    have hh := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hM1 (n := 4)) (one_le_pow₀ hq1 (n := 2))
    nlinarith only [hh]
  have hh := section16_cubic_scalar_graph_width hM hq1 hV
    (by positivity : 0 ≤ rho / 4) (by linarith : rho / 4 ≤ 1) he1
  unfold section16CubicTwoGraphBound section16CubicLiftGraphBound
  change max (9 * (M : Real)^4 * (q : Real)^2) 9 * _ ≤ 1
  rw [max_eq_left hgraph]
  convert hh using 1
  simp only [section16CubicTwoAlgebraicExponent, section16CubicLiftExponent,
    cubicBaseExponent, e, Qd, Ed, Nat.cast_mul]
  rfl

end LeanProofs.GowersSzemeredi
