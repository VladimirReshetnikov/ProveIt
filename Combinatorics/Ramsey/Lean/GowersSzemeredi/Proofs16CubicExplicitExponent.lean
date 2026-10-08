import GowersSzemeredi.Proofs16CubicCapBound
import GowersSzemeredi.Proofs16CubicStructuredCover

/-! Remove the rounding threshold from the dimension-two width control.
The remaining logarithm depends only on the outer density parameters, not
on the inner loss. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem lemma9WidthWithExponent_le_one {q k : Nat} {sigma theta gamma a : Real}
    (hs : 0 < sigma) (hs1 : sigma ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ha : 0 < a) (ha1 : a ≤ 1) (hr : 1 ≤ section16Lemma9R theta gamma k) :
    lemma9WidthWithExponent q k sigma theta gamma a ≤ 1 := by
  have hr0 : 0 < section16Lemma9R theta gamma k := lt_of_lt_of_le zero_lt_one hr
  have hb : 0 ≤ gamma * (sigma / (2 * section16Lemma9R theta gamma k)) := by positivity
  have hb1 : gamma * (sigma / (2 * section16Lemma9R theta gamma k)) ≤ 1 := by
    have hsdiv : sigma / (2 * section16Lemma9R theta gamma k) ≤ 1 :=
      (div_le_one (by positivity)).mpr (by linarith)
    exact (mul_le_of_le_one_right hg.le hsdiv).trans hg1
  have hc : 0 ≤ multipleC (sigma / (2 * section16Lemma9R theta gamma k)) gamma (k + 1) := by
    unfold multipleC
    positivity
  have hc1 : multipleC (sigma / (2 * section16Lemma9R theta gamma k)) gamma (k + 1) ≤ 1 :=
    pow_le_one₀ hb hb1
  have hp := Real.rpow_le_one hc hc1 hr0.le
  obtain ⟨he, he1⟩ := section16RecurrenceExponent_pos_le_one k q
  have hae : a * section16RecurrenceExponent k q ≤ 1 :=
    (mul_le_of_le_one_right ha.le he1).trans ha1
  have hmul := mul_le_of_le_one_left (mul_pos ha he).le hp
  unfold lemma9WidthWithExponent
  linarith

def section16CubicTwoPowerExponent (q : Nat) (theta gamma rho : Real) : Real :=
  let Qd := fun _ : Real => ((3 * section16CubicSpectrumCount theta gamma : Nat) : Real)
  let Ed := cubicBaseExponent (section16CubicSpectrumCount theta gamma)
  section16CubicLiftExponent q 1 (rho / 4) theta gamma Qd Ed /
    (4 + Real.log (32 / section16Zeta theta gamma 1))

theorem section16CubicTwoPowerExponent_pos {q : Nat} {theta gamma rho : Real}
    (hq : 0 < q) (ht : 0 < theta) (ht1 : theta ≤ 1)
    (hg : 0 < gamma) (hg1 : gamma ≤ 1) (hrho : 0 < rho) :
    0 < section16CubicTwoPowerExponent q theta gamma rho := by
  obtain ⟨hz, hz1⟩ := section16Zeta_pos_le_half 1 ht ht1 hg hg1
  have hlog : 0 ≤ Real.log (32 / section16Zeta theta gamma 1) :=
    Real.log_nonneg ((one_le_div hz).mpr (by linarith))
  apply div_pos
  · exact section16CubicLiftExponent_pos hq (by decide) (by positivity) ht hg
      (cubicBaseExponent_pos (section16CubicSpectrumCount_pos theta gamma) (by positivity))
  · positivity

/-- The logarithmic denominator is independent of the inner loss rho. -/
theorem section16CubicTwoPowerExponent_le {q : Nat} {theta gamma rho : Real}
    (hq : 0 < q) (ht : 0 < theta) (ht1 : theta ≤ 1)
    (hg : 0 < gamma) (hg1 : gamma ≤ 1) (hrho : 0 < rho) (hrho1 : rho ≤ 1) :
    section16CubicTwoPowerExponent q theta gamma rho ≤ section16CubicTwoExponent q theta gamma rho := by
  let Qd := fun _ : Real => ((3 * section16CubicSpectrumCount theta gamma : Nat) : Real)
  let Ed := cubicBaseExponent (section16CubicSpectrumCount theta gamma)
  let e := lemma9WidthWithExponent ⌈Qd (rho / 4 / 2)⌉₊ 1 (rho / 4) theta gamma (Ed (rho / 4 / 2))
  let a := cubicBaseExponent (section16UniformSampleCount (rho / 4) theta gamma 1 * q) (rho / 4)
  have hspec := section16CubicSpectrumCount_pos theta gamma
  have hsample := Nat.mul_pos
    (section16UniformSampleCount_pos (theta := theta) (gamma := gamma) 1 (by positivity : 0 < rho / 4)) hq
  have hEd : 0 < Ed (rho / 4 / 2) := cubicBaseExponent_pos hspec (by positivity)
  have hEd1 : Ed (rho / 4 / 2) ≤ 1 := cubicBaseExponent_le_one hspec (by positivity) (by linarith)
  have he : 0 < e := lemma9WidthWithExponent_pos (by decide) (by positivity) ht hg hEd _
  have hR : 1 ≤ section16Lemma9R theta gamma 1 := by
    have hh := (section16_face_parameter_lift_reserve 1 ht ht1 hg hg1).1
    norm_num [section16Lemma9R] at hh ⊢
    linarith
  have he1 : e ≤ 1 := lemma9WidthWithExponent_le_one (by positivity) (by linarith) hg hg1 hEd hEd1 hR
  have ha : 0 < a := cubicBaseExponent_pos hsample (by positivity)
  have ha1 : a ≤ 1 := cubicBaseExponent_le_one hsample (by positivity) (by linarith)
  obtain ⟨hz, hz1⟩ := section16Zeta_pos_le_half 1 ht ht1 hg hg1
  have hcap := section16_cubic_capped_exponent_lower
    (by positivity : 0 < section16Zeta theta gamma 1 / 2) (by linarith) he he1 ha ha1
  have hratio : 16 / (section16Zeta theta gamma 1 / 2) = 32 / section16Zeta theta gamma 1 := by ring
  rw [hratio] at hcap
  convert hcap using 1
  · change (e * a / 4) / (4 + Real.log (32 / section16Zeta theta gamma 1)) =
      e * a / (16 + 4 * Real.log (32 / section16Zeta theta gamma 1))
    rw [div_div]
    congr 1
    ring
  · rfl

/-- Every cover with the capped controls also has the simpler width control. -/
theorem MultiplyLinearWith.cubic_two_power_control {N q : Nat} [NeZero N]
    {theta gamma : Real} {Gamma : Finset (Point N 2 × ZMod N)}
    (h : MultiplyLinearWith (section16CubicTwoGraphBound q theta gamma)
      (section16CubicTwoExponent q theta gamma) Gamma)
    (hq : 0 < q) (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    MultiplyLinearWith (section16CubicTwoGraphBound q theta gamma)
      (section16CubicTwoPowerExponent q theta gamma) Gamma := by
  exact h.weaken (fun _ _ _ => le_rfl)
    (fun _ hr _ => section16CubicTwoPowerExponent_pos hq ht ht1 hg hg1 hr)
    (fun _ hr hr1 => section16CubicTwoPowerExponent_le hq ht ht1 hg hg1 hr hr1)

end LeanProofs.GowersSzemeredi
