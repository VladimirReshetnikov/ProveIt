import GowersSzemeredi.Proofs16CoverParameterMonotonicity

/-! Zero-dimensional partial functions have a single constant graph.
The zero-width convention for boxes causes no loss in this cover. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem isMultilinear_dimension_zero {N : Nat} (phi : Point N 0 → ZMod N) :
    IsMultilinear phi := by
  classical
  let x0 : Point N 0 := fun i => Fin.elim0 i
  refine ⟨fun _ => phi x0, ?_⟩
  intro x
  have hx : x = x0 := Subsingleton.elim _ _
  simp [hx]

theorem multiplyLinearFunction_dimension_zero {N : Nat} [NeZero N]
    (B : Finset (Point N 0)) (phi : Point N 0 → ZMod N) {gamma r : Real}
    (hg : 0 < gamma) (hg1 : gamma ≤ 1) (hr : 1 ≤ r) :
    MultiplyLinearFunction gamma r B phi := by
  classical
  intro theta ht ht1 P hP
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hb : 0 < gamma * (r⁻¹ * theta) := by positivity
  have hb1 : gamma * (r⁻¹ * theta) ≤ 1 := by
    calc
      _ ≤ 1 * (1 * 1) := mul_le_mul hg1
        (mul_le_mul (inv_le_one_of_one_le₀ hr) ht1 ht.le (by norm_num))
        (by positivity) (by norm_num)
      _ = 1 := by norm_num
  have hc : 0 < multipleC (r⁻¹ * theta) gamma 0 := pow_pos hb _
  have hc1 : multipleC (r⁻¹ * theta) gamma 0 ≤ 1 := pow_le_one₀ hb.le hb1
  have ha : 0 < (multipleC (r⁻¹ * theta) gamma 0) ^ r := Real.rpow_pos_of_pos hc _
  refine ⟨1, 1, P.carrier, fun _ => P, fun _ _ => phi,
    Finset.Subset.rfl, ?_, ?_, fun _ => hP, ?_, ?_,
    fun _ _ => isMultilinear_dimension_zero phi, ?_⟩
  · have hcard : (0 : Real) ≤ P.carrier.card := by positivity
    nlinarith
  · constructor
    · intro x
      simp
    · intro i j hij
      exact ((bne_iff_ne.mp hij) (Subsingleton.elim i j)).elim
  · simpa only [Nat.cast_one, multipleQ] using
      Real.one_le_rpow ((one_le_inv₀ hc).mpr hc1) hr0.le
  · intro j
    have hw : P.width = 0 := by simp [Box.width]
    simp only [hw, Nat.cast_zero, Real.zero_rpow ha.ne', le_refl]
  · intro j x hxQ hxH y hxy
    obtain ⟨z, hz, heq⟩ := Finset.mem_image.mp hxy
    have hzx : z = x := congrArg Prod.fst heq
    have hzy : phi z = y := congrArg Prod.snd heq
    exact ⟨0, hzx ▸ hzy.symm⟩

end LeanProofs.GowersSzemeredi
