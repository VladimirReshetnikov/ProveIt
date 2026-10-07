import GowersSzemeredi.Proofs16ZeroDimensionalFaces

/-! The zero-dimensional case of the relation induction. A relation over the
single empty tuple is covered by one constant graph for each of its values.
No product-property or large-modulus hypothesis is needed in this dimension. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem multipleQ_rpow_ge_parameter (k : Nat) {gamma theta r : Real}
    (hg : 0 < gamma) (hg1 : gamma ≤ 1) (ht : 0 < theta) (ht1 : theta ≤ 1)
    (hr : 1 ≤ r) : r ≤ (multipleQ (r⁻¹ * theta) gamma k) ^ r := by
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hb : 0 < gamma * (r⁻¹ * theta) := by positivity
  have hbr : gamma * (r⁻¹ * theta) ≤ r⁻¹ := by
    calc
      _ ≤ 1 * (r⁻¹ * 1) := mul_le_mul hg1
        (mul_le_mul_of_nonneg_left ht1 (inv_nonneg.mpr hr0.le))
        (by positivity) (by norm_num)
      _ = r⁻¹ := by ring
  have hb1 : gamma * (r⁻¹ * theta) ≤ 1 :=
    hbr.trans (inv_le_one_of_one_le₀ hr)
  have hc : 0 < multipleC (r⁻¹ * theta) gamma k := pow_pos hb _
  have hcr : multipleC (r⁻¹ * theta) gamma k ≤ r⁻¹ := by
    exact (pow_le_of_le_one hb.le hb1 (by positivity)).trans hbr
  have hq : r ≤ multipleQ (r⁻¹ * theta) gamma k := by
    simpa only [inv_inv, multipleQ] using inv_anti₀ hc hcr
  exact hq.trans (Real.self_le_rpow_of_one_le (hr.trans hq) hr)

theorem multiplyLinear_relation_dimension_zero {N : Nat} [NeZero N]
    (Gamma : Finset (Point N 0 × ZMod N)) {gamma r : Real}
    (hg : 0 < gamma) (hg1 : gamma ≤ 1) (hr : 1 ≤ r)
    (hcard : (Gamma.card : Real) ≤ r) : MultiplyLinear gamma r Gamma := by
  classical
  let e : Fin Gamma.card ≃ {z // z ∈ Gamma} := Gamma.equivFin.symm
  intro theta ht ht1 P hP
  have hc : 0 < multipleC (r⁻¹ * theta) gamma 0 := pow_pos (by positivity) _
  have ha : 0 < (multipleC (r⁻¹ * theta) gamma 0) ^ r :=
    Real.rpow_pos_of_pos hc _
  refine ⟨1, Gamma.card, P.carrier, fun _ => P,
    fun _ i _ => (e i).val.2, Finset.Subset.rfl, ?_, ?_, fun _ => hP,
    hcard.trans (multipleQ_rpow_ge_parameter 0 hg hg1 ht ht1 hr), ?_,
    fun _ _ => isMultilinear_dimension_zero _, ?_⟩
  · have hnonneg : (0 : Real) ≤ P.carrier.card := by positivity
    nlinarith
  · constructor
    · intro x
      simp
    · intro i j hij
      exact ((bne_iff_ne.mp hij) (Subsingleton.elim i j)).elim
  · intro j
    have hw : P.width = 0 := by simp [Box.width]
    simp only [hw, Nat.cast_zero, Real.zero_rpow ha.ne', le_refl]
  · intro j x hxQ hxH y hxy
    refine ⟨e.symm ⟨(x, y), hxy⟩, ?_⟩
    simp only [Equiv.apply_symm_apply]

theorem theorem_16_2_zero : Theorem162At 0 := by
  classical
  intro gamma theta hg hg1 ht ht1
  refine ⟨0, ?_⟩
  intro N _ _ hN Gamma hcard hprod
  have hginv : 1 ≤ gamma ^ (-(2 : Int)) := by
    rw [zpow_neg, zpow_ofNat]
    exact (one_le_inv₀ (pow_pos hg 2)).mpr (pow_le_one₀ hg.le hg1)
  have hs : 1 ≤ multipleS theta gamma 0 := one_le_multipleS 0 ht ht1 hg hg1
  have hgr : gamma ^ (-(2 : Int)) ≤
      gamma ^ (-(2 : Int)) * multipleS theta gamma 0 := by
    nlinarith
  refine ⟨Finset.univ, ?_, ?_⟩
  · simp only [pow_zero, mul_one, Finset.card_univ, Fintype.card_pi,
      Fin.prod_univ_zero, Nat.cast_one]
    linarith
  · have hrestriction : restrictRelation Gamma Finset.univ = Gamma := by
      simp only [restrictRelation, Finset.mem_univ, Finset.filter_true]
    rw [hrestriction]
    have hcard' : (Gamma.card : Real) ≤ gamma ^ (-(2 : Int)) := by
      simpa only [pow_zero, mul_one] using hcard
    exact multiplyLinear_relation_dimension_zero Gamma hg hg1 (hginv.trans hgr)
      (hcard'.trans hgr)

end LeanProofs.GowersSzemeredi
