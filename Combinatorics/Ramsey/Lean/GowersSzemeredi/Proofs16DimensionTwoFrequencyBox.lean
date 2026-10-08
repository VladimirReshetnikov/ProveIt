import GowersSzemeredi.Proofs16DimensionTwoSharper
import GowersSzemeredi.Proofs16CorollaryFromInduction

/-! Carry the improved dimension-two parameter into the Fourier-frequency
box conclusion of Corollary 16.11. The width and frequency-density exponents
retain the smaller iteration parameter. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem section16DimensionTwoParameter_one_le {theta gamma : Real}
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    1 ≤ section16DimensionTwoParameter theta gamma := by
  have hginv : 1 ≤ gamma ^ (-(2 : Int)) := by
    rw [zpow_neg, zpow_ofNat]
    exact (one_le_inv₀ (pow_pos hg 2)).mpr (pow_le_one₀ hg.le hg1)
  exact one_le_mul_of_one_le_of_one_le hginv
    (one_le_pow₀ (one_le_multipleS 1 ht ht1 hg hg1))

/-- Restrict a partial graph with the improved structural parameter. -/
theorem section16_two_sharper_restrict_function (gamma theta : Real)
    (hg : 0 < gamma) (hg1 : gamma ≤ 1) (ht : 0 < theta) (ht1 : theta ≤ 1) :
    ∃ N0 : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N →
      ∀ (B : Finset (Point N 2)) (phi : Point N 2 → ZMod N),
        HasProductProperty B phi gamma →
        ∃ C : Finset (Point N 2), C ⊆ B ∧
          (B.card : Real) - theta * (N : Real)^2 ≤ C.card ∧
          MultiplyLinearFunction gamma (section16DimensionTwoParameter theta gamma) C phi := by
  obtain ⟨N0, hN0⟩ := theorem_16_2_at_two_sharper gamma theta hg hg1 ht ht1
  refine ⟨N0, ?_⟩
  intro N _ _ hN B phi hprod
  have hginv : 1 ≤ gamma ^ (-(2 : Int)) := by
    rw [zpow_neg, zpow_ofNat]
    exact (one_le_inv₀ (pow_pos hg 2)).mpr (pow_le_one₀ hg.le hg1)
  have hB : (B.card : Real) ≤ (N : Real) ^ 2 := by
    exact_mod_cast (show B.card ≤ N ^ 2 by simpa [Point, ZMod.card] using Finset.card_le_univ B)
  have hgraph : ((partialGraph B phi).card : Real) ≤ gamma ^ (-(2 : Int)) * (N : Real) ^ 2 := by
    rw [partialGraph_card]
    exact hB.trans (le_mul_of_one_le_left (by positivity) hginv)
  obtain ⟨J, hJ, hcover⟩ := hN0 N hN (partialGraph B phi) hgraph (partialGraph_relationProductProperty hprod)
  refine ⟨B ∩ J, Finset.inter_subset_left, ?_, ?_⟩
  · have hsum : ((B ∪ J).card : Real) + (B ∩ J).card = B.card + J.card := by
      exact_mod_cast Finset.card_union_add_card_inter B J
    have hunion : ((B ∪ J).card : Real) ≤ (N : Real) ^ 2 := by
      exact_mod_cast (show (B ∪ J).card ≤ N ^ 2 by
        simpa [Point, ZMod.card] using Finset.card_le_univ (B ∪ J))
    linarith
  · rw [restrictRelation_partialGraph] at hcover
    exact hcover

def section16DimensionTwoCorollaryWidthExponent (alpha : Real) : Real :=
  let r := section16DimensionTwoParameter (alpha / 4) (alpha / 2)
  (multipleC (r⁻¹ * (alpha / 8)) (alpha / 2) 2)^r

theorem section16DimensionTwoCorollaryWidthExponent_pos {alpha : Real}
    (ha : 0 < alpha) : 0 < section16DimensionTwoCorollaryWidthExponent alpha := by
  unfold section16DimensionTwoCorollaryWidthExponent section16DimensionTwoParameter multipleS multipleC
  positivity

/-- Strictly reducing a positive source parameter strictly increases its
width control, even at the endpoints of the density range. -/
theorem multipleCover_width_strictAnti (k : Nat) {gamma theta r s : Real}
    (hg : 0 < gamma) (hg1 : gamma ≤ 1) (ht : 0 < theta) (ht1 : theta ≤ 1)
    (hr : 1 ≤ r) (hrs : r < s) :
    (multipleC (s⁻¹ * theta) gamma k)^s < (multipleC (r⁻¹ * theta) gamma k)^r := by
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hs0 : 0 < s := hr0.trans hrs
  have hbr : 0 < gamma * (r⁻¹ * theta) := by positivity
  have hbs : 0 < gamma * (s⁻¹ * theta) := by positivity
  have hbase : gamma * (s⁻¹ * theta) < gamma * (r⁻¹ * theta) :=
    mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_right (inv_strictAnti₀ hr0 hrs) ht) hg
  have hbr1 : gamma * (r⁻¹ * theta) ≤ 1 := by
    apply mul_le_one₀ hg1 (by positivity)
    exact mul_le_one₀ (inv_le_one_of_one_le₀ hr) ht.le ht1
  have hcr : 0 < multipleC (r⁻¹ * theta) gamma k := pow_pos hbr _
  have hcs : 0 < multipleC (s⁻¹ * theta) gamma k := pow_pos hbs _
  have hcr1 : multipleC (r⁻¹ * theta) gamma k ≤ 1 := pow_le_one₀ hbr.le hbr1
  have hcc : multipleC (s⁻¹ * theta) gamma k < multipleC (r⁻¹ * theta) gamma k :=
    pow_lt_pow_left₀ hbase hbs.le (by positivity)
  exact (Real.rpow_lt_rpow hcs.le hcc hs0).trans_le
    (Real.rpow_le_rpow_of_exponent_ge hcr hcr1 hrs.le)

/-- The sharper structural parameter strictly improves the frequency-box
width exponent, and hence also its displayed relative frequency density. -/
theorem section16_corollary_two_width_lt_sharper {alpha : Real}
    (ha : 0 < alpha) (haHalf : alpha ≤ 1 / 2) :
    section16CorollaryWidthExponent alpha 2 < section16DimensionTwoCorollaryWidthExponent alpha := by
  have hr := section16DimensionTwoParameter_one_le
    (by positivity : 0 < alpha / 4) (by linarith) (by positivity : 0 < alpha / 2) (by linarith)
  have hrs := section16DimensionTwoParameter_lt_source
    (by positivity : 0 < alpha / 4) (by linarith) (by positivity : 0 < alpha / 2) (by linarith)
  rw [section16_corollary_iteration_identity] at hrs
  exact multipleCover_width_strictAnti 2 (by positivity : 0 < alpha / 2) (by linarith)
    (by positivity : 0 < alpha / 8) (by linarith) hr hrs

/-- The improved width exponent is at least the original corollary width. -/
theorem section16_corollary_two_width_le_sharper {alpha : Real}
    (ha : 0 < alpha) (haHalf : alpha ≤ 1 / 2) :
    section16CorollaryWidthExponent alpha 2 ≤ section16DimensionTwoCorollaryWidthExponent alpha := by
  have hr := section16DimensionTwoParameter_one_le
    (by positivity : 0 < alpha / 4) (by linarith) (by positivity : 0 < alpha / 2) (by linarith)
  have hrs := section16DimensionTwoParameter_le_source
    (by positivity : 0 < alpha / 4) (by linarith) (by positivity : 0 < alpha / 2) (by linarith)
  rw [section16_corollary_iteration_identity] at hrs
  exact (multipleCover_controls_mono 2 (by positivity : 0 < alpha / 2) (by linarith)
    (by positivity : 0 < alpha / 8) (by linarith) hr hrs).1

/-- A proper Fourier-frequency box with the improved dimension-two width
and density, constructed unconditionally from degree-three nonuniformity. -/
theorem corollary_16_11_at_two_sharper (alpha : Real) (ha : 0 < alpha) (haHalf : alpha ≤ 1 / 2) :
    ∃ N0 : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N →
      ∀ f : ZMod N → Complex, DiscValued f → ¬ UniformOfDegree f alpha 3 →
        ∃ P : Box N 2, ∃ mu : Point N 2 → ZMod N,
          P.IsProper ∧ IsMultilinear mu ∧
          (N : Real)^section16DimensionTwoCorollaryWidthExponent alpha ≤ P.width ∧
          ((alpha / 8) * section16DimensionTwoCorollaryWidthExponent alpha) * P.carrier.card ≤
            section16LargeMultilinearFrequencyCount f P mu alpha := by
  classical
  obtain ⟨N0, hN0⟩ := section16_two_sharper_restrict_function (alpha / 2) (alpha / 4)
    (by positivity) (by linarith) (by positivity) (by linarith)
  refine ⟨N0, fun N _ _ hN f hf hnot ↦ ?_⟩
  obtain ⟨B, phi, hBmass, hprod, hfreq⟩ := section16_large_frequency_graph
    alpha ha (by linarith) f hf hnot
  obtain ⟨C, hCB, hCmass, hML⟩ := hN0 N hN B phi hprod
  let R : Box N 2 := {
    axis := fun _ ↦ modInterval N 0 N
    commonDiff := 1
    axis_step := fun _ ↦ rfl }
  have hRcarrier : R.carrier = Finset.univ := by
    ext x
    simp [R, Box.carrier, modInterval_zero_modulus_carrier]
  have hRproper : R.IsProper := by
    intro i
    change (modInterval N 0 N).carrier.card = N
    rw [modInterval_zero_modulus_carrier, Finset.card_univ, ZMod.card]
  have hRwidth : R.width = N := by
    apply Nat.le_antisymm
    · exact R.width_le_axis_length ⟨0, by omega⟩
    · exact Box.le_width_of_le_axis R (by omega) (fun _ ↦ le_rfl)
  have hRcard : (R.carrier.card : Real) = (N : Real) ^ 2 := by
    rw [hRcarrier, Finset.card_univ]
    simp [Point, ZMod.card]
  have hCdense : alpha / 4 * R.carrier.card ≤ C.card := by
    rw [hRcard]
    linarith only [hBmass, hCmass]
  obtain ⟨P, A, mu, hP, _, hwidth, hAC, hAP, hAmass, hmu, hagree⟩ :=
    hML.dense_multilinear_box (by positivity : 0 < alpha / 4) (by linarith)
      C phi R hRproper (by rw [hRcarrier]; exact Finset.univ_nonempty)
      (by rw [hRcarrier]; exact Finset.subset_univ _) hCdense
  have hhalf : alpha / 4 / 2 = alpha / 8 := by ring
  rw [hhalf] at hwidth hAmass
  let r := section16DimensionTwoParameter (alpha / 4) (alpha / 2)
  let c := multipleC (r⁻¹ * (alpha / 8)) (alpha / 2) 2
  have hr : 0 < r := by
    dsimp [r, section16DimensionTwoParameter, multipleS]
    positivity
  have hc : 0 < c := multipleC_pos 2
    (mul_pos (inv_pos.mpr hr) (by positivity)) (by positivity)
  have hdensity : (alpha / 8) /
      (multipleQ (r⁻¹ * (alpha / 8)) (alpha / 2) 2) ^ r =
      ((alpha / 8) * section16DimensionTwoCorollaryWidthExponent alpha) := by
    change (alpha / 8) / (c⁻¹) ^ r = (alpha / 8) * c ^ r
    rw [Real.inv_rpow hc.le, div_inv_eq_mul]
  have hlarge : A.card ≤ section16LargeMultilinearFrequencyCount f P mu alpha := by
    unfold section16LargeMultilinearFrequencyCount countWhere
    apply Finset.card_le_card
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨hAP hy, ?_⟩
    rw [← hagree y hy]
    exact hfreq y (hCB (hAC hy))
  refine ⟨P, mu, hP, hmu, ?_, ?_⟩
  · simpa only [hRwidth, section16DimensionTwoCorollaryWidthExponent] using hwidth
  · have hm : ((alpha / 8) * section16DimensionTwoCorollaryWidthExponent alpha) * P.carrier.card ≤ A.card := by
      simpa only [← hdensity] using hAmass
    exact hm.trans (Nat.cast_le.mpr hlarge)

end LeanProofs.GowersSzemeredi
