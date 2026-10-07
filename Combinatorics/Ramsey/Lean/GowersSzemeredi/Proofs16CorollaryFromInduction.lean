import GowersSzemeredi.Proofs16FrequencySelection
import GowersSzemeredi.Proofs16DenseMultilinearBox
import GowersSzemeredi.Proofs16FaceInduction
import GowersSzemeredi.Proofs08AffineFrequencyProgression

/-! Corollary 16.11 from the corresponding dimension of Theorem 16.2.
The corrected common exponent is retained exactly; the unproved induction
hypothesis is explicit and is not counted as a companion proof. -/

set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The width exponent before multiplying by the density prefactor in
Corollary 16.11. Keeping it separate improves the stated width. -/
def section16CorollaryWidthExponent (alpha : Real) (k : Nat) : Real :=
  let r := section16CorollaryIteration alpha k
  (multipleC (r⁻¹ * (alpha / 8)) (alpha / 2) k) ^ r

theorem section16_corollary_common_exponent_eq_width (alpha : Real) (k : Nat) :
    section16CorollaryExponent alpha k =
      (alpha / 8) * section16CorollaryWidthExponent alpha k := rfl

theorem section16_corollary_width_exponent_pos {alpha : Real} (ha : 0 < alpha) (k : Nat) :
    0 < section16CorollaryWidthExponent alpha k := by
  unfold section16CorollaryWidthExponent section16CorollaryIteration multipleC multipleS
  positivity

theorem section16_corollary_common_exponent_lt_width {alpha : Real}
    (ha : 0 < alpha) (haHalf : alpha ≤ 1 / 2) (k : Nat) :
    section16CorollaryExponent alpha k < section16CorollaryWidthExponent alpha k := by
  rw [section16_corollary_common_exponent_eq_width]
  exact mul_lt_of_lt_one_left (section16_corollary_width_exponent_pos ha k) (by linarith)

/-- The iteration parameter supplied by Theorem 16.2 at alpha/2 and alpha/4
is exactly the one used in the corrected corollary exponent. -/
theorem section16_corollary_iteration_identity (alpha : Real) (k : Nat) :
    (alpha / 2) ^ (-(2 : Int)) * multipleS (alpha / 4) (alpha / 2) k =
      section16CorollaryIteration alpha k := by
  have h : (alpha / 2) ^ (-(2 : Int)) = 4 * alpha ^ (-(2 : Int)) := by
    simp only [zpow_neg, zpow_ofNat, div_pow, inv_div]
    norm_num [div_eq_mul_inv]
  simp only [section16CorollaryIteration, h]

/-- Prove the entire corollary in a fixed dimension once Theorem 16.2 in
that dimension is supplied. The resulting box is proper, and oddness is
unnecessary beyond the standing prime assumption. -/
theorem corollary_16_11_of_dimension_induction {k : Nat} (hk : 1 ≤ k)
    (hth : Theorem162At k) (alpha : Real) (ha : 0 < alpha) (haHalf : alpha ≤ 1 / 2) :
    ∃ N0 : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N →
      ∀ f : ZMod N → Complex, DiscValued f →
        ¬ UniformOfDegree f alpha (k + 1) →
        ∃ P : Box N k, ∃ mu : Point N k → ZMod N,
          P.IsProper ∧ IsMultilinear mu ∧
          (N : Real) ^ section16CorollaryWidthExponent alpha k ≤ P.width ∧
          section16CorollaryExponent alpha k * P.carrier.card ≤
            section16LargeMultilinearFrequencyCount f P mu alpha := by
  classical
  obtain ⟨N0, hN0⟩ := hth.restrict_function (alpha / 2) (alpha / 4)
    (by positivity) (by linarith) (by positivity) (by linarith)
  refine ⟨N0, fun N _ _ hN f hf hnot ↦ ?_⟩
  obtain ⟨B, phi, hBmass, hprod, hfreq⟩ := section16_large_frequency_graph
    alpha ha (by linarith) f hf hnot
  obtain ⟨C, hCB, hCmass, hML⟩ := hN0 N hN B phi hprod
  rw [section16_corollary_iteration_identity] at hML
  let R : Box N k := {
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
  have hRcard : (R.carrier.card : Real) = (N : Real) ^ k := by
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
  let r := section16CorollaryIteration alpha k
  let c := multipleC (r⁻¹ * (alpha / 8)) (alpha / 2) k
  have hr : 0 < r := by
    dsimp [r, section16CorollaryIteration, multipleS]
    positivity
  have hc : 0 < c := by
    dsimp [c, multipleC]
    positivity
  have hdensity : (alpha / 8) /
      (multipleQ (r⁻¹ * (alpha / 8)) (alpha / 2) k) ^ r =
      section16CorollaryExponent alpha k := by
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
  · simpa only [hRwidth, section16CorollaryWidthExponent] using hwidth
  · have hm : section16CorollaryExponent alpha k * P.carrier.card ≤ A.card := by
      simpa only [← hdensity] using hAmass
    exact hm.trans (Nat.cast_le.mpr hlarge)

/-- The only remaining theorem-level input to Corollary 16.11 is the
higher-dimensional multiple-linearity induction, not an extra box-selection
or quantitative-comparison assumption. -/
theorem corollary_16_11_of_theorem_16_2 (hth : theorem_16_2) : corollary_16_11 := by
  intro k alpha hk ha haHalf
  obtain ⟨N0, hN0⟩ := corollary_16_11_of_dimension_induction hk (hth k) alpha ha haHalf
  refine ⟨N0, fun N _ _ hN _hOdd f hf hnot ↦ ?_⟩
  obtain ⟨P, mu, _, hmu, hwidth, hmass⟩ := hN0 N hN f hf hnot
  refine ⟨P, mu, hmu, ?_, hmass⟩
  have hNreal : (1 : Real) ≤ N := by exact_mod_cast NeZero.pos N
  exact (Real.rpow_le_rpow_of_exponent_le hNreal
    (section16_corollary_common_exponent_lt_width ha haHalf k).le).trans hwidth

end LeanProofs.GowersSzemeredi
