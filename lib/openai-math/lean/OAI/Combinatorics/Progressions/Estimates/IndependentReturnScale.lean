import OAI.Combinatorics.Progressions.Dynamics.LocalizedAverageScaleBudget
import OAI.Combinatorics.Progressions.Fourier.BohrLocalMomentAlternatives
import OAI.Combinatorics.Progressions.Fourier.BohrMatchingScales

namespace OAI

section

namespace Erdos3

theorem localizedAverageScale_mono_error (rank : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    Monotone (fun epsilon : ℝ => localizedAverageScale rank R epsilon) := by
  intro a b hab
  unfold localizedAverageScale
  apply Real.toNNReal_mono
  exact min_le_min le_rfl (div_le_div_of_nonneg_right hab (by positivity))

theorem localizedAverageScale_exp_lower_of_error (rank : ℕ) {W A E epsilon : ℝ}
    (hW : 0 ≤ W) (hWA : W ≤ Real.exp A) (hA : 0 ≤ A) (hE : 0 ≤ E)
    (hepsilon : Real.exp (-E) / 2 ≤ epsilon) :
    Real.exp (-((rank : ℝ) + A + E + 1600)) ≤ (localizedAverageScale rank W epsilon : ℝ) := by
  apply (localizedAverageScale_exp_lower rank hW hWA hA hE).trans
  exact_mod_cast localizedAverageScale_mono_error rank hW hepsilon

end Erdos3

end

section

namespace Erdos3.CellRefinement

open scoped NNReal

noncomputable def outerMatchingScale (rank : ℕ) (W epsilon : ℝ) (scale : ℝ≥0) : ℝ≥0 :=
  min scale (localizedAverageScale rank W (epsilon / 4))

theorem outerMatchingScale_spec (rank : ℕ) {W epsilon : ℝ} {scale : ℝ≥0}
    (hW : 0 ≤ W) (hepsilon : 0 < epsilon) (hscale : 0 < scale) :
    0 < outerMatchingScale rank W epsilon scale ∧
      outerMatchingScale rank W epsilon scale ≤ scale ∧
      outerMatchingScale rank W epsilon scale ≤ localizedAverageScale rank W (epsilon / 4) := by
  exact ⟨lt_min hscale (localizedAverageScale_spec rank hW (show 0 < epsilon / 4 by positivity)).1,
    min_le_left _ _, min_le_right _ _⟩

noncomputable def outerMatchingScaleLoss (rank : ℕ) (A E T : ℝ) : ℝ :=
  T + rank + A + E + 1602

theorem outerMatchingScaleLoss_nonneg (rank : ℕ) {A E T : ℝ}
    (hA : 0 ≤ A) (hE : 0 ≤ E) (hT : 0 ≤ T) :
    0 ≤ outerMatchingScaleLoss rank A E T := by
  unfold outerMatchingScaleLoss
  positivity

theorem outerMatchingScale_exp_lower (rank : ℕ) {W A E T : ℝ} {scale : ℝ≥0}
    (hW : 0 ≤ W) (hcap : W ≤ Real.exp A) (hA : 0 ≤ A) (hE : 0 ≤ E) (hT : 0 ≤ T)
    (hscale : Real.exp (-T) ≤ (scale : ℝ)) :
    Real.exp (-outerMatchingScaleLoss rank A E T) ≤
      (outerMatchingScale rank W (Real.exp (-E)) scale : ℝ) := by
  have htwo : Real.exp (-2 : ℝ) ≤ 1 / 2 := by
    have h : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp 2]
    simpa only [Real.exp_neg, one_div] using one_div_le_one_div_of_le (by norm_num) h
  have herror : Real.exp (-(E + 2)) / 2 ≤ Real.exp (-E) / 4 := by
    have h := mul_le_mul_of_nonneg_left htwo (Real.exp_nonneg (-E))
    rw [← Real.exp_add] at h
    have heq : -E + -2 = -(E + 2) := by ring
    rw [heq] at h
    linarith
  have hlocal := localizedAverageScale_exp_lower_of_error rank hW hcap hA
    (show 0 ≤ E + 2 by positivity) herror
  change _ ≤ min (scale : ℝ) (localizedAverageScale rank W (Real.exp (-E) / 4) : ℝ)
  apply le_min
  · apply le_trans _ hscale
    apply Real.exp_le_exp.mpr
    unfold outerMatchingScaleLoss
    have hrank : (0 : ℝ) ≤ rank := Nat.cast_nonneg rank
    linarith
  · apply le_trans _ hlocal
    apply Real.exp_le_exp.mpr
    unfold outerMatchingScaleLoss
    linarith

end Erdos3.CellRefinement

end

section

namespace Erdos3.LocalConvolution

open scoped NNReal

noncomputable def controlledLocalMomentScale (rank : ℕ) (M delta : ℝ) : ℝ≥0 :=
  localizedAverageScale rank M (min (delta / 2) (localMomentGain delta) / 3) / 2

noncomputable def localMomentErrorBudget (delta : ℝ) : ℝ :=
  -Real.log (2 * min (delta / 2) (localMomentGain delta) / 3)

theorem controlledLocalMomentScale_spec (rank : ℕ) {M delta : ℝ}
    (hM : 0 ≤ M) (hdelta : 0 < delta) :
    0 < controlledLocalMomentScale rank M delta ∧
      controlledLocalMomentScale rank M delta + controlledLocalMomentScale rank M delta ≤
        1 / (100 * (2 * max rank 1 : ℕ) : ℝ≥0) ∧
      1200 * (max rank 1 : ℕ) *
          ((controlledLocalMomentScale rank M delta + controlledLocalMomentScale rank M delta : ℝ≥0) : ℝ) * M ≤
        min (delta / 2) (localMomentGain delta) := by
  have hc : 0 < min (delta / 2) (localMomentGain delta) :=
    lt_min (by positivity) (localMomentGain_pos delta)
  obtain ⟨hr, hsmall, herror⟩ := localizedAverageScale_spec rank hM
    (show 0 < min (delta / 2) (localMomentGain delta) / 3 by positivity)
  have heq : controlledLocalMomentScale rank M delta + controlledLocalMomentScale rank M delta =
      localizedAverageScale rank M (min (delta / 2) (localMomentGain delta) / 3) := by
    unfold controlledLocalMomentScale
    ring
  refine ⟨div_pos hr (by norm_num), ?_, ?_⟩
  · rwa [heq]
  · rw [heq]
    nlinarith

theorem localMomentErrorBudget_spec {delta : ℝ} (hdelta : 0 < delta) :
    0 ≤ localMomentErrorBudget delta ∧
      Real.exp (-localMomentErrorBudget delta) / 2 = min (delta / 2) (localMomentGain delta) / 3 := by
  have hc : 0 < min (delta / 2) (localMomentGain delta) :=
    lt_min (by positivity) (localMomentGain_pos delta)
  have hc1 : min (delta / 2) (localMomentGain delta) ≤ 1 / 2 :=
    (min_le_right _ _).trans (localMomentGain_le_half delta)
  unfold localMomentErrorBudget
  constructor
  · exact neg_nonneg.mpr (Real.log_nonpos (by positivity) (by linarith))
  · rw [neg_neg, Real.exp_log (by positivity)]
    ring

theorem controlledLocalMomentScale_exp_lower (rank : ℕ) {M delta A : ℝ}
    (hM : 0 ≤ M) (hcap : M ≤ Real.exp A) (hA : 0 ≤ A) (hdelta : 0 < delta) :
    Real.exp (-((rank : ℝ) + A + localMomentErrorBudget delta + 1602)) ≤
      (controlledLocalMomentScale rank M delta : ℝ) := by
  obtain ⟨hE, hEeq⟩ := localMomentErrorBudget_spec hdelta
  have hbase := localizedAverageScale_exp_lower rank hM hcap hA hE
  rw [hEeq] at hbase
  have htwo : Real.exp (-2 : ℝ) ≤ 1 / 2 := by
    have h : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp 2]
    simpa only [Real.exp_neg, one_div] using one_div_le_one_div_of_le (by norm_num) h
  calc
    _ = Real.exp (-((rank : ℝ) + A + localMomentErrorBudget delta + 1600)) * Real.exp (-2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ (localizedAverageScale rank M (min (delta / 2) (localMomentGain delta) / 3) : ℝ) * (1 / 2) :=
      mul_le_mul hbase htwo (Real.exp_nonneg _) (by positivity)
    _ = _ := by
      change _ = (localizedAverageScale rank M (min (delta / 2) (localMomentGain delta) / 3) : ℝ) / 2
      ring

end Erdos3.LocalConvolution

end

section

namespace Erdos3.LocalConvolution

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

theorem normalized_local_alternatives_at_scale
    (L : CyclicBohr.Set N) (hL : L.IsRankRegular)
    (S : Finset (ZMod N)) (hS : S.Nonempty)
    (f g : ZMod N → ℝ) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hfsupport : ∀ x, x ∉ L.carrier → f x = 0)
    (hgsupport : ∀ x, x ∉ L.carrier → g x = 0)
    {u v M delta : ℝ} (hu : 0 < u) (hv : 0 < v) (hM : 0 ≤ M) (hdelta : 0 < delta)
    (hmeanf : (𝔼 x ∈ L.carrier, f x) = u) (hmeang : (𝔼 x ∈ L.carrier, g x) = v)
    (hcapf : ∀ x, f x / u ≤ M) (hcapg : ∀ x, g x / v ≤ M)
    (hSL : S ⊆ (L.ndilate (controlledLocalMomentScale L.rank M delta)).carrier)
    (m : ℕ) (hm : 0 < m) :
    sumLp S (fun x => convolution L.carrier (fun y => f y / u) (fun y => g y / v) x - 1)
        (2 * m) ≤ delta ∨
      ∃ h : ZMod N → ℝ, (h = (fun x => f x / u) ∨ h = (fun x => g x / v)) ∧
        ∃ m' : ℕ, 0 < m' ∧ m ≤ m' ∧ m' ≤ localMomentExponentFactor delta * m ∧
          1 + localMomentGain delta ≤ differenceLp S (correlation L.carrier h h) (2 * m') := by
  have hfnorm := normalized_mass_one L.carrier f hfsupport hu hmeanf
  have hgnorm := normalized_mass_one L.carrier g hgsupport hv hmeang
  have hcard : (L.carrier.card : ℝ) ≠ 0 := by exact_mod_cast L.card_pos.ne'
  have hfsum : (∑ x, f x / u) = L.carrier.card := by
    simpa only [one_mul] using (div_eq_iff hcard).mp hfnorm
  have hgsum : (∑ x, g x / v) = L.carrier.card := by
    simpa only [one_mul] using (div_eq_iff hcard).mp hgnorm
  obtain ⟨_, hsmall, herror⟩ := controlledLocalMomentScale_spec L.rank hM hdelta
  apply local_alternatives_of_regular_bohr L hL S hS hSL hsmall
    (fun x => f x / u) (fun x => g x / v) _ _ hfsum hgsum _ _ hdelta herror hm
  · intro x hx
    rw [hfsupport x hx, zero_div]
  · intro x hx
    rw [hgsupport x hx, zero_div]
  · intro x
    exact (abs_of_nonneg (div_nonneg (hf x) hu.le)).le.trans (hcapf x)
  · intro x
    exact (abs_of_nonneg (div_nonneg (hg x) hv.le)).le.trans (hcapg x)

end Erdos3.LocalConvolution

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators NNReal

noncomputable def independentReturnScale (rank : ℕ) (M epsilon : ℝ) : ℝ≥0 :=
  localizedAverageScale rank M (epsilon / 2) / 2

theorem independentReturnScale_spec (rank : ℕ) {M epsilon : ℝ}
    (hM : 0 ≤ M) (hepsilon : 0 < epsilon) :
    0 < independentReturnScale rank M epsilon ∧
      independentReturnScale rank M epsilon ≤ 1 ∧
      independentReturnScale rank M epsilon + independentReturnScale rank M epsilon ≤
        1 / (100 * (2 * max rank 1 : ℕ) : ℝ≥0) ∧
      M * (400 * (max rank 1 : ℕ) * (independentReturnScale rank M epsilon : ℝ) +
        400 * (max rank 1 : ℕ) *
          ((independentReturnScale rank M epsilon + independentReturnScale rank M epsilon : ℝ≥0) : ℝ)) ≤
        epsilon := by
  obtain ⟨hr, hsmall, herror⟩ := localizedAverageScale_spec rank hM
    (show 0 < epsilon / 2 by positivity)
  have heq : independentReturnScale rank M epsilon + independentReturnScale rank M epsilon =
      localizedAverageScale rank M (epsilon / 2) := by
    unfold independentReturnScale
    ring
  have hone : independentReturnScale rank M epsilon ≤ 1 := by
    change localizedAverageScale rank M (epsilon / 2) / 2 ≤ 1
    exact (div_le_self (by positivity) (by norm_num : (1 : ℝ≥0) ≤ 2)).trans
      (localizedAverageScale_le_one rank hM (show 0 < epsilon / 2 by positivity))
  refine ⟨div_pos hr (by norm_num), hone, ?_, ?_⟩
  · rwa [heq]
  · rw [heq]
    change M * (400 * (max rank 1 : ℕ) *
      ((localizedAverageScale rank M (epsilon / 2) : ℝ) / 2) +
      400 * (max rank 1 : ℕ) * (localizedAverageScale rank M (epsilon / 2) : ℝ)) ≤ epsilon
    nlinarith

theorem independentReturnScale_exp_lower (rank : ℕ) {M A E : ℝ}
    (hM : 0 ≤ M) (hcap : M ≤ Real.exp A) (hA : 0 ≤ A) (hE : 0 ≤ E) :
    Real.exp (-((rank : ℝ) + A + E + 1602)) ≤
      (independentReturnScale rank M (Real.exp (-E)) : ℝ) := by
  have hbase := localizedAverageScale_exp_lower rank hM hcap hA hE
  have htwo : Real.exp (-2 : ℝ) ≤ 1 / 2 := by
    have h : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp 2]
    simpa only [Real.exp_neg, one_div] using one_div_le_one_div_of_le (by norm_num) h
  calc
    _ = Real.exp (-((rank : ℝ) + A + E + 1600)) * Real.exp (-2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ (localizedAverageScale rank M (Real.exp (-E) / 2) : ℝ) * (1 / 2) :=
      mul_le_mul hbase htwo (Real.exp_nonneg _) (by positivity)
    _ = _ := by
      change _ = (localizedAverageScale rank M (Real.exp (-E) / 2) : ℝ) / 2
      ring

variable {N : ℕ} [NeZero N]

theorem bohr_matched_independent_at_return_scale
    (L S : CyclicBohr.Set N) (hL : L.IsRankRegular) (hS : S.IsRankRegular)
    (hfreq : S.frequencies = L.frequencies) (hwidth : S.radius ≤ L.radius)
    (C : Finset (ZMod N)) (hC : C.Nonempty)
    (a f g : ZMod N → ℝ) {M epsilon : ℝ} (hM : 0 ≤ M) (hepsilon : 0 < epsilon)
    (hCS : C ⊆ (S.ndilate (independentReturnScale S.rank M epsilon)).carrier)
    (ha : ∀ x, |a x| ≤ M) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    (hg : ∀ x, 0 ≤ g x ∧ g x ≤ 1) :
    |(𝔼 z ∈ matchedCellSpace L.carrier S.carrier,
        bilinearIntegral (C.image (fun t => z.1 + t))
          (C.image (fun t => (-z.1 + z.2.1 + z.2.2) + t)) a f g) -
      matchedIntegral L.carrier S.carrier a f g| ≤ epsilon := by
  let zeta := independentReturnScale S.rank M epsilon
  have hrank : L.rank = S.rank := (congrArg Finset.card hfreq).symm
  have hSL : (S.ndilate zeta).carrier ⊆ (L.ndilate zeta).carrier := by
    apply CyclicBohr.Set.carrier_mono
    · change L.frequencies ⊆ S.frequencies
      rw [hfreq]
    · simp only [CyclicBohr.Set.radius_ndilate]
      exact mul_le_mul_of_nonneg_left hwidth zeta.coe_nonneg
  obtain ⟨_, _, hsmall, herror⟩ := independentReturnScale_spec S.rank hM hepsilon
  have hell : zeta ≤ 1 / (100 * (2 * max L.rank 1 : ℕ) : ℝ≥0) := by
    rw [hrank]
    exact le_trans le_self_add hsmall
  have h := bohr_matched_independent_integral_error L S hL hS C hC (hCS.trans hSL) hCS
    hell hsmall a f g hM ha hf hg
  rw [hrank] at h
  exact h.trans herror

end Erdos3.CellRefinement

end

end OAI
