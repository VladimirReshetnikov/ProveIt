import OAI.Combinatorics.Progressions.Geometry.NormalizedTwistUniformBoxHaar

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

theorem exists_normalizedTwist_uniform_ambient_haar_comparison (m : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {X : Type} [Fintype X] [DecidableEq X]
      {J : Fin m → Type} [∀ j, Fintype (J j)]
      (U : ∀ j, Submodule ℝ (J j → ℝ))
      (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
        (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
      [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
      (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)),
      (∀ j, DegreeLE (fun _ => 1) (j.val + 1) (poly j)) →
      (∀ j α, coefficients (poly j) α ∈ U j) →
      ∀ {periodCap coverCap : ℝ} {L : ℝ≥0}
      (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
      {η Q p Rrank : ℝ}, 0 < η → 0 ≤ Q →
      (Fintype.card (Σ j, J j) : ℝ) ≤ Q →
      (L : ℝ) ≤ Real.exp Q → η⁻¹ ≤ Real.exp Q →
      3 * Q + 16 ≤ p → (2 * Q + 2) ^ 4 ≤ p →
      (W.cover : ℝ) ≤ Real.exp p → (W.modulus : ℝ) ≤ Real.exp Q →
      ∀ (N : X → ℕ), (Fintype.card X : ℝ) ≤ p →
      (∀ i, Real.exp ((p + C) ^ C + 3 * Q + 16) ≤ (N i : ℝ)) →
      Real.exp ((p + C) ^ C) ≤ Rrank →
      (∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ)) Rrank (U j) (poly j)) →
      ‖(𝔼 x ∈ integerBox N, W.eval N poly x) -
        (𝔼 x ∈ integerBox N, W.frozenSingleSiteHaarReference U ν
          (fun i => (x i : ZMod W.modulus)) (fun i => (x i : ℝ) / N i))‖ ≤
        2 * η + Real.exp (2 * Q * (2 * Q + 2) ^ 4 - p) +
          (L : ℝ) * Real.exp (-2 * Q) / 2 := by
  obtain ⟨C, hC, hlocal⟩ := exists_normalizedTwist_uniform_progression_haar_comparison m
  refine ⟨C, hC, ?_⟩
  intro X _ _ J _ U ν _ _ poly hp hm periodCap coverCap L W
    η Q p Rrank hη hQ hdim hL hηQ hpQ hfreq hcover hmod N hX hlarge hRrank hrank
  have hp2 : 2 ≤ p := by linarith
  have hpow : 0 ≤ (p + C) ^ C := pow_nonneg (by positivity) _
  have hNloc (i) : Real.exp (3 * Q + 16) ≤ (N i : ℝ) :=
    (Real.exp_le_exp.mpr (by linarith)).trans (hlarge i)
  have hNpos (i) : 0 < (N i : ℝ) := (Real.exp_pos _).trans_le (hNloc i)
  let H (x : X → ℤ) := W.frozenSingleSiteHaarReference U ν
    (fun i => (x i : ZMod W.modulus)) (fun i => (x i : ℝ) / N i)
  obtain ⟨start, length, hpos, hlen, hscale, _, _, hdiam, _, hselect⟩ :=
    exists_correlated_integer_residue_box N W.modulus Q hQ W.modulus_pos hmod hNloc
      (fun x => W.eval N poly x - H x)
  let u (v : X → ℤ) (i : X) : ℤ := (start i : ℤ) + (W.modulus : ℤ) * v i
  let center (i : X) : ℝ := (start i : ℝ) / N i
  let residue (i : X) : ZMod W.modulus := (start i : ZMod W.modulus)
  let F (v : X → ℤ) := W.frozenSpatialEval center poly (u v)
  let H₀ := W.frozenSingleSiteHaarReference U ν residue center
  have hresidue (v) : (fun i => (u v i : ZMod W.modulus)) = residue := by
    funext i
    simp [u, residue]
  have hdist (v) (hv : v ∈ integerBox length) :
      dist (fun i => (u v i : ℝ) / N i) center ≤ Real.exp (-2 * Q) / 4 := by
    apply (dist_pi_le_iff (by positivity)).mpr
    intro i
    simpa only [u, center, Real.dist_eq, Int.cast_add, Int.cast_mul, Int.cast_natCast,
      neg_mul] using hdiam v hv i
  have hFerr (v) (hv : v ∈ integerBox length) :
      ‖W.eval N poly (u v) - F v‖ ≤ (L : ℝ) * (Real.exp (-2 * Q) / 4) :=
    (W.eval_sub_frozenSpatialEval N center poly (u v)).trans
      (mul_le_mul_of_nonneg_left (hdist v hv) L.coe_nonneg)
  have hHerr (v) (hv : v ∈ integerBox length) :
      ‖H (u v) - H₀‖ ≤ (L : ℝ) * (Real.exp (-2 * Q) / 4) := by
    dsimp only [H, H₀]
    rw [hresidue]
    exact ((W.frozenSingleSiteHaarReference_lipschitz U ν residue).norm_sub_le _ _).trans
      (mul_le_mul_of_nonneg_left (hdist v hv) L.coe_nonneg)
  let : ∀ i, NeZero (length i) := fun i => ⟨(hpos i).ne'⟩
  have hmeanerr : ‖(𝔼 v ∈ integerBox length, (W.eval N poly (u v) - H (u v))) -
      (𝔼 v ∈ integerBox length, (F v - H₀))‖ ≤ (L : ℝ) * Real.exp (-2 * Q) / 2 := by
    rw [← Finset.expect_sub_distrib]
    apply (RCLike.norm_expect_le (K := ℂ)).trans
    apply Finset.expect_le (integerBox_nonempty length)
    intro v hv
    have he : W.eval N poly (u v) - H (u v) - (F v - H₀) =
        (W.eval N poly (u v) - F v) - (H (u v) - H₀) := by ring
    rw [he]
    have hh := (norm_sub_le (W.eval N poly (u v) - F v) (H (u v) - H₀)).trans
      (add_le_add (hFerr v hv) (hHerr v hv))
    convert hh using 1; ring
  have hlong (i) : Real.exp ((p + C) ^ C) ≤ (length i : ℝ) := by
    calc
      _ = Real.exp ((p + C) ^ C + 3 * Q + 16) * Real.exp (-(3 * Q + 16)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ (N i : ℝ) * Real.exp (-(3 * Q + 16)) :=
        mul_le_mul_of_nonneg_right (hlarge i) (Real.exp_nonneg _)
      _ ≤ _ := hlen i
  have hzero : translatedIntegerBox (0 : X → ℤ) length = integerBox length := by
    ext v
    simp only [mem_translatedIntegerBox, mem_integerBox, Pi.zero_apply, zero_add]
  have hcomp := hlocal U ν poly hp hm W residue center hη hQ hdim hL hηQ hp2 hfreq hcover
    W.modulus W.modulus_pos (hmod.trans (Real.exp_le_exp.mpr (by linarith)))
    (fun i => (start i : ℤ)) (Real.exp (3 * Q + 16))
    (Real.one_le_exp (by positivity)) (Real.exp_le_exp.mpr hpQ)
    (fun i => (N i : ℝ)) hNpos 0 length hpos hscale hX hlong hRrank hrank
  rw [hzero] at hcomp
  have hF (v) : F v = W.frozenTorus residue center (physicalGridFactorInput W.cover poly
      (fun i => (start i : ℝ) + (W.modulus : ℝ) * (v i : ℝ))) := by
    dsimp only [F, NormalizedPolynomialTwist.frozenSpatialEval]
    rw [hresidue]
    simp only [u, Int.cast_add, Int.cast_mul, Int.cast_natCast]
  simp only [Int.cast_natCast] at hcomp
  simp_rw [← hF] at hcomp
  have hcomp' : ‖𝔼 v ∈ integerBox length, (F v - H₀)‖ ≤
      2 * η + Real.exp (2 * Q * (2 * Q + 2) ^ 4 - p) := by
    rw [Finset.expect_sub_distrib, Finset.expect_const (integerBox_nonempty length)]
    simpa only [Int.cast_natCast] using hcomp
  change ‖(𝔼 x ∈ integerBox N, W.eval N poly x) - 𝔼 x ∈ integerBox N, H x‖ ≤ _
  rw [← Finset.expect_sub_distrib]
  apply hselect.trans
  change ‖𝔼 v ∈ integerBox length, (W.eval N poly (u v) - H (u v))‖ ≤ _
  have ht := norm_le_norm_sub_add
    (𝔼 v ∈ integerBox length, (W.eval N poly (u v) - H (u v)))
    (𝔼 v ∈ integerBox length, (F v - H₀))
  linarith

end Erdos3.VectorPolynomial

end

end OAI
