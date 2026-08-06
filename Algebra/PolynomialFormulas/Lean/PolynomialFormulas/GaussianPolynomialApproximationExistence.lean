import PolynomialFormulas.GaussianPolynomialApproximationCore
import PolynomialFormulas.GaussianPolynomialContraction
import PolynomialFormulas.GaussianPolynomialContractionCertificate
import Mathlib.Topology.MetricSpace.Infsep
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Algebra.Polynomial

/-!
# Analytic existence for Gaussian-rational root approximations

This module supplies the non-algorithmic existence arguments needed to prove
that an exhaustive, decidable certificate search eventually succeeds.  The
objects found by that search are still literal Gaussian rationals; density is
used only in the termination proof.
-/

namespace LeanProofs.PolynomialFormulas

open Function Metric Set
open scoped Topology

namespace GaussianRat

/-- Gaussian rationals are dense in the complex numbers under the canonical
embedding `a + bI ↦ a + b Complex.I`. -/
theorem denseRange_toComplex : DenseRange toComplex := by
  rw [Metric.denseRange_iff]
  intro z ε hε
  obtain ⟨a, ha⟩ := Rat.denseRange_cast.exists_dist_lt z.re (half_pos hε)
  obtain ⟨b, hb⟩ := Rat.denseRange_cast.exists_dist_lt z.im (half_pos hε)
  refine ⟨⟨a, b⟩, ?_⟩
  rw [dist_eq_norm]
  calc
    ‖z - toComplex (⟨a, b⟩ : GaussianRat)‖
        ≤ |(z - toComplex (⟨a, b⟩ : GaussianRat)).re| +
            |(z - toComplex (⟨a, b⟩ : GaussianRat)).im| :=
          Complex.norm_le_abs_re_add_abs_im _
    _ = dist z.re (a : ℝ) + dist z.im (b : ℝ) := by
          simp [Real.dist_eq]
    _ < ε / 2 + ε / 2 := add_lt_add ha hb
    _ = ε := by ring

/-- Simultaneous finite-dimensional form of
`GaussianRat.denseRange_toComplex`. -/
theorem denseRange_toComplex_pi (d : ℕ) :
    DenseRange (fun c : Fin d → GaussianRat => fun i => toComplex (c i)) := by
  change DenseRange (Pi.map (fun _ : Fin d => (toComplex : GaussianRat → ℂ)))
  exact DenseRange.piMap (fun _ : Fin d => denseRange_toComplex)

/-- Every finite vector of complex points has a simultaneous
Gaussian-rational approximation with a prescribed positive error. -/
theorem exists_pi_dist_lt {d : ℕ} (z : Fin d → ℂ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ c : Fin d → GaussianRat, ∀ i, dist (z i) (toComplex (c i)) < δ := by
  obtain ⟨c, hc⟩ := (denseRange_toComplex_pi d).exists_dist_lt z hδ
  exact ⟨c, (dist_pi_lt_iff hδ).mp hc⟩

end GaussianRat

namespace GaussianPolynomialApproximationExistence

/-- The Manhattan norm is at most twice the maximum-coordinate norm. -/
theorem l1_le_two_linf (q : GaussianRat) :
    GaussianRat.l1 q ≤ 2 * GaussianRat.linf q := by
  unfold GaussianRat.l1 GaussianRat.linf
  calc
    |q.re| + |q.im| ≤ max |q.re| |q.im| + max |q.re| |q.im| :=
      add_le_add (le_max_left _ _) (le_max_right _ _)
    _ = 2 * max |q.re| |q.im| := by ring

/-- Complex distance between embedded Gaussian rationals is bounded by twice
the exact rational maximum-coordinate distance. -/
theorem dist_toComplex_le_two_linf (q r : GaussianRat) :
    dist (GaussianRat.toComplex q) (GaussianRat.toComplex r) ≤
      (2 * GaussianRat.linf (q - r) : ℚ) := by
  rw [dist_eq_norm, ← GaussianRat.toComplex_sub]
  calc
    ‖GaussianRat.toComplex (q - r)‖ ≤ (GaussianRat.l1 (q - r) : ℝ) :=
      GaussianRat.norm_toComplex_le_l1 _
    _ ≤ (2 * GaussianRat.linf (q - r) : ℚ) := by
      exact_mod_cast l1_le_two_linf (q - r)

/-- An injectively indexed finite family has a positive lower bound on all
distances between differently indexed points.  For an index type with fewer
than two elements the conclusion is vacuous and the bound `1` is used. -/
theorem exists_positive_pairwise_separation {d : ℕ} (z : Fin d → ℂ)
    (hz : Function.Injective z) :
    ∃ η : ℝ, 0 < η ∧ ∀ i j, i ≠ j → η ≤ dist (z i) (z j) := by
  let s : Set ℂ := Set.range z
  have hsfinite : s.Finite := Set.finite_range z
  by_cases hsnontrivial : s.Nontrivial
  · refine ⟨s.infsep, (hsfinite.infsep_pos_iff_nontrivial).mpr hsnontrivial, ?_⟩
    intro i j hij
    exact infsep_le_dist_of_mem ⟨i, rfl⟩ ⟨j, rfl⟩ (hz.ne hij)
  · refine ⟨1, zero_lt_one, ?_⟩
    intro i j hij
    exfalso
    apply hij
    apply hz
    exact (not_nontrivial_iff.mp hsnontrivial) ⟨i, rfl⟩ ⟨j, rfl⟩

/-- Injectively indexed complex points admit arbitrarily accurate
Gaussian-rational centers that remain quantitatively separated. -/
theorem exists_gaussian_centers_close_separated {d : ℕ} (z : Fin d → ℂ)
    (hz : Function.Injective z) {ε : ℝ} (hε : 0 < ε) :
    ∃ (c : Fin d → GaussianRat) (δ : ℝ),
      0 < δ ∧ δ < ε ∧
      (∀ i, dist (z i) (GaussianRat.toComplex (c i)) < δ) ∧
      (∀ i j, i ≠ j → 4 * δ <
        dist (GaussianRat.toComplex (c i)) (GaussianRat.toComplex (c j))) := by
  obtain ⟨η, hη, hsep⟩ := exists_positive_pairwise_separation z hz
  let δ := min (ε / 2) (η / 7)
  have hδ : 0 < δ := lt_min (half_pos hε) (div_pos hη (by norm_num))
  obtain ⟨c, hc⟩ := GaussianRat.exists_pi_dist_lt z (show 0 < δ by exact hδ)
  refine ⟨c, δ, hδ, ?_, hc, ?_⟩
  · exact (min_le_left _ _).trans_lt (half_lt_self hε)
  · intro i j hij
    have hic : dist (GaussianRat.toComplex (c i)) (z i) < δ := by
      simpa [dist_comm] using hc i
    have hjc : dist (z j) (GaussianRat.toComplex (c j)) < δ := hc j
    have hroot : η ≤ dist (z i) (z j) := hsep i j hij
    have hηδ : 7 * δ ≤ η := by
      dsimp [δ]
      have := min_le_right (ε / 2) (η / 7)
      linarith
    have htriangle :
        dist (z i) (z j) ≤
          dist (z i) (GaussianRat.toComplex (c i)) +
          dist (GaussianRat.toComplex (c i)) (GaussianRat.toComplex (c j)) +
          dist (GaussianRat.toComplex (c j)) (z j) :=
      dist_triangle4 _ _ _ _
    have hi' : dist (z i) (GaussianRat.toComplex (c i)) < δ := hc i
    have hj' : dist (GaussianRat.toComplex (c j)) (z j) < δ := by
      simpa [dist_comm] using hc j
    linarith

/-- Density can meet finitely many local conditions simultaneously, while
keeping the chosen Gaussian-rational centers close to their prescribed points
and quantitatively separated.  The local conditions only need to hold in a
neighborhood of each prescribed point.

This is the general termination lemma used for certificate predicates: once
certificate validity is shown to hold throughout a neighborhood of every
simple root, an exhaustive enumeration of Gaussian-rational centers must find
a valid separated tuple. -/
theorem exists_gaussian_centers_of_eventually {d : ℕ} (z : Fin d → ℂ)
    (hz : Function.Injective z) (P : Fin d → ℂ → Prop)
    (hP : ∀ i, ∀ᶠ w in 𝓝 (z i), P i w) {ε : ℝ} (hε : 0 < ε) :
    ∃ (c : Fin d → GaussianRat) (δ : ℝ),
      0 < δ ∧ δ < ε ∧
      (∀ i, dist (z i) (GaussianRat.toComplex (c i)) < δ) ∧
      (∀ i, P i (GaussianRat.toComplex (c i))) ∧
      (∀ i j, i ≠ j → 4 * δ <
        dist (GaussianRat.toComplex (c i)) (GaussianRat.toComplex (c j))) := by
  obtain ⟨η, hη, hsep⟩ := exists_positive_pairwise_separation z hz
  let δ := min (ε / 2) (η / 7)
  have hδ : 0 < δ := lt_min (half_pos hε) (div_pos hη (by norm_num))
  have hex : ∀ i, ∃ q : GaussianRat,
      dist (z i) (GaussianRat.toComplex q) < δ ∧
      P i (GaussianRat.toComplex q) := by
    intro i
    obtain ⟨r, hr, hrP⟩ := Metric.mem_nhds_iff.mp (hP i)
    have hmin : 0 < min δ r := lt_min hδ hr
    obtain ⟨q, hq⟩ := GaussianRat.denseRange_toComplex.exists_dist_lt (z i) hmin
    refine ⟨q, hq.trans_le (min_le_left _ _), hrP ?_⟩
    exact Metric.mem_ball.mpr (by
      simpa [dist_comm] using hq.trans_le (min_le_right _ _))
  choose c hcclose hcP using hex
  refine ⟨c, δ, hδ, (min_le_left _ _).trans_lt (half_lt_self hε), hcclose, hcP, ?_⟩
  intro i j hij
  have hroot : η ≤ dist (z i) (z j) := hsep i j hij
  have hηδ : 7 * δ ≤ η := by
    dsimp [δ]
    have hmin := min_le_right (ε / 2) (η / 7)
    linarith
  have htriangle :
      dist (z i) (z j) ≤
        dist (z i) (GaussianRat.toComplex (c i)) +
        dist (GaussianRat.toComplex (c i)) (GaussianRat.toComplex (c j)) +
        dist (GaussianRat.toComplex (c j)) (z j) :=
    dist_triangle4 _ _ _ _
  have hi' := hcclose i
  have hj' : dist (GaussianRat.toComplex (c j)) (z j) < δ := by
    simpa [dist_comm] using hcclose j
  linarith

/-- Parameterized version of `exists_gaussian_centers_of_eventually`.  The
local property may depend on the common accuracy/separation scale, provided it
holds near each prescribed point for every positive scale. -/
theorem exists_gaussian_centers_of_eventually_param {d : ℕ} (z : Fin d → ℂ)
    (hz : Function.Injective z) (P : Fin d → ℝ → ℂ → Prop)
    (hP : ∀ i δ, 0 < δ → ∀ᶠ w in 𝓝 (z i), P i δ w)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (c : Fin d → GaussianRat) (δ : ℝ),
      0 < δ ∧ δ < ε ∧
      (∀ i, dist (z i) (GaussianRat.toComplex (c i)) < δ) ∧
      (∀ i, P i δ (GaussianRat.toComplex (c i))) ∧
      (∀ i j, i ≠ j → 4 * δ <
        dist (GaussianRat.toComplex (c i)) (GaussianRat.toComplex (c j))) := by
  obtain ⟨η, hη, hsep⟩ := exists_positive_pairwise_separation z hz
  let δ := min (ε / 2) (η / 7)
  have hδ : 0 < δ := lt_min (half_pos hε) (div_pos hη (by norm_num))
  have hex : ∀ i, ∃ q : GaussianRat,
      dist (z i) (GaussianRat.toComplex q) < δ ∧
      P i δ (GaussianRat.toComplex q) := by
    intro i
    obtain ⟨r, hr, hrP⟩ := Metric.mem_nhds_iff.mp (hP i δ hδ)
    have hmin : 0 < min δ r := lt_min hδ hr
    obtain ⟨q, hq⟩ := GaussianRat.denseRange_toComplex.exists_dist_lt (z i) hmin
    refine ⟨q, hq.trans_le (min_le_left _ _), hrP ?_⟩
    exact Metric.mem_ball.mpr (by
      simpa [dist_comm] using hq.trans_le (min_le_right _ _))
  choose c hcclose hcP using hex
  refine ⟨c, δ, hδ, (min_le_left _ _).trans_lt (half_lt_self hε), hcclose, hcP, ?_⟩
  intro i j hij
  have hroot : η ≤ dist (z i) (z j) := hsep i j hij
  have hηδ : 7 * δ ≤ η := by
    dsimp [δ]
    have hmin := min_le_right (ε / 2) (η / 7)
    linarith
  have htriangle :
      dist (z i) (z j) ≤
        dist (z i) (GaussianRat.toComplex (c i)) +
        dist (GaussianRat.toComplex (c i)) (GaussianRat.toComplex (c j)) +
        dist (GaussianRat.toComplex (c j)) (z j) :=
    dist_triangle4 _ _ _ _
  have hi' := hcclose i
  have hj' : dist (GaussianRat.toComplex (c j)) (z j) < δ := by
    simpa [dist_comm] using hcclose j
  linarith

/-- Strong Euclidean separation plus radii below the common scale implies the
exact rational `linf` separation test used by the executable search. -/
theorem radii_linf_separated_of_close {d : ℕ} (c : Fin d → GaussianRat)
    (r : Fin d → ℚ) {δ : ℝ}
    (hr : ∀ i, (r i : ℝ) < δ)
    (hsep : ∀ i j, i ≠ j → 4 * δ <
      dist (GaussianRat.toComplex (c i)) (GaussianRat.toComplex (c j))) :
    ∀ i j, i ≠ j → r i + r j < GaussianRat.linf (c i - c j) := by
  intro i j hij
  have hrij : ((r i + r j : ℚ) : ℝ) < 2 * δ := by
    push_cast
    linarith [hr i, hr j]
  have hdist := hsep i j hij
  have hupper := dist_toComplex_le_two_linf (c i) (c j)
  have hreal : ((r i + r j : ℚ) : ℝ) < (GaussianRat.linf (c i - c j) : ℝ) := by
    push_cast at hupper
    linarith
  exact_mod_cast hreal

/-! ## Local validity near a simple root -/

open GaussianPolynomialApproximationCore
open GaussianPolynomialApproximationCore.QPoly
open GaussianPolynomialContractionCertificate

noncomputable section

/-- Semantic complex extension of a shifted coefficient. -/
def shiftedCoeffComplex (p : QPoly4) (c : ℂ) (i : Fin 5) : ℂ :=
  (Polynomial.taylor c (toComplexPolynomial p)).coeff i

def linearCoeffComplex (p : QPoly4) (c : ℂ) : ℂ :=
  shiftedCoeffComplex p c 1

def normalizedCoeffComplex (p : QPoly4) (c : ℂ) (i : Fin 5) : ℂ :=
  shiftedCoeffComplex p c i / linearCoeffComplex p c

/-- Manhattan norm on semantic complex values. -/
def complexL1 (z : ℂ) : ℝ := |z.re| + |z.im|

def displacementL1Complex (p : QPoly4) (c : ℂ) : ℝ :=
  complexL1 (normalizedCoeffComplex p c 0)

def newtonRadiusComplex (p : QPoly4) (c : ℂ) : ℝ :=
  2 * displacementL1Complex p c

def contractionL1Complex (p : QPoly4) (c : ℂ) (r : ℝ) : ℝ :=
  2 * complexL1 (normalizedCoeffComplex p c 2) * r +
  3 * complexL1 (normalizedCoeffComplex p c 3) * r ^ 2 +
  4 * complexL1 (normalizedCoeffComplex p c 4) * r ^ 3

/-- Semantic real-valued extension of the rational auto-validity bound. -/
def autoBoundComplex (p : QPoly4) (c : ℂ) : ℝ :=
  2 * contractionL1Complex p c (newtonRadiusComplex p c)

theorem shiftedCoeffComplex_toComplex (p : QPoly4) (c : GaussianRat) (i : Fin 5) :
    shiftedCoeffComplex p (GaussianRat.toComplex c) i =
      GaussianRat.toComplex (shiftedCoeff p c i) := by
  calc
    shiftedCoeffComplex p (GaussianRat.toComplex c) i =
        (Polynomial.taylor (GaussianRat.toComplex c)
          ((toPolynomial p).map GaussianRat.toComplex.toRingHom)).coeff i := by
      rw [shiftedCoeffComplex, toComplexPolynomial_eq_map]
    _ = ((Polynomial.taylor c (toPolynomial p)).map
          GaussianRat.toComplex.toRingHom).coeff i := by
      rw [Polynomial.map_taylor]
      rfl
    _ = GaussianRat.toComplex ((Polynomial.taylor c (toPolynomial p)).coeff i) := by
      rw [Polynomial.coeff_map]
      rfl
    _ = GaussianRat.toComplex (shiftedCoeff p c i) := by
      apply congrArg GaussianRat.toComplex
      calc
        (Polynomial.taylor c (toPolynomial p)).coeff i =
            (toPolynomial (translate c p)).coeff i := by
          rw [toPolynomial_translate]
        _ = (translate c p) i := coeff_apply _ _
        _ = shiftedCoeff p c i := rfl

theorem linearCoeffComplex_toComplex (p : QPoly4) (c : GaussianRat) :
    linearCoeffComplex p (GaussianRat.toComplex c) =
      GaussianRat.toComplex (linearCoeff p c) :=
  shiftedCoeffComplex_toComplex p c 1

theorem normalizedCoeffComplex_toComplex (p : QPoly4) (c : GaussianRat) (i : Fin 5) :
    normalizedCoeffComplex p (GaussianRat.toComplex c) i =
      GaussianRat.toComplex (normalizedCoeff p c i) := by
  simp [normalizedCoeffComplex, normalizedCoeff,
    shiftedCoeffComplex_toComplex, linearCoeffComplex_toComplex]

theorem complexL1_toComplex (q : GaussianRat) :
    complexL1 (GaussianRat.toComplex q) = (GaussianRat.l1 q : ℝ) := by
  simp [complexL1, GaussianRat.l1, Rat.cast_add, Rat.cast_abs]

theorem displacementL1Complex_toComplex (p : QPoly4) (c : GaussianRat) :
    displacementL1Complex p (GaussianRat.toComplex c) = (displacementL1 p c : ℝ) := by
  simp [displacementL1Complex, displacementL1,
    normalizedCoeffComplex_toComplex, complexL1_toComplex]

theorem newtonRadiusComplex_toComplex (p : QPoly4) (c : GaussianRat) :
    newtonRadiusComplex p (GaussianRat.toComplex c) = (newtonRadius p c : ℝ) := by
  simp [newtonRadiusComplex, newtonRadius, displacementL1Complex_toComplex]

theorem contractionL1Complex_toComplex (p : QPoly4) (c : GaussianRat) (r : ℚ) :
    contractionL1Complex p (GaussianRat.toComplex c) r = (contractionL1 p c r : ℝ) := by
  simp [contractionL1Complex, contractionL1, normalizedCoeffComplex_toComplex,
    complexL1_toComplex]

theorem autoBoundComplex_toComplex (p : QPoly4) (c : GaussianRat) :
    autoBoundComplex p (GaussianRat.toComplex c) =
      (2 * contractionL1 p c (newtonRadius p c) : ℚ) := by
  rw [autoBoundComplex, newtonRadiusComplex_toComplex]
  simp [contractionL1Complex_toComplex]

theorem continuous_shiftedCoeffComplex (p : QPoly4) (i : Fin 5) :
    Continuous (fun c => shiftedCoeffComplex p c i) := by
  simp only [shiftedCoeffComplex, Polynomial.taylor_coeff]
  exact ((toComplexPolynomial p).hasseDeriv i).continuous

theorem continuous_linearCoeffComplex (p : QPoly4) :
    Continuous (linearCoeffComplex p) :=
  continuous_shiftedCoeffComplex p 1

theorem continuous_complexL1 : Continuous complexL1 := by
  unfold complexL1
  fun_prop

theorem continuousAt_normalizedCoeffComplex (p : QPoly4) (i : Fin 5) {z : ℂ}
    (hlinear : linearCoeffComplex p z ≠ 0) :
    ContinuousAt (fun c => normalizedCoeffComplex p c i) z := by
  unfold normalizedCoeffComplex
  exact (continuous_shiftedCoeffComplex p i).continuousAt.div
    (continuous_linearCoeffComplex p).continuousAt hlinear

theorem continuousAt_displacementL1Complex (p : QPoly4) {z : ℂ}
    (hlinear : linearCoeffComplex p z ≠ 0) :
    ContinuousAt (displacementL1Complex p) z := by
  unfold displacementL1Complex
  exact continuous_complexL1.continuousAt.comp
    (continuousAt_normalizedCoeffComplex p 0 hlinear)

theorem continuousAt_newtonRadiusComplex (p : QPoly4) {z : ℂ}
    (hlinear : linearCoeffComplex p z ≠ 0) :
    ContinuousAt (newtonRadiusComplex p) z := by
  unfold newtonRadiusComplex
  exact continuousAt_const.mul (continuousAt_displacementL1Complex p hlinear)

theorem continuousAt_contractionL1Complex_comp_radius (p : QPoly4) {z : ℂ}
    (hlinear : linearCoeffComplex p z ≠ 0) :
    ContinuousAt (fun c => contractionL1Complex p c (newtonRadiusComplex p c)) z := by
  unfold contractionL1Complex
  have hnorm (i : Fin 5) :
      ContinuousAt (fun c => complexL1 (normalizedCoeffComplex p c i)) z :=
    continuous_complexL1.continuousAt.comp
      (continuousAt_normalizedCoeffComplex p i hlinear)
  have hr := continuousAt_newtonRadiusComplex p hlinear
  exact
    (((continuousAt_const.mul (hnorm 2)).mul hr).add
      ((continuousAt_const.mul (hnorm 3)).mul (hr.pow 2))).add
        ((continuousAt_const.mul (hnorm 4)).mul (hr.pow 3))

theorem continuousAt_autoBoundComplex (p : QPoly4) {z : ℂ}
    (hlinear : linearCoeffComplex p z ≠ 0) :
    ContinuousAt (autoBoundComplex p) z := by
  unfold autoBoundComplex
  exact continuousAt_const.mul
    (continuousAt_contractionL1Complex_comp_radius p hlinear)

theorem shiftedCoeffComplex_zero (p : QPoly4) (z : ℂ) :
    shiftedCoeffComplex p z 0 = evalComplex p z := by
  simp [shiftedCoeffComplex, evalComplex_eq_toComplexPolynomial_eval]

theorem linearCoeffComplex_eq_derivative_eval (p : QPoly4) (z : ℂ) :
    linearCoeffComplex p z = (toComplexPolynomial p).derivative.eval z := by
  simp [linearCoeffComplex, shiftedCoeffComplex]

theorem linearCoeffComplex_ne_zero_of_root (p : QPoly4)
    (hsep : (toPolynomial p).Separable) {z : ℂ} (hz : evalComplex p z = 0) :
    linearCoeffComplex p z ≠ 0 := by
  rw [linearCoeffComplex_eq_derivative_eval]
  have hsepC : (toComplexPolynomial p).Separable := by
    rw [toComplexPolynomial_eq_map]
    exact hsep.map
  exact hsepC.eval₂_derivative_ne_zero (RingHom.id ℂ) (by
    simpa [evalComplex_eq_toComplexPolynomial_eval] using hz)

theorem normalizedCoeffComplex_zero_at_root (p : QPoly4) {z : ℂ}
    (hz : evalComplex p z = 0) : normalizedCoeffComplex p z 0 = 0 := by
  simp [normalizedCoeffComplex, shiftedCoeffComplex_zero, hz]

theorem displacementL1Complex_eq_zero_at_root (p : QPoly4) {z : ℂ}
    (hz : evalComplex p z = 0) : displacementL1Complex p z = 0 := by
  simp [displacementL1Complex, normalizedCoeffComplex_zero_at_root p hz, complexL1]

theorem newtonRadiusComplex_eq_zero_at_root (p : QPoly4) {z : ℂ}
    (hz : evalComplex p z = 0) : newtonRadiusComplex p z = 0 := by
  simp [newtonRadiusComplex, displacementL1Complex_eq_zero_at_root p hz]

theorem autoBoundComplex_eq_zero_at_root (p : QPoly4) {z : ℂ}
    (hz : evalComplex p z = 0) : autoBoundComplex p z = 0 := by
  simp [autoBoundComplex, contractionL1Complex,
    newtonRadiusComplex_eq_zero_at_root p hz]

/-- Auto-validity, together with an arbitrarily small automatic radius, holds
throughout a neighborhood of every simple root. -/
theorem eventually_local_autoValid (p : QPoly4)
    (hsep : (toPolynomial p).Separable) {z : ℂ} (hz : evalComplex p z = 0)
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ w in 𝓝 z,
      linearCoeffComplex p w ≠ 0 ∧
      autoBoundComplex p w < 1 ∧
      newtonRadiusComplex p w < δ := by
  have hlinear : linearCoeffComplex p z ≠ 0 :=
    linearCoeffComplex_ne_zero_of_root p hsep hz
  have hevLinear : ∀ᶠ w in 𝓝 z, linearCoeffComplex p w ≠ 0 :=
    (continuous_linearCoeffComplex p).continuousAt.eventually_ne hlinear
  have hevBound : ∀ᶠ w in 𝓝 z, autoBoundComplex p w < 1 :=
    (continuousAt_autoBoundComplex p hlinear).tendsto.eventually_lt_const (by
      rw [autoBoundComplex_eq_zero_at_root p hz]
      norm_num)
  have hevRadius : ∀ᶠ w in 𝓝 z, newtonRadiusComplex p w < δ :=
    (continuousAt_newtonRadiusComplex p hlinear).tendsto.eventually_lt_const (by
      rw [newtonRadiusComplex_eq_zero_at_root p hz]
      exact hδ)
  filter_upwards [hevLinear, hevBound, hevRadius] with w hwlin hwbound hwradius
  exact ⟨hwlin, hwbound, hwradius⟩

/-- A finite vector of distinct simple roots admits Gaussian-rational centers
with executable auto-valid certificates, arbitrarily small radii, prescribed
accuracy, and the exact rational pairwise-separation inequality used by the
search. -/
theorem exists_autoValid_centers_for_root_vector {d : ℕ} (p : QPoly4)
    (hsep : (toPolynomial p).Separable) (z : Fin d → ℂ)
    (hzinj : Function.Injective z) (hzroot : ∀ i, evalComplex p (z i) = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (c : Fin d → GaussianRat) (δ : ℝ),
      0 < δ ∧ δ < ε ∧
      (∀ i, dist (z i) (GaussianRat.toComplex (c i)) < δ) ∧
      (∀ i, AutoValid p (c i)) ∧
      (∀ i, (newtonRadius p (c i) : ℝ) < δ) ∧
      (∀ i j, i ≠ j →
        newtonRadius p (c i) + newtonRadius p (c j) <
          GaussianRat.linf (c i - c j)) := by
  let Local : Fin d → ℝ → ℂ → Prop := fun _ δ w =>
    linearCoeffComplex p w ≠ 0 ∧
    autoBoundComplex p w < 1 ∧
    newtonRadiusComplex p w < δ
  have hLocal : ∀ i δ, 0 < δ → ∀ᶠ w in 𝓝 (z i), Local i δ w := by
    intro i δ hδ
    exact eventually_local_autoValid p hsep (hzroot i) δ hδ
  obtain ⟨c, δ, hδ, hδε, hclose, hlocal, hsepCenters⟩ :=
    exists_gaussian_centers_of_eventually_param z hzinj Local hLocal hε
  have hauto : ∀ i, AutoValid p (c i) := by
    intro i
    have hi := hlocal i
    refine ⟨?_, ?_⟩
    · intro hzero
      apply hi.1
      rw [linearCoeffComplex_toComplex, hzero]
      exact GaussianRat.toComplex_zero
    · have hbound : (2 * contractionL1 p (c i) (newtonRadius p (c i)) : ℚ) < 1 := by
        have hb := hi.2.1
        rw [autoBoundComplex_toComplex] at hb
        exact_mod_cast hb
      exact hbound.le
  have hradius : ∀ i, (newtonRadius p (c i) : ℝ) < δ := by
    intro i
    simpa [newtonRadiusComplex_toComplex] using (hlocal i).2.2
  have hlinf := radii_linf_separated_of_close c (fun i => newtonRadius p (c i))
    hradius hsepCenters
  exact ⟨c, δ, hδ, hδε, hclose, hauto, hradius, hlinf⟩

/-- Enumerate all roots of a separable Gaussian-rational bounded polynomial
by `Fin (degree p)`.  Separability makes the enumeration injective. -/
theorem exists_injective_root_vector (p : QPoly4)
    (hsep : (toPolynomial p).Separable) :
    ∃ z : Fin (degree p) → ℂ,
      Function.Injective z ∧ ∀ i, evalComplex p (z i) = 0 := by
  let P : Polynomial ℂ := toComplexPolynomial p
  have hsepC : P.Separable := by
    dsimp [P]
    rw [toComplexPolynomial_eq_map]
    exact hsep.map
  have hdeg : P.natDegree = degree p := by
    dsimp [P]
    rw [toComplexPolynomial_eq_map,
      (toPolynomial p).natDegree_map GaussianRat.toComplex.toRingHom,
      degree_eq_natDegree]
  have hcard : Fintype.card (P.rootSet ℂ) = degree p := by
    rw [← hdeg]
    exact Polynomial.card_rootSet_eq_natDegree hsepC (IsAlgClosed.splits _)
  let e : Fin (degree p) ≃ P.rootSet ℂ :=
    (Fintype.equivFinOfCardEq hcard).symm
  let z : Fin (degree p) → ℂ := fun i => (e i : ℂ)
  refine ⟨z, ?_, ?_⟩
  · exact Subtype.val_injective.comp e.injective
  · intro i
    have hi : (z i) ∈ P.rootSet ℂ := (e i).property
    have hP0 : P ≠ 0 := hsepC.ne_zero
    have hroot := (Polynomial.mem_rootSet_of_ne hP0).mp hi
    dsimp [z, P] at hroot ⊢
    simpa [evalComplex_eq_toComplexPolynomial_eval] using hroot

/-- Caller-facing existence theorem for one separable factor.  It supplies
four stored center slots, with all search conditions proved for the active
slots (`j < degree p`).  Inactive slots are padded by zero.

The requested accuracy is expressed exactly as the search expects it:
`2 * newtonRadius ≤ ε`. -/
theorem exists_padded_autoValid_centers (p : QPoly4)
    (hsep : (toPolynomial p).Separable) {ε : ℚ} (hε : 0 < ε) :
    ∃ c : Fin 4 → GaussianRat,
      (∀ j : Fin 4, (j : ℕ) < degree p → AutoValid p (c j)) ∧
      (∀ j : Fin 4, (j : ℕ) < degree p → 2 * newtonRadius p (c j) ≤ ε) ∧
      (∀ j j' : Fin 4,
        (j : ℕ) < degree p → (j' : ℕ) < degree p → j ≠ j' →
          newtonRadius p (c j) + newtonRadius p (c j') <
            GaussianRat.linf (c j - c j')) := by
  obtain ⟨z, hzinj, hzroot⟩ := exists_injective_root_vector p hsep
  have hεR : 0 < (ε : ℝ) / 2 := half_pos (by exact_mod_cast hε)
  obtain ⟨active, δ, hδ, hδε, _hclose, hauto, hradius, hseparated⟩ :=
    exists_autoValid_centers_for_root_vector p hsep z hzinj hzroot hεR
  let c : Fin 4 → GaussianRat := fun j =>
    if hj : (j : ℕ) < degree p then active ⟨j, hj⟩ else 0
  refine ⟨c, ?_, ?_, ?_⟩
  · intro j hj
    simpa [c, hj] using hauto ⟨j, hj⟩
  · intro j hj
    have hr := hradius ⟨j, hj⟩
    have hreal : ((2 * newtonRadius p (c j) : ℚ) : ℝ) < (ε : ℝ) := by
      simp only [c, dif_pos hj]
      push_cast
      linarith
    exact (by exact_mod_cast hreal.le)
  · intro j j' hj hj' hjne
    have hactiveNe : (⟨j, hj⟩ : Fin (degree p)) ≠ ⟨j', hj'⟩ := by
      intro heq
      apply hjne
      exact Fin.ext (congrArg (fun x : Fin (degree p) => x.val) heq)
    simpa [c, hj, hj'] using hseparated ⟨j, hj⟩ ⟨j', hj'⟩ hactiveNe

end

end GaussianPolynomialApproximationExistence

end LeanProofs.PolynomialFormulas
