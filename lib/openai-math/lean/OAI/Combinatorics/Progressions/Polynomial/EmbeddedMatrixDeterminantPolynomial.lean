import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import OAI.Combinatorics.Progressions.Estimates.RectangularCellGeometry
import OAI.Combinatorics.Progressions.Estimates.SymmetricCubeSublevel
import OAI.Combinatorics.Progressions.Estimates.SymmetricCubeVolume
import OAI.Combinatorics.Progressions.Geometry.CoordinateDeterminant
import OAI.Combinatorics.Progressions.Polynomial.PolynomialDilation
import OAI.Combinatorics.Progressions.Polynomial.PolynomialValueCoefficient
import OAI.Combinatorics.Progressions.Probability.FiniteConditionedMass

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem polynomial_det_totalDegree_le {I X : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix I I (MvPolynomial X ℝ)) (d : ℕ)
    (hM : ∀ i j, (M i j).totalDegree ≤ d) :
    M.det.totalDegree ≤ Fintype.card I * d := by
  classical
  rw [Matrix.det_apply']
  apply MvPolynomial.totalDegree_finsetSum_le
  intro σ _
  have hsign : (((Equiv.Perm.sign σ : ℤ) : MvPolynomial X ℝ)) =
      MvPolynomial.C ((Equiv.Perm.sign σ : ℤ) : ℝ) := by simp
  rw [hsign]
  apply (MvPolynomial.totalDegree_mul _ _).trans
  simp only [MvPolynomial.totalDegree_C, zero_add]
  apply (MvPolynomial.totalDegree_finsetProd Finset.univ _).trans
  calc
    _ ≤ ∑ _i : I, d := Finset.sum_le_sum (fun i _ => hM (σ i) i)
    _ = _ := by simp

theorem coordinateMatrixPolynomial_totalDegree {I X : Type*} [Fintype I]
    [DecidableEq I] (index : I → I → X) :
    (coordinateMatrixPolynomial index).det.totalDegree ≤ Fintype.card I := by
  apply (polynomial_det_totalDegree_le _ 1 ?_).trans_eq (Nat.mul_one _)
  intro i j
  simp only [coordinateMatrixPolynomial, MvPolynomial.totalDegree_X, le_refl]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

def unitMvPolynomialSublevel {N : ℕ} (p : MvPolynomial (Fin N) ℝ) (u : ℝ) : Set (Fin N → ℝ) :=
  symmetricUnitBox N ∩ {x | |MvPolynomial.eval x p| ≤ u}

theorem unitMvPolynomialSublevel_measurable {N : ℕ} (p : MvPolynomial (Fin N) ℝ) (u : ℝ) :
    MeasurableSet (unitMvPolynomialSublevel p u) :=
  (MeasurableSet.univ_pi (fun _ => measurableSet_Icc)).inter
    (isClosed_le p.continuous_eval.abs continuous_const).measurableSet

theorem unitMvPolynomialSublevel_volume_ne_top {N : ℕ} (p : MvPolynomial (Fin N) ℝ) (u : ℝ) :
    volume (unitMvPolynomialSublevel p u) ≠ ⊤ := by
  have hbox : volume (symmetricUnitBox N) ≠ ⊤ := by
    rw [symmetricUnitBox, volume_pi_pi]
    exact ENNReal.prod_ne_top (fun _ _ => by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  exact measure_ne_top_of_subset Set.inter_subset_left hbox

noncomputable def multivariateSublevelConstant (N d : ℕ) : ℝ :=
  (2 : ℝ) ^ N * N * univariateSublevelConstant d

theorem multivariateSublevelConstant_pos {N : ℕ} (hN : 0 < N) (d : ℕ) :
    0 < multivariateSublevelConstant N d := by
  unfold multivariateSublevelConstant
  exact mul_pos (mul_pos (by positivity) (by exact_mod_cast hN)) (univariateSublevelConstant_pos d)

theorem multivariate_polynomial_sublevel_bound {N d : ℕ} (hN : 0 < N) (hd : 0 < d)
    (p : MvPolynomial (Fin N) ℝ) (hp : ∀ j, p.degreeOf j ≤ d)
    {u c : ℝ} (hu : 0 < u) (hc : 0 < c) (m : Fin N →₀ ℕ)
    (hm : c ≤ |p.coeff m|) :
    volume.real (unitMvPolynomialSublevel p u) ≤
      multivariateSublevelConstant N d * (u / c) ^ (((N * d : ℕ) : ℝ)⁻¹) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
  have h := symmetricCube_polynomial_sublevel_bound d hd n p hp hu hc m hm
  rw [unitMvPolynomialSublevel, symmetricUnitBox_volume_inter _ _
    (isClosed_le p.continuous_eval.abs continuous_const).measurableSet]
  have hmul := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ (2 : ℝ) ^ (n + 1))
  simpa only [multivariateSublevelConstant, Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, mul_assoc] using hmul

theorem weighted_multivariate_polynomial_sublevel_bound {N d : ℕ} (hN : 0 < N) (hd : 0 < d)
    (p : MvPolynomial (Fin N) ℝ) (hp : ∀ j, p.degreeOf j ≤ d)
    (ρ : (Fin N → ℝ) → ℝ) (hρ : IntegrableOn ρ (symmetricUnitBox N))
    {H : ℝ} (hH : 0 ≤ H) (hbound : ∀ x ∈ symmetricUnitBox N, ρ x ≤ H)
    {u c : ℝ} (hu : 0 < u) (hc : 0 < c) (m : Fin N →₀ ℕ)
    (hm : c ≤ |p.coeff m|) :
    (∫ x in unitMvPolynomialSublevel p u, ρ x) ≤
      H * multivariateSublevelConstant N d * (u / c) ^ (((N * d : ℕ) : ℝ)⁻¹) := by
  have hi : IntegrableOn (fun _ : Fin N → ℝ => H) (unitMvPolynomialSublevel p u) :=
    integrableOn_const (unitMvPolynomialSublevel_volume_ne_top p u)
  calc
    _ ≤ ∫ _x in unitMvPolynomialSublevel p u, H :=
      setIntegral_mono_on (hρ.mono_set Set.inter_subset_left) hi
        (unitMvPolynomialSublevel_measurable p u) (fun x hx => hbound x hx.1)
    _ = H * volume.real (unitMvPolynomialSublevel p u) := by rw [setIntegral_const, smul_eq_mul, mul_comm]
    _ ≤ H * (multivariateSublevelConstant N d * (u / c) ^ (((N * d : ℕ) : ℝ)⁻¹)) :=
      mul_le_mul_of_nonneg_left (multivariate_polynomial_sublevel_bound hN hd p hp hu hc m hm) hH
    _ = _ := by ring

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped Pointwise

def boxMvPolynomialSublevel {N : ℕ} (p : MvPolynomial (Fin N) ℝ) (R u : ℝ) : Set (Fin N → ℝ) :=
  {x | (∀ i, |x i| ≤ R) ∧ |MvPolynomial.eval x p| ≤ u}

theorem boxMvPolynomialSublevel_eq_smul {N : ℕ} (p : MvPolynomial (Fin N) ℝ)
    {R : ℝ} (hR : 0 < R) (u : ℝ) :
    boxMvPolynomialSublevel p R u = R • unitMvPolynomialSublevel (dilateMvPolynomial R p) u := by
  ext x
  constructor
  · intro hx
    have hback : R • (R⁻¹ • x) = x := by rw [smul_smul, mul_inv_cancel₀ hR.ne', one_smul]
    refine Set.mem_smul_set.mpr ⟨R⁻¹ • x, ⟨?_, ?_⟩, hback⟩
    · apply (symmetricUnitBox_mem N _).mpr
      intro i
      change |R⁻¹ * x i| ≤ 1
      rw [abs_mul, abs_inv, abs_of_pos hR]
      calc
        R⁻¹ * |x i| ≤ R⁻¹ * R := mul_le_mul_of_nonneg_left (hx.1 i) (inv_nonneg.mpr hR.le)
        _ = 1 := inv_mul_cancel₀ hR.ne'
    · change |MvPolynomial.eval (R⁻¹ • x) (dilateMvPolynomial R p)| ≤ u
      rw [dilateMvPolynomial_eval, hback]
      exact hx.2
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Set.mem_smul_set.mp hx
    refine ⟨?_, ?_⟩
    · intro i
      change |R * y i| ≤ R
      rw [abs_mul, abs_of_pos hR]
      have hi := (symmetricUnitBox_mem N y).mp hy.1 i
      exact (mul_le_mul_of_nonneg_left hi hR.le).trans_eq (mul_one R)
    · rw [← dilateMvPolynomial_eval]
      exact hy.2

theorem boxMvPolynomialSublevel_volume {N : ℕ} (p : MvPolynomial (Fin N) ℝ)
    {R : ℝ} (hR : 0 < R) (u : ℝ) :
    volume.real (boxMvPolynomialSublevel p R u) =
      R ^ N * volume.real (unitMvPolynomialSublevel (dilateMvPolynomial R p) u) := by
  rw [boxMvPolynomialSublevel_eq_smul p hR, measureReal_def, Measure.addHaar_smul_of_nonneg volume hR.le,
    ENNReal.toReal_mul]
  simp [Module.finrank_fintype_fun_eq_card, measureReal_def, hR.le]

theorem boxMvPolynomialSublevel_volume_ne_top {N : ℕ} (p : MvPolynomial (Fin N) ℝ)
    {R : ℝ} (hR : 0 < R) (u : ℝ) : volume (boxMvPolynomialSublevel p R u) ≠ ⊤ := by
  rw [boxMvPolynomialSublevel_eq_smul p hR, Measure.addHaar_smul_of_nonneg volume hR.le]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (unitMvPolynomialSublevel_volume_ne_top _ _)

theorem polynomial_sublevel_box_bound {N d : ℕ} (hN : 0 < N) (hd : 0 < d)
    (p : MvPolynomial (Fin N) ℝ) (hp : ∀ j, p.degreeOf j ≤ d)
    {R u c : ℝ} (hR : 1 ≤ R) (hu : 0 < u) (hc : 0 < c) (m : Fin N →₀ ℕ)
    (hm : c ≤ |p.coeff m|) :
    volume.real (boxMvPolynomialSublevel p R u) ≤
      R ^ N * multivariateSublevelConstant N d * (u / c) ^ (((N * d : ℕ) : ℝ)⁻¹) := by
  rw [boxMvPolynomialSublevel_volume p (zero_lt_one.trans_le hR)]
  have h := multivariate_polynomial_sublevel_bound hN hd (dilateMvPolynomial R p)
    (fun j => dilateMvPolynomial_degree_le R p j (hp j)) hu hc m
    (hm.trans (dilateMvPolynomial_coeff_abs_le hR p m))
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left h (pow_nonneg (zero_le_one.trans hR) N)

theorem polynomial_sublevel_bounded_set_bound {N d : ℕ} (hN : 0 < N) (hd : 0 < d)
    (p : MvPolynomial (Fin N) ℝ) (hp : ∀ j, p.degreeOf j ≤ d)
    (Ω : Set (Fin N → ℝ)) {R u c : ℝ} (hR : 1 ≤ R)
    (hΩ : ∀ x ∈ Ω, ∀ i, |x i| ≤ R) (hu : 0 < u) (hc : 0 < c) (m : Fin N →₀ ℕ)
    (hm : c ≤ |p.coeff m|) :
    volume.real (Ω ∩ {x | |MvPolynomial.eval x p| ≤ u}) ≤
      R ^ N * multivariateSublevelConstant N d * (u / c) ^ (((N * d : ℕ) : ℝ)⁻¹) := by
  have hs : Ω ∩ {x | |MvPolynomial.eval x p| ≤ u} ⊆ boxMvPolynomialSublevel p R u :=
    fun x hx => ⟨hΩ x hx.1, hx.2⟩
  exact (measureReal_mono hs (boxMvPolynomialSublevel_volume_ne_top p (zero_lt_one.trans_le hR) u)).trans
    (polynomial_sublevel_box_bound hN hd p hp hR hu hc m hm)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

theorem weighted_polynomial_sublevel_bounded_set_bound {N d : ℕ} (hN : 0 < N) (hd : 0 < d)
    (p : MvPolynomial (Fin N) ℝ) (hp : ∀ j, p.degreeOf j ≤ d)
    (Ω : Set (Fin N → ℝ)) (hΩm : MeasurableSet Ω) {R u c : ℝ} (hR : 1 ≤ R)
    (hΩ : ∀ x ∈ Ω, ∀ i, |x i| ≤ R)
    (ρ : (Fin N → ℝ) → ℝ) (hρ : IntegrableOn ρ Ω)
    {H : ℝ} (hH : 0 ≤ H) (hbound : ∀ x ∈ Ω, ρ x ≤ H)
    (hu : 0 < u) (hc : 0 < c) (m : Fin N →₀ ℕ) (hm : c ≤ |p.coeff m|) :
    (∫ x in Ω ∩ {x | |MvPolynomial.eval x p| ≤ u}, ρ x) ≤
      H * (R ^ N * multivariateSublevelConstant N d) * (u / c) ^ (((N * d : ℕ) : ℝ)⁻¹) := by
  let s := Ω ∩ {x | |MvPolynomial.eval x p| ≤ u}
  have hs : MeasurableSet s := hΩm.inter (isClosed_le p.continuous_eval.abs continuous_const).measurableSet
  have hsub : s ⊆ boxMvPolynomialSublevel p R u := fun x hx => ⟨hΩ x hx.1, hx.2⟩
  have hsfin : volume s ≠ ⊤ := measure_ne_top_of_subset hsub
    (boxMvPolynomialSublevel_volume_ne_top p (zero_lt_one.trans_le hR) u)
  calc
    _ ≤ ∫ _x in s, H := setIntegral_mono_on (hρ.mono_set Set.inter_subset_left)
      (integrableOn_const hsfin) hs (fun x hx => hbound x hx.1)
    _ = H * volume.real s := by rw [setIntegral_const, smul_eq_mul, mul_comm]
    _ ≤ H * (R ^ N * multivariateSublevelConstant N d * (u / c) ^ (((N * d : ℕ) : ℝ)⁻¹)) :=
      mul_le_mul_of_nonneg_left (polynomial_sublevel_bounded_set_bound hN hd p hp Ω hR hΩ hu hc m hm) hH
    _ = _ := by ring

theorem polynomial_sublevel_bound_of_value {N d : ℕ} (hN : 0 < N) (hd : 0 < d)
    (p : MvPolynomial (Fin N) ℝ) (hp : ∀ j, p.degreeOf j ≤ d)
    (Ω : Set (Fin N → ℝ)) {R u v : ℝ} (hR : 1 ≤ R)
    (hΩ : ∀ x ∈ Ω, ∀ i, |x i| ≤ R) (hu : 0 < u) (hv : 0 < v)
    (x₀ : Fin N → ℝ) (hx₀ : ∀ i, |x₀ i| ≤ 1) (hval : v ≤ |MvPolynomial.eval x₀ p|) :
    volume.real (Ω ∩ {x | |MvPolynomial.eval x p| ≤ u}) ≤
      R ^ N * multivariateSublevelConstant N d *
        (u * (d + 1 : ℝ) ^ N / v) ^ (((N * d : ℕ) : ℝ)⁻¹) := by
  obtain ⟨m, hm⟩ := exists_coefficient_of_unit_box_value p hp x₀ hx₀ hv hval
  have h := polynomial_sublevel_bounded_set_bound hN hd p hp Ω hR hΩ hu
    (div_pos hv (by positivity : 0 < (d + 1 : ℝ) ^ N)) m hm
  simpa only [div_div_eq_mul_div] using h

theorem weighted_polynomial_sublevel_bound_of_value {N d : ℕ} (hN : 0 < N) (hd : 0 < d)
    (p : MvPolynomial (Fin N) ℝ) (hp : ∀ j, p.degreeOf j ≤ d)
    (Ω : Set (Fin N → ℝ)) (hΩm : MeasurableSet Ω) {R u v : ℝ} (hR : 1 ≤ R)
    (hΩ : ∀ x ∈ Ω, ∀ i, |x i| ≤ R)
    (ρ : (Fin N → ℝ) → ℝ) (hρ : IntegrableOn ρ Ω)
    {H : ℝ} (hH : 0 ≤ H) (hbound : ∀ x ∈ Ω, ρ x ≤ H)
    (hu : 0 < u) (hv : 0 < v)
    (x₀ : Fin N → ℝ) (hx₀ : ∀ i, |x₀ i| ≤ 1) (hval : v ≤ |MvPolynomial.eval x₀ p|) :
    (∫ x in Ω ∩ {x | |MvPolynomial.eval x p| ≤ u}, ρ x) ≤
      H * (R ^ N * multivariateSublevelConstant N d) *
        (u * (d + 1 : ℝ) ^ N / v) ^ (((N * d : ℕ) : ℝ)⁻¹) := by
  obtain ⟨m, hm⟩ := exists_coefficient_of_unit_box_value p hp x₀ hx₀ hv hval
  have h := weighted_polynomial_sublevel_bounded_set_bound hN hd p hp Ω hΩm hR hΩ ρ hρ hH hbound hu
    (div_pos hv (by positivity : 0 < (d + 1 : ℝ) ^ N)) m hm
  simpa only [div_div_eq_mul_div] using h

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

theorem polynomial_det_exists_large_coefficient {ι : Type*} [Fintype ι] [DecidableEq ι]
    {N e : ℕ} (M : Matrix ι ι (MvPolynomial (Fin N) ℝ))
    (hM : ∀ a b j, (M a b).degreeOf j ≤ e)
    (x₀ : Fin N → ℝ) (hx₀ : ∀ j, |x₀ j| ≤ 1) (a : ι → ℝ)
    (hdiag : M.map (MvPolynomial.eval x₀) = Matrix.diagonal a)
    {c : ℝ} (hc : 0 < c) (ha : ∀ i, c ≤ |a i|) :
    ∃ m : Fin N →₀ ℕ,
      c ^ Fintype.card ι / (Fintype.card ι * e + 1 : ℝ) ^ N ≤ |M.det.coeff m| := by
  have h := exists_coefficient_of_unit_box_value M.det
    (fun j => polynomial_det_degreeOf_le M j e (fun a b => hM a b j)) x₀ hx₀
    (pow_pos hc _) (polynomial_det_value_abs_lower M x₀ a hdiag hc.le ha)
  simpa only [Nat.cast_mul] using h

theorem polynomial_det_sublevel_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    {N e d : ℕ} (hN : 0 < N) (hd : 0 < d) (hdeg : Fintype.card ι * e ≤ d)
    (M : Matrix ι ι (MvPolynomial (Fin N) ℝ)) (hM : ∀ a b j, (M a b).degreeOf j ≤ e)
    (x₀ : Fin N → ℝ) (hx₀ : ∀ j, |x₀ j| ≤ 1) (a : ι → ℝ)
    (hdiag : M.map (MvPolynomial.eval x₀) = Matrix.diagonal a)
    {c : ℝ} (hc : 0 < c) (ha : ∀ i, c ≤ |a i|)
    (Ω : Set (Fin N → ℝ)) {R u : ℝ} (hR : 1 ≤ R)
    (hΩ : ∀ x ∈ Ω, ∀ j, |x j| ≤ R) (hu : 0 < u) :
    volume.real (Ω ∩ {x | |(M.map (MvPolynomial.eval x)).det| ≤ u}) ≤
      R ^ N * multivariateSublevelConstant N d *
        (u * (d + 1 : ℝ) ^ N / c ^ Fintype.card ι) ^ (((N * d : ℕ) : ℝ)⁻¹) := by
  have h := polynomial_sublevel_bound_of_value hN hd M.det
    (fun j => (polynomial_det_degreeOf_le M j e (fun a b => hM a b j)).trans hdeg)
    Ω hR hΩ hu (pow_pos hc _) x₀ hx₀ (polynomial_det_value_abs_lower M x₀ a hdiag hc.le ha)
  simp only [RingHom.map_det, RingHom.mapMatrix_apply] at h
  exact h

theorem weighted_polynomial_det_sublevel_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    {N e d : ℕ} (hN : 0 < N) (hd : 0 < d) (hdeg : Fintype.card ι * e ≤ d)
    (M : Matrix ι ι (MvPolynomial (Fin N) ℝ)) (hM : ∀ a b j, (M a b).degreeOf j ≤ e)
    (x₀ : Fin N → ℝ) (hx₀ : ∀ j, |x₀ j| ≤ 1) (a : ι → ℝ)
    (hdiag : M.map (MvPolynomial.eval x₀) = Matrix.diagonal a)
    {c : ℝ} (hc : 0 < c) (ha : ∀ i, c ≤ |a i|)
    (Ω : Set (Fin N → ℝ)) (hΩm : MeasurableSet Ω) {R u : ℝ} (hR : 1 ≤ R)
    (hΩ : ∀ x ∈ Ω, ∀ j, |x j| ≤ R)
    (ρ : (Fin N → ℝ) → ℝ) (hρ : IntegrableOn ρ Ω)
    {H : ℝ} (hH : 0 ≤ H) (hbound : ∀ x ∈ Ω, ρ x ≤ H) (hu : 0 < u) :
    (∫ x in Ω ∩ {x | |(M.map (MvPolynomial.eval x)).det| ≤ u}, ρ x) ≤
      H * (R ^ N * multivariateSublevelConstant N d) *
        (u * (d + 1 : ℝ) ^ N / c ^ Fintype.card ι) ^ (((N * d : ℕ) : ℝ)⁻¹) := by
  have h := weighted_polynomial_sublevel_bound_of_value hN hd M.det
    (fun j => (polynomial_det_degreeOf_le M j e (fun a b => hM a b j)).trans hdeg)
    Ω hΩm hR hΩ ρ hρ hH hbound hu (pow_pos hc _) x₀ hx₀
    (polynomial_det_value_abs_lower M x₀ a hdiag hc.le ha)
  simp only [RingHom.map_det, RingHom.mapMatrix_apply] at h
  exact h

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem polynomial_grid_sublevel_transfer {Ω : Type*} [Fintype Ω] {N : ℕ}
    (p : FiniteProbabilityWeights Ω) (grid : Ω → Fin N → ℤ) (hinj : Function.Injective grid)
    (L : ℕ) (hL : 0 < L) (hgrid : ∀ ω i, -(L : ℤ) ≤ grid ω i ∧ grid ω i < L)
    (P : MvPolynomial (Fin N) ℝ) (M K u : ℝ) (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hw : ∀ ω, p.weight ω ≤ M * ((L : ℝ) ^ N)⁻¹)
    (hLip : ∀ x y : Fin N → ℝ, (∀ i, |x i| ≤ 1) → (∀ i, |y i| ≤ 1) →
      |MvPolynomial.eval x P - MvPolynomial.eval y P| ≤ K * ‖x - y‖) :
    p.eventProbability (fun ω => |MvPolynomial.eval (fun i => (grid ω i : ℝ) / L) P| ≤ u) ≤
      M * volume.real (boxMvPolynomialSublevel P 1 (u + K / L)) := by
  let cell := fun ω => rectangularLatticeCell (fun _ => 0) (fun _ => (L : ℝ)) (grid ω)
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  apply finite_cell_event_probability_le p _ volume cell _ M (((L : ℝ) ^ N)⁻¹) hM
    (fun a b hab => rectangularLatticeCell_disjoint _ _ (fun _ => hL') (hinj.ne hab))
    (fun ω => rectangularLatticeCell_measurable _ _ _)
    (fun ω => rectangularLatticeCell_volume_ne_top _ _ _) _ hw _
    (boxMvPolynomialSublevel_volume_ne_top P (by norm_num) _)
  · intro ω
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
      rectangularLatticeCell_volume (fun _ : Fin N => 0) (fun _ => (L : ℝ)) (fun _ => hL') (grid ω)
  · intro ω hω x hx
    have hxbox := integerBoxCell_unit_bound L hL (grid ω) (hgrid ω) x hx
    have hycell := rectangularLatticePoint_mem_cell (fun _ : Fin N => 0) (fun _ => (L : ℝ))
      (fun _ => hL') (grid ω)
    have hybox := integerBoxCell_unit_bound L hL (grid ω) (hgrid ω) _ hycell
    have hdist := rectangularLatticeCell_point_distance (fun _ : Fin N => 0) (fun _ => (L : ℝ))
      (fun _ => hL') (1 / (L : ℝ)) (by positivity) (fun _ => le_rfl) (grid ω) x hx
    have h := hLip x _ hxbox hybox
    have hpoint : rectangularLatticePoint (fun _ : Fin N => 0) (fun _ => (L : ℝ)) (grid ω) =
        (fun i => (grid ω i : ℝ) / L) := by
      funext i
      simp only [rectangularLatticePoint, sub_zero]
    rw [hpoint] at h hdist
    refine ⟨hxbox, ?_⟩
    have hchange : |MvPolynomial.eval x P - MvPolynomial.eval
        (fun i => (grid ω i : ℝ) / L) P| ≤ K / L := by
      simpa only [mul_one_div] using
        h.trans (mul_le_mul_of_nonneg_left hdist hK)
    have ht := abs_sub_abs_le_abs_sub (MvPolynomial.eval x P)
      (MvPolynomial.eval (fun i => (grid ω i : ℝ) / L) P)
    nlinarith

theorem polynomial_grid_sublevel_bound_of_value {Ω : Type*} [Fintype Ω] {N d : ℕ}
    (hN : 0 < N) (hd : 0 < d)
    (p : FiniteProbabilityWeights Ω) (grid : Ω → Fin N → ℤ) (hinj : Function.Injective grid)
    (L : ℕ) (hL : 0 < L) (hgrid : ∀ ω i, -(L : ℤ) ≤ grid ω i ∧ grid ω i < L)
    (P : MvPolynomial (Fin N) ℝ) (hdeg : ∀ i, P.degreeOf i ≤ d)
    (M K u : ℝ) (hM : 0 ≤ M) (hK : 0 ≤ K) (hu : 0 < u)
    (hw : ∀ ω, p.weight ω ≤ M * ((L : ℝ) ^ N)⁻¹)
    (hLip : ∀ x y : Fin N → ℝ, (∀ i, |x i| ≤ 1) → (∀ i, |y i| ≤ 1) →
      |MvPolynomial.eval x P - MvPolynomial.eval y P| ≤ K * ‖x - y‖)
    (x₀ : Fin N → ℝ) (hx₀ : ∀ i, |x₀ i| ≤ 1) (hval : 1 ≤ |MvPolynomial.eval x₀ P|) :
    p.eventProbability (fun ω => |MvPolynomial.eval (fun i => (grid ω i : ℝ) / L) P| ≤ u) ≤
      M * (multivariateSublevelConstant N d *
        ((u + K / L) * (d + 1 : ℝ) ^ N) ^ (((N * d : ℕ) : ℝ)⁻¹)) := by
  apply (polynomial_grid_sublevel_transfer p grid hinj L hL hgrid P M K u hM hK hw hLip).trans
  apply mul_le_mul_of_nonneg_left _ hM
  obtain ⟨m, hm⟩ := exists_coefficient_of_unit_box_value P hdeg x₀ hx₀ zero_lt_one hval
  have h := polynomial_sublevel_box_bound hN hd P hdeg (by norm_num : (1 : ℝ) ≤ 1)
    (add_pos_of_pos_of_nonneg hu (div_nonneg hK (Nat.cast_nonneg L)))
    (by positivity : (0 : ℝ) < 1 / (d + 1 : ℝ) ^ N) m hm
  simpa only [one_pow, one_mul, div_div_eq_mul_div, div_one] using h

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators

def normalizedMatrixEntryIndex (n : ℕ) (i j : Fin n) : Fin (n * n) :=
  finProdFinEquiv (i,j)

noncomputable def normalizedMatrixDeterminantPolynomial (n : ℕ) :
    MvPolynomial (Fin (n * n)) ℝ :=
  (coordinateMatrixPolynomial (normalizedMatrixEntryIndex n)).det

def normalizedMatrixIdentityPoint (n : ℕ) (k : Fin (n * n)) : ℝ :=
  if (finProdFinEquiv.symm k).1 = (finProdFinEquiv.symm k).2 then 1 else 0

theorem normalizedMatrixDeterminantPolynomial_eval (n : ℕ) (x : Fin (n * n) → ℝ) :
    MvPolynomial.eval x (normalizedMatrixDeterminantPolynomial n) =
      Matrix.det (fun i j : Fin n => x (normalizedMatrixEntryIndex n i j)) :=
  coordinateMatrixPolynomial_eval _ _

theorem normalizedMatrixDeterminantPolynomial_degree (n : ℕ) (k : Fin (n * n)) :
    (normalizedMatrixDeterminantPolynomial n).degreeOf k ≤ n := by
  simpa only [Fintype.card_fin, normalizedMatrixDeterminantPolynomial] using
    coordinateMatrixPolynomial_degree (normalizedMatrixEntryIndex n) k

theorem normalizedMatrixDeterminantPolynomial_totalDegree (n : ℕ) :
    (normalizedMatrixDeterminantPolynomial n).totalDegree ≤ n := by
  simpa only [Fintype.card_fin, normalizedMatrixDeterminantPolynomial] using
    coordinateMatrixPolynomial_totalDegree (normalizedMatrixEntryIndex n)

theorem normalizedMatrixIdentityPoint_bound (n : ℕ) (k : Fin (n * n)) :
    |normalizedMatrixIdentityPoint n k| ≤ 1 := by
  unfold normalizedMatrixIdentityPoint
  split_ifs <;> norm_num

theorem normalizedMatrixDeterminantPolynomial_identity (n : ℕ) :
    MvPolynomial.eval (normalizedMatrixIdentityPoint n) (normalizedMatrixDeterminantPolynomial n) = 1 := by
  rw [normalizedMatrixDeterminantPolynomial_eval]
  have he : (fun i j : Fin n => normalizedMatrixIdentityPoint n (normalizedMatrixEntryIndex n i j)) =
      (1 : Matrix (Fin n) (Fin n) ℝ) := by
    ext i j
    simp only [normalizedMatrixIdentityPoint, normalizedMatrixEntryIndex,
      Equiv.symm_apply_apply, Matrix.one_apply]
  rw [he, Matrix.det_one]

noncomputable def normalizedMatrixDeterminantLip (n : ℕ) : ℝ :=
  (n * n : ℕ) * ((n.factorial : ℝ) * ((n : ℝ) * 2 ^ n))

theorem normalizedMatrixDeterminantLip_nonneg (n : ℕ) :
    0 ≤ normalizedMatrixDeterminantLip n := by
  unfold normalizedMatrixDeterminantLip
  positivity

theorem normalizedMatrixDeterminantPolynomial_derivative (n : ℕ)
    (x : Fin (n * n) → ℝ) (hx : ∀ j, |x j| ≤ 2) :
    ‖fderiv ℝ (fun x => MvPolynomial.eval x (normalizedMatrixDeterminantPolynomial n)) x‖ ≤
      normalizedMatrixDeterminantLip n := by
  have h := polynomial_det_fderiv_norm_le
    (coordinateMatrixPolynomial (normalizedMatrixEntryIndex n)) x
    (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 1)
    (fun a b => by
      simpa only [coordinateMatrixPolynomial, MvPolynomial.eval_X]
        using hx (normalizedMatrixEntryIndex n a b))
    (fun a b j => by
      simp only [coordinateMatrixPolynomial, MvPolynomial.pderiv_X, Pi.single_apply]
      split_ifs <;> norm_num)
  rw [polynomial_det_eval_function] at h
  simpa only [Fintype.card_fin, mul_one, normalizedMatrixDeterminantLip,
    normalizedMatrixDeterminantPolynomial] using h

theorem normalizedMatrixDeterminantPolynomial_lipschitz (n : ℕ)
    (x y : Fin (n * n) → ℝ) (hx : ∀ j, |x j| ≤ 2) (hy : ∀ j, |y j| ≤ 2) :
    |MvPolynomial.eval x (normalizedMatrixDeterminantPolynomial n) -
      MvPolynomial.eval y (normalizedMatrixDeterminantPolynomial n)| ≤
      normalizedMatrixDeterminantLip n * ‖x - y‖ := by
  let S : Set (Fin (n * n) → ℝ) := Set.Icc (fun _ => -2) (fun _ => 2)
  have hmem (z : Fin (n * n) → ℝ) : z ∈ S ↔ ∀ j, |z j| ≤ 2 := by
    simp only [S, Set.mem_Icc, Pi.le_def, abs_le, forall_and]
  have h := Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun z (_ : z ∈ S) => (mvPolynomial_contDiff_eval (normalizedMatrixDeterminantPolynomial n)).differentiable
      (by norm_num) z)
    (fun z hz => normalizedMatrixDeterminantPolynomial_derivative n z ((hmem z).mp hz))
    (convex_Icc _ _) ((hmem y).mpr hy) ((hmem x).mpr hx)
  simpa only [Real.norm_eq_abs] using h

theorem normalizedMatrixDeterminantPolynomial_sublevel {n : ℕ} (hn : 0 < n)
    (Ω : Set (Fin (n * n) → ℝ)) {R u : ℝ} (hR : 1 ≤ R)
    (hΩ : ∀ x ∈ Ω, ∀ j, |x j| ≤ R) (hu : 0 < u) :
    volume.real (Ω ∩ {x | |MvPolynomial.eval x (normalizedMatrixDeterminantPolynomial n)| ≤ u}) ≤
      R ^ (n * n) * multivariateSublevelConstant (n * n) n *
        (u * (n + 1 : ℝ) ^ (n * n)) ^ (((n * n * n : ℕ) : ℝ)⁻¹) := by
  have h := polynomial_sublevel_bound_of_value (Nat.mul_pos hn hn) hn
    (normalizedMatrixDeterminantPolynomial n) (normalizedMatrixDeterminantPolynomial_degree n)
    Ω hR hΩ hu (by norm_num : (0 : ℝ) < 1)
    (normalizedMatrixIdentityPoint n) (normalizedMatrixIdentityPoint_bound n)
    (by rw [normalizedMatrixDeterminantPolynomial_identity]; norm_num)
  simpa only [div_one] using h

theorem normalizedMatrixDeterminantPolynomial_zero_eval (x : Fin (0 * 0) → ℝ) :
    MvPolynomial.eval x (normalizedMatrixDeterminantPolynomial 0) = 1 := by
  rw [normalizedMatrixDeterminantPolynomial_eval]
  exact Matrix.det_isEmpty

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

noncomputable def reindexPolynomialMatrix {I J O : Type*} (e : I ≃ J)
    (M : Matrix O O (MvPolynomial I ℝ)) : Matrix O O (MvPolynomial J ℝ) :=
  M.map (MvPolynomial.rename e)

theorem reindexPolynomialMatrix_degreeOf {I J O : Type*} (e : I ≃ J)
    (M : Matrix O O (MvPolynomial I ℝ)) (a b : O) (j : J) :
    (reindexPolynomialMatrix e M a b).degreeOf j = (M a b).degreeOf (e.symm j) := by
  have h := MvPolynomial.degreeOf_rename_of_injective (p := M a b) e.injective (e.symm j)
  simp only [e.apply_symm_apply] at h
  exact h

theorem reindexPolynomialMatrix_eval {I J O : Type*} (e : I ≃ J)
    (M : Matrix O O (MvPolynomial I ℝ)) (x : J → ℝ) :
    (reindexPolynomialMatrix e M).map (MvPolynomial.eval x) =
      M.map (MvPolynomial.eval (x ∘ e)) := by
  ext a b
  exact MvPolynomial.eval_rename e x (M a b)

theorem reindexed_polynomial_det_sublevel_bound {I O : Type*}
    [Fintype O] [DecidableEq O] {N t d : ℕ} (e : I ≃ Fin N)
    (hN : 0 < N) (hd : 0 < d) (hdeg : Fintype.card O * t ≤ d)
    (M : Matrix O O (MvPolynomial I ℝ)) (hM : ∀ a b j, (M a b).degreeOf j ≤ t)
    (x₀ : I → ℝ) (hx₀ : ∀ j, |x₀ j| ≤ 1) (a : O → ℝ)
    (hdiag : M.map (MvPolynomial.eval x₀) = Matrix.diagonal a)
    {c : ℝ} (hc : 0 < c) (ha : ∀ i, c ≤ |a i|)
    (Ω : Set (Fin N → ℝ)) {R u : ℝ} (hR : 1 ≤ R)
    (hΩ : ∀ x ∈ Ω, ∀ j, |x j| ≤ R) (hu : 0 < u) :
    volume.real (Ω ∩ {x | |(M.map (MvPolynomial.eval (x ∘ e))).det| ≤ u}) ≤
      R ^ N * multivariateSublevelConstant N d *
        (u * (d + 1 : ℝ) ^ N / c ^ Fintype.card O) ^ (((N * d : ℕ) : ℝ)⁻¹) := by
  have hM' : ∀ a b j, (reindexPolynomialMatrix e M a b).degreeOf j ≤ t := by
    intro a b j
    rw [reindexPolynomialMatrix_degreeOf]
    exact hM a b (e.symm j)
  have hdiag' : (reindexPolynomialMatrix e M).map (MvPolynomial.eval (x₀ ∘ e.symm)) =
      Matrix.diagonal a := by
    rw [reindexPolynomialMatrix_eval]
    simpa only [Function.comp_def, e.symm_apply_apply] using hdiag
  have h := polynomial_det_sublevel_bound hN hd hdeg (reindexPolynomialMatrix e M) hM'
    (x₀ ∘ e.symm) (fun j => hx₀ (e.symm j)) a hdiag' hc ha Ω hR hΩ hu
  simp only [reindexPolynomialMatrix_eval] at h
  exact h

theorem weighted_reindexed_polynomial_det_sublevel_bound {I O : Type*}
    [Fintype O] [DecidableEq O] {N t d : ℕ} (e : I ≃ Fin N)
    (hN : 0 < N) (hd : 0 < d) (hdeg : Fintype.card O * t ≤ d)
    (M : Matrix O O (MvPolynomial I ℝ)) (hM : ∀ a b j, (M a b).degreeOf j ≤ t)
    (x₀ : I → ℝ) (hx₀ : ∀ j, |x₀ j| ≤ 1) (a : O → ℝ)
    (hdiag : M.map (MvPolynomial.eval x₀) = Matrix.diagonal a)
    {c : ℝ} (hc : 0 < c) (ha : ∀ i, c ≤ |a i|)
    (Ω : Set (Fin N → ℝ)) (hΩm : MeasurableSet Ω) {R u : ℝ} (hR : 1 ≤ R)
    (hΩ : ∀ x ∈ Ω, ∀ j, |x j| ≤ R)
    (ρ : (Fin N → ℝ) → ℝ) (hρ : IntegrableOn ρ Ω)
    {H : ℝ} (hH : 0 ≤ H) (hbound : ∀ x ∈ Ω, ρ x ≤ H) (hu : 0 < u) :
    (∫ x in Ω ∩ {x | |(M.map (MvPolynomial.eval (x ∘ e))).det| ≤ u}, ρ x) ≤
      H * (R ^ N * multivariateSublevelConstant N d) *
        (u * (d + 1 : ℝ) ^ N / c ^ Fintype.card O) ^ (((N * d : ℕ) : ℝ)⁻¹) := by
  have hM' : ∀ a b j, (reindexPolynomialMatrix e M a b).degreeOf j ≤ t := by
    intro a b j
    rw [reindexPolynomialMatrix_degreeOf]
    exact hM a b (e.symm j)
  have hdiag' : (reindexPolynomialMatrix e M).map (MvPolynomial.eval (x₀ ∘ e.symm)) =
      Matrix.diagonal a := by
    rw [reindexPolynomialMatrix_eval]
    simpa only [Function.comp_def, e.symm_apply_apply] using hdiag
  have h := weighted_polynomial_det_sublevel_bound hN hd hdeg (reindexPolynomialMatrix e M) hM'
    (x₀ ∘ e.symm) (fun j => hx₀ (e.symm j)) a hdiag' hc ha Ω hΩm hR hΩ ρ hρ hH hbound hu
  simp only [reindexPolynomialMatrix_eval] at h
  exact h

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem shiftedPolynomial_grid_sublevel_transfer {Ω : Type*} [Fintype Ω] {N : ℕ}
    (p : FiniteProbabilityWeights Ω) (grid : Ω → Fin N → ℤ) (hinj : Function.Injective grid)
    (a S : Fin N → ℝ) (hS : ∀ i, 0 < S i)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hmesh : ∀ i, 1 / S i ≤ δ)
    (hgrid : ∀ ω i, |rectangularLatticePoint a S (grid ω) i| ≤ 1)
    (P : MvPolynomial (Fin N) ℝ) (M K u : ℝ) (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hw : ∀ ω, p.weight ω ≤ M * (∏ i, S i)⁻¹)
    (hLip : ∀ x y : Fin N → ℝ, (∀ i, |x i| ≤ 2) → (∀ i, |y i| ≤ 2) →
      |MvPolynomial.eval x P - MvPolynomial.eval y P| ≤ K * ‖x - y‖) :
    p.eventProbability (fun ω => |MvPolynomial.eval (rectangularLatticePoint a S (grid ω)) P| ≤ u) ≤
      M * volume.real (boxMvPolynomialSublevel P 2 (u + K * δ)) := by
  let cell := fun ω => rectangularLatticeCell a S (grid ω)
  apply finite_cell_event_probability_le p _ volume cell _ M ((∏ i, S i)⁻¹) hM
    (fun v w hvw => rectangularLatticeCell_disjoint a S hS (hinj.ne hvw))
    (fun ω => rectangularLatticeCell_measurable _ _ _)
    (fun ω => rectangularLatticeCell_volume_ne_top _ _ _)
    (fun ω => rectangularLatticeCell_volume a S hS (grid ω)) hw _
    (boxMvPolynomialSublevel_volume_ne_top P (by norm_num) _)
  intro ω hω x hx
  have hd := rectangularLatticeCell_point_distance a S hS δ hδ hmesh (grid ω) x hx
  have hxb (i : Fin N) : |x i| ≤ 2 := by
    have hi0 : |x i - rectangularLatticePoint a S (grid ω) i| ≤
        ‖x - rectangularLatticePoint a S (grid ω)‖ := by
      simpa only [Pi.sub_apply, Real.norm_eq_abs] using
        norm_le_pi_norm (x - rectangularLatticePoint a S (grid ω)) i
    have hi := hi0.trans hd
    have ht := abs_add_le (x i - rectangularLatticePoint a S (grid ω) i)
      (rectangularLatticePoint a S (grid ω) i)
    rw [sub_add_cancel] at ht
    exact ht.trans (by linarith [hgrid ω i])
  have hyb (i : Fin N) : |rectangularLatticePoint a S (grid ω) i| ≤ 2 :=
    (hgrid ω i).trans (by norm_num)
  have he := (hLip x _ hxb hyb).trans (mul_le_mul_of_nonneg_left hd hK)
  refine ⟨hxb, ?_⟩
  have ha := abs_sub_abs_le_abs_sub (MvPolynomial.eval x P)
    (MvPolynomial.eval (rectangularLatticePoint a S (grid ω)) P)
  linarith

theorem shiftedPolynomial_grid_sublevel_bound_of_value {Ω : Type*} [Fintype Ω] {N d : ℕ}
    (hN : 0 < N) (hd : 0 < d)
    (p : FiniteProbabilityWeights Ω) (grid : Ω → Fin N → ℤ) (hinj : Function.Injective grid)
    (a S : Fin N → ℝ) (hS : ∀ i, 0 < S i)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hmesh : ∀ i, 1 / S i ≤ δ)
    (hgrid : ∀ ω i, |rectangularLatticePoint a S (grid ω) i| ≤ 1)
    (P : MvPolynomial (Fin N) ℝ) (hdeg : ∀ i, P.degreeOf i ≤ d)
    (M K u : ℝ) (hM : 0 ≤ M) (hK : 0 ≤ K) (hu : 0 < u)
    (hw : ∀ ω, p.weight ω ≤ M * (∏ i, S i)⁻¹)
    (hLip : ∀ x y : Fin N → ℝ, (∀ i, |x i| ≤ 2) → (∀ i, |y i| ≤ 2) →
      |MvPolynomial.eval x P - MvPolynomial.eval y P| ≤ K * ‖x - y‖)
    (x₀ : Fin N → ℝ) (hx₀ : ∀ i, |x₀ i| ≤ 1) (hval : 1 ≤ |MvPolynomial.eval x₀ P|) :
    p.eventProbability (fun ω => |MvPolynomial.eval (rectangularLatticePoint a S (grid ω)) P| ≤ u) ≤
      M * (2 ^ N * multivariateSublevelConstant N d *
        ((u + K * δ) * (d + 1 : ℝ) ^ N) ^ (((N * d : ℕ) : ℝ)⁻¹)) := by
  apply (shiftedPolynomial_grid_sublevel_transfer p grid hinj a S hS hδ hδ1 hmesh hgrid
    P M K u hM hK hw hLip).trans
  apply mul_le_mul_of_nonneg_left _ hM
  obtain ⟨t, ht⟩ := exists_coefficient_of_unit_box_value P hdeg x₀ hx₀ zero_lt_one hval
  have h := polynomial_sublevel_box_bound hN hd P hdeg (by norm_num : (1 : ℝ) ≤ 2)
    (add_pos_of_pos_of_nonneg hu (mul_nonneg hK hδ))
    (by positivity : (0 : ℝ) < 1 / (d + 1 : ℝ) ^ N) t ht
  simpa only [div_div_eq_mul_div, div_one] using h

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators Classical

variable {n N : ℕ}

noncomputable def embeddedMatrixDeterminantPolynomial
    (e : Fin n × Fin n ↪ Fin N) : MvPolynomial (Fin N) ℝ :=
  (coordinateMatrixPolynomial (fun i j => e (i,j))).det

noncomputable def embeddedMatrixIdentityPoint
    (e : Fin n × Fin n ↪ Fin N) (k : Fin N) : ℝ :=
  if ∃ i : Fin n, e (i,i) = k then 1 else 0

theorem embeddedMatrixIdentityPoint_entry (e : Fin n × Fin n ↪ Fin N) (a b : Fin n) :
    embeddedMatrixIdentityPoint e (e (a,b)) = if a = b then 1 else 0 := by
  have hdiag : (∃ i : Fin n, e (i,i) = e (a,b)) ↔ a = b := by
    constructor
    · rintro ⟨i,hi⟩
      have hh := e.injective hi
      exact (congrArg Prod.fst hh).symm.trans (congrArg Prod.snd hh)
    · intro hab
      subst b
      exact ⟨a,rfl⟩
  simp only [embeddedMatrixIdentityPoint, hdiag]

theorem embeddedMatrixIdentityPoint_bound (e : Fin n × Fin n ↪ Fin N) (k : Fin N) :
    |embeddedMatrixIdentityPoint e k| ≤ 1 := by
  unfold embeddedMatrixIdentityPoint
  split_ifs <;> norm_num

theorem embeddedMatrixDeterminantPolynomial_eval
    (e : Fin n × Fin n ↪ Fin N) (x : Fin N → ℝ) :
    MvPolynomial.eval x (embeddedMatrixDeterminantPolynomial e) =
      Matrix.det (fun i j : Fin n => x (e (i,j))) :=
  coordinateMatrixPolynomial_eval _ _

theorem embeddedMatrixDeterminantPolynomial_degree
    (e : Fin n × Fin n ↪ Fin N) (k : Fin N) :
    (embeddedMatrixDeterminantPolynomial e).degreeOf k ≤ n := by
  simpa only [Fintype.card_fin, embeddedMatrixDeterminantPolynomial] using
    coordinateMatrixPolynomial_degree (fun i j => e (i,j)) k

theorem embeddedMatrixDeterminantPolynomial_totalDegree
    (e : Fin n × Fin n ↪ Fin N) :
    (embeddedMatrixDeterminantPolynomial e).totalDegree ≤ n := by
  simpa only [Fintype.card_fin, embeddedMatrixDeterminantPolynomial] using
    coordinateMatrixPolynomial_totalDegree (fun i j => e (i,j))

theorem embeddedMatrixDeterminantPolynomial_identity
    (e : Fin n × Fin n ↪ Fin N) :
    MvPolynomial.eval (embeddedMatrixIdentityPoint e) (embeddedMatrixDeterminantPolynomial e) = 1 := by
  rw [embeddedMatrixDeterminantPolynomial_eval]
  have he : (fun i j : Fin n => embeddedMatrixIdentityPoint e (e (i,j))) =
      (1 : Matrix (Fin n) (Fin n) ℝ) := by
    ext i j
    simpa only [Matrix.one_apply] using embeddedMatrixIdentityPoint_entry e i j
  rw [he, Matrix.det_one]

noncomputable def embeddedMatrixDeterminantLip (n N : ℕ) : ℝ :=
  (N : ℝ) * ((n.factorial : ℝ) * ((n : ℝ) * 2 ^ n))

theorem embeddedMatrixDeterminantLip_nonneg (n N : ℕ) :
    0 ≤ embeddedMatrixDeterminantLip n N := by
  unfold embeddedMatrixDeterminantLip
  positivity

theorem embeddedMatrixDeterminantPolynomial_derivative
    (e : Fin n × Fin n ↪ Fin N) (x : Fin N → ℝ) (hx : ∀ j, |x j| ≤ 2) :
    ‖fderiv ℝ (fun x => MvPolynomial.eval x (embeddedMatrixDeterminantPolynomial e)) x‖ ≤
      embeddedMatrixDeterminantLip n N := by
  have h := polynomial_det_fderiv_norm_le
    (coordinateMatrixPolynomial (fun i j => e (i,j))) x
    (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 1)
    (fun a b => by
      simpa only [coordinateMatrixPolynomial, MvPolynomial.eval_X] using hx (e (a,b)))
    (fun a b j => by
      simp only [coordinateMatrixPolynomial, MvPolynomial.pderiv_X, Pi.single_apply]
      split_ifs <;> norm_num)
  rw [polynomial_det_eval_function] at h
  simpa only [Fintype.card_fin, mul_one, embeddedMatrixDeterminantLip,
    embeddedMatrixDeterminantPolynomial] using h

theorem embeddedMatrixDeterminantPolynomial_lipschitz
    (e : Fin n × Fin n ↪ Fin N) (x y : Fin N → ℝ)
    (hx : ∀ j, |x j| ≤ 2) (hy : ∀ j, |y j| ≤ 2) :
    |MvPolynomial.eval x (embeddedMatrixDeterminantPolynomial e) -
      MvPolynomial.eval y (embeddedMatrixDeterminantPolynomial e)| ≤
      embeddedMatrixDeterminantLip n N * ‖x - y‖ := by
  let S : Set (Fin N → ℝ) := Set.Icc (fun _ => -2) (fun _ => 2)
  have hmem (z : Fin N → ℝ) : z ∈ S ↔ ∀ j, |z j| ≤ 2 := by
    simp only [S, Set.mem_Icc, Pi.le_def, abs_le, forall_and]
  have h := Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun z (_ : z ∈ S) => (mvPolynomial_contDiff_eval (embeddedMatrixDeterminantPolynomial e)).differentiable
      (by norm_num) z)
    (fun z hz => embeddedMatrixDeterminantPolynomial_derivative e z ((hmem z).mp hz))
    (convex_Icc _ _) ((hmem y).mpr hy) ((hmem x).mpr hx)
  simpa only [Real.norm_eq_abs] using h

theorem embeddedMatrixDeterminantPolynomial_sublevel
    (e : Fin n × Fin n ↪ Fin N) (hn : 0 < n)
    (Ω : Set (Fin N → ℝ)) {R u : ℝ} (hR : 1 ≤ R)
    (hΩ : ∀ x ∈ Ω, ∀ j, |x j| ≤ R) (hu : 0 < u) :
    volume.real (Ω ∩ {x | |MvPolynomial.eval x (embeddedMatrixDeterminantPolynomial e)| ≤ u}) ≤
      R ^ N * multivariateSublevelConstant N n *
        (u * (n + 1 : ℝ) ^ N) ^ (((N * n : ℕ) : ℝ)⁻¹) := by
  have hN : 0 < N := Nat.zero_lt_of_lt (e (⟨0,hn⟩,⟨0,hn⟩)).isLt
  have h := polynomial_sublevel_bound_of_value hN hn
    (embeddedMatrixDeterminantPolynomial e) (embeddedMatrixDeterminantPolynomial_degree e)
    Ω hR hΩ hu (by norm_num : (0 : ℝ) < 1)
    (embeddedMatrixIdentityPoint e) (embeddedMatrixIdentityPoint_bound e)
    (by rw [embeddedMatrixDeterminantPolynomial_identity]; norm_num)
  simpa only [div_one] using h

theorem embeddedMatrixDeterminantPolynomial_zero_eval
    (e : Fin 0 × Fin 0 ↪ Fin N) (x : Fin N → ℝ) :
    MvPolynomial.eval x (embeddedMatrixDeterminantPolynomial e) = 1 := by
  rw [embeddedMatrixDeterminantPolynomial_eval]
  exact Matrix.det_isEmpty

end Erdos3

end

end OAI
