import Surreal.Algebra.Modulus
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Polynomial root bounds over an ordered base field

The finite algebraic root estimates in `polynomial:prop:rootbounds` and
`polynomial:eq:cauchybound` of `docs/surcomplex/polynomial-algebra/article.tex`.
The absolute value takes values in an arbitrary ordered field. In particular,
the modulus of `Complexify F` retains infinite and infinitesimal scales; these
proofs impose no Archimedean or topological hypothesis.
-/

noncomputable section

namespace Surreal.Complexify

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F] [IsRealClosed F]

/-- The base-field-valued modulus, bundled as an absolute value. -/
def modulusAbsoluteValue : AbsoluteValue (Complexify F) F where
  toFun := modulus
  map_mul' := modulus_mul
  nonneg' := modulus_nonneg
  eq_zero' := modulus_eq_zero_iff
  add_le' := modulus_add_le

@[simp] theorem modulusAbsoluteValue_apply (z : Complexify F) :
    (modulusAbsoluteValue (F := F)) z = modulus z := rfl

end Surreal.Complexify

namespace Surreal.FinitePolynomial

open Polynomial Finset

variable {K F : Type*} [Field K] [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- Finite triangle inequality for an ordered-field-valued absolute value. -/
theorem absoluteValue_sum_le (v : AbsoluteValue K F) {ι : Type*}
    (s : Finset ι) (f : ι → K) : v (∑ i ∈ s, f i) ≤ ∑ i ∈ s, v (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    simp only [sum_insert ha]
    exact (v.add_le _ _).trans (add_le_add_right ih _)

/-- The root equation bounds the leading power by all lower normalized terms. -/
theorem root_power_le_sum (v : AbsoluteValue K F) (p : K[X]) (hp : p ≠ 0)
    {z : K} (hz : p.IsRoot z) :
    v z ^ p.natDegree ≤ ∑ j ∈ range p.natDegree,
      v (p.coeff j / p.leadingCoeff) * v z ^ j := by
  have h := hz
  rw [IsRoot.def, eval_eq_sum_range, sum_range_succ, coeff_natDegree,
    add_eq_zero_iff_eq_neg] at h
  have habs := congrArg v h
  simp only [v.map_mul, v.map_pow, v.map_neg] at habs
  have hl : 0 < v p.leadingCoeff := v.pos (leadingCoeff_ne_zero.mpr hp)
  apply (mul_le_mul_iff_left₀ hl).mp
  calc
    v z ^ p.natDegree * v p.leadingCoeff =
        v (∑ j ∈ range p.natDegree, p.coeff j * z ^ j) := by
          simpa [mul_comm] using habs.symm
    _ ≤ ∑ j ∈ range p.natDegree, v (p.coeff j * z ^ j) := absoluteValue_sum_le v _ _
    _ = (∑ j ∈ range p.natDegree,
        v (p.coeff j / p.leadingCoeff) * v z ^ j) * v p.leadingCoeff := by
      rw [sum_mul]
      apply sum_congr rfl
      intro j _
      simp only [map_mul, map_div₀, map_pow]
      field_simp

/-- A uniform coefficient-ratio bound gives the strict Cauchy estimate. -/
theorem root_lt_one_add_of_coeff_le (v : AbsoluteValue K F) (p : K[X]) (hp : p ≠ 0)
    {z : K} (hz : p.IsRoot z) {A : F} (hA : 0 ≤ A)
    (hcoeff : ∀ j < p.natDegree, v (p.coeff j / p.leadingCoeff) ≤ A) :
    v z < 1 + A := by
  have hroot := root_power_le_sum v p hp hz
  have hsum : v z ^ p.natDegree ≤ A * ∑ j ∈ range p.natDegree, v z ^ j := by
    apply hroot.trans
    rw [mul_sum]
    apply sum_le_sum
    intro j hj
    exact mul_le_mul_of_nonneg_right (hcoeff j (mem_range.mp hj))
      (pow_nonneg (v.nonneg z) _)
  by_contra! hbound
  by_cases hA0 : A = 0
  · have hr : 0 < v z := by linarith
    rw [hA0, zero_mul] at hsum
    exact (not_le_of_gt (pow_pos hr _)) hsum
  have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hA0)
  have hr : 1 < v z := by linarith
  have hgeom := geom_sum_mul (v z) p.natDegree
  have hsum0 : 0 ≤ ∑ j ∈ range p.natDegree, v z ^ j :=
    sum_nonneg (fun j _ => pow_nonneg (v.nonneg z) j)
  have hA_le : A ≤ v z - 1 := by linarith
  have hle := mul_le_mul_of_nonneg_right hA_le hsum0
  rw [mul_comm (v z - 1), hgeom] at hle
  linarith

/-- The maximum of the normalized lower coefficients; positive degree makes
its indexing set nonempty. -/
def coefficientRatioMax (v : AbsoluteValue K F) (p : K[X]) (hn : 0 < p.natDegree) : F :=
  (range p.natDegree).sup' (nonempty_range_iff.mpr (Nat.ne_of_gt hn))
    (fun j => v (p.coeff j / p.leadingCoeff))

omit [IsStrictOrderedRing F] in
theorem coefficientRatio_le_max (v : AbsoluteValue K F) (p : K[X])
    (hn : 0 < p.natDegree) {j : ℕ} (hj : j < p.natDegree) :
    v (p.coeff j / p.leadingCoeff) ≤ coefficientRatioMax v p hn :=
  Finset.le_sup' (fun j => v (p.coeff j / p.leadingCoeff)) (mem_range.mpr hj)

omit [IsStrictOrderedRing F] in
theorem coefficientRatioMax_nonneg (v : AbsoluteValue K F) (p : K[X])
    (hn : 0 < p.natDegree) : 0 ≤ coefficientRatioMax v p hn :=
  (v.nonneg _).trans (coefficientRatio_le_max v p hn hn)

/-- The strict bound displayed as `polynomial:eq:cauchybound`. -/
theorem root_lt_cauchy_bound (v : AbsoluteValue K F) (p : K[X])
    (hn : 0 < p.natDegree) {z : K} (hz : p.IsRoot z) :
    v z < 1 + coefficientRatioMax v p hn :=
  root_lt_one_add_of_coeff_le v p (ne_zero_of_natDegree_gt hn) hz
    (coefficientRatioMax_nonneg v p hn) (fun _ hj => coefficientRatio_le_max v p hn hj)

/-- Vanishing of every lower coefficient-ratio forces every root to be zero. -/
theorem root_eq_zero_of_coefficientRatioMax_eq_zero (v : AbsoluteValue K F) (p : K[X])
    (hn : 0 < p.natDegree) {z : K} (hz : p.IsRoot z)
    (hmax : coefficientRatioMax v p hn = 0) : z = 0 := by
  have hroot := root_power_le_sum v p (ne_zero_of_natDegree_gt hn) hz
  have hcoeff (j : ℕ) (hj : j ∈ range p.natDegree) :
      v (p.coeff j / p.leadingCoeff) = 0 := by
    apply le_antisymm _ (v.nonneg _)
    simpa [hmax] using coefficientRatio_le_max v p hn (mem_range.mp hj)
  have hsum : (∑ j ∈ range p.natDegree,
      v (p.coeff j / p.leadingCoeff) * v z ^ j) = 0 :=
    sum_eq_zero (fun j hj => by rw [hcoeff j hj, zero_mul])
  rw [hsum] at hroot
  apply v.eq_zero.mp
  exact (eq_zero_of_pow_eq_zero (le_antisymm hroot (pow_nonneg (v.nonneg z) _)))

/-- The strict lower Cauchy bound with any common bound on the nonconstant
coefficient ratios relative to the constant coefficient. -/
theorem inv_one_add_lt_root_of_coeff_le (v : AbsoluteValue K F) (p : K[X])
    (h₀ : p.coeff 0 ≠ 0) {z : K} (hz : p.IsRoot z) {B : F} (hB : 0 ≤ B)
    (hcoeff : ∀ j, 1 ≤ j → j ≤ p.natDegree → v (p.coeff j / p.coeff 0) ≤ B) :
    (1 + B)⁻¹ < v z := by
  have hp : p ≠ 0 := by intro h; simp [h] at h₀
  have hz0 : z ≠ 0 := by
    intro h
    exact h₀ (by simpa [coeff_zero_eq_eval_zero, IsRoot.def, h] using hz)
  have htrail : p.natTrailingDegree = 0 := natTrailingDegree_eq_zero.mpr (Or.inr h₀)
  have hdeg : p.reverse.natDegree = p.natDegree := by simp [reverse_natDegree, htrail]
  have hlc : p.reverse.leadingCoeff = p.coeff 0 := by
    simp [reverse_leadingCoeff, trailingCoeff, htrail]
  have hrev : p.reverse.IsRoot z⁻¹ := by
    letI := invertibleOfNonzero hz0
    simpa [IsRoot.def, invOf_eq_inv, eval₂_id] using
      (eval₂_reverse_eq_zero_iff (RingHom.id K) z p).mpr (by simpa using hz)
  have hb := root_lt_one_add_of_coeff_le v p.reverse
    (by simpa using hp) hrev hB (fun j hj => by
      rw [hdeg] at hj
      rw [hlc, coeff_reverse, revAt_le (Nat.le_of_lt hj)]
      exact hcoeff _ (by omega) (Nat.sub_le _ _))
  rw [map_inv₀] at hb
  exact inv_lt_of_inv_lt₀ (v.pos hz0) hb

/-- The maximum in the reciprocal Cauchy bound, indexed exactly by `1 ≤ j ≤ n`. -/
def reciprocalCoefficientRatioMax (v : AbsoluteValue K F) (p : K[X])
    (hn : 0 < p.natDegree) : F :=
  (Icc 1 p.natDegree).sup' (nonempty_Icc.mpr hn)
    (fun j => v (p.coeff j / p.coeff 0))

/-- The reciprocal strict lower bound in `polynomial:prop:rootbounds`. -/
theorem reciprocal_cauchy_bound_lt_root (v : AbsoluteValue K F) (p : K[X])
    (hn : 0 < p.natDegree) (h₀ : p.coeff 0 ≠ 0) {z : K} (hz : p.IsRoot z) :
    (1 + reciprocalCoefficientRatioMax v p hn)⁻¹ < v z := by
  apply inv_one_add_lt_root_of_coeff_le v p h₀ hz
  · exact (v.nonneg _).trans
      (le_sup' (fun j => v (p.coeff j / p.coeff 0)) (mem_Icc.mpr ⟨hn, le_rfl⟩))
  · intro j hj₁ hjn
    exact le_sup' (fun j => v (p.coeff j / p.coeff 0)) (mem_Icc.mpr ⟨hj₁, hjn⟩)

/-- A radial coefficient-domination certificate implies the radius bound.
This proof only uses a finite two-variable geometric identity. -/
theorem root_le_two_mul_of_coeff_le_pow (v : AbsoluteValue K F) (p : K[X])
    (hp : p ≠ 0) {z : K} (hz : p.IsRoot z) {M : F} (hM : 0 ≤ M)
    (hcoeff : ∀ j < p.natDegree,
      v (p.coeff j / p.leadingCoeff) ≤ M ^ (p.natDegree - j)) :
    v z ≤ 2 * M := by
  let S := ∑ j ∈ range p.natDegree, v z ^ j * M ^ (p.natDegree - 1 - j)
  have hsum : v z ^ p.natDegree ≤ M * S := by
    apply (root_power_le_sum v p hp hz).trans
    simp only [S, mul_sum]
    apply sum_le_sum
    intro j hj
    have hjn := mem_range.mp hj
    calc
      v (p.coeff j / p.leadingCoeff) * v z ^ j ≤
          M ^ (p.natDegree - j) * v z ^ j :=
        mul_le_mul_of_nonneg_right (hcoeff j hjn) (pow_nonneg (v.nonneg z) j)
      _ = M * (v z ^ j * M ^ (p.natDegree - 1 - j)) := by
        rw [show p.natDegree - j = (p.natDegree - 1 - j) + 1 by omega, pow_succ]
        ring
  have hgeom : S * (v z - M) = v z ^ p.natDegree - M ^ p.natDegree :=
    geom_sum₂_mul (v z) M p.natDegree
  by_contra! hbound
  have hr : 0 < v z := lt_of_le_of_lt (by positivity : 0 ≤ 2 * M) hbound
  have hd : 0 < v z - M := by linarith
  have hmul := mul_le_mul_of_nonneg_right hsum hd.le
  rw [mul_assoc M S, hgeom] at hmul
  have hpow := pow_pos hr p.natDegree
  have hMpow := pow_nonneg hM p.natDegree
  nlinarith

section RealClosed

variable [IsRealClosed F]

/-- Nonnegative roots supply the fractional exponents used in the radial bound. -/
theorem exists_nonneg_pow_eq (x : F) (hx : 0 ≤ x) (n : ℕ) (hn : n ≠ 0) :
    ∃ r : F, 0 ≤ r ∧ r ^ n = x := by
  obtain ⟨r, hr⟩ := IsRealClosed.exists_eq_pow_of_nonneg hx hn
  refine ⟨|r|, abs_nonneg r, ?_⟩
  rw [← abs_pow, ← hr, abs_of_nonneg hx]

/-- The nonnegative `(n-j)`th root of the `j`th normalized coefficient modulus. -/
def radialCoefficientRoot (v : AbsoluteValue K F) (p : K[X]) (j : Fin p.natDegree) : F :=
  Classical.choose (exists_nonneg_pow_eq (v (p.coeff j / p.leadingCoeff)) (v.nonneg _)
    (p.natDegree - j) (Nat.ne_of_gt (Nat.sub_pos_of_lt j.isLt)))

theorem radialCoefficientRoot_nonneg (v : AbsoluteValue K F) (p : K[X])
    (j : Fin p.natDegree) : 0 ≤ radialCoefficientRoot v p j :=
  (Classical.choose_spec (exists_nonneg_pow_eq (v (p.coeff j / p.leadingCoeff))
    (v.nonneg _) (p.natDegree - j) (Nat.ne_of_gt (Nat.sub_pos_of_lt j.isLt)))).1

theorem radialCoefficientRoot_pow (v : AbsoluteValue K F) (p : K[X])
    (j : Fin p.natDegree) :
    radialCoefficientRoot v p j ^ (p.natDegree - j) = v (p.coeff j / p.leadingCoeff) :=
  (Classical.choose_spec (exists_nonneg_pow_eq (v (p.coeff j / p.leadingCoeff))
    (v.nonneg _) (p.natDegree - j) (Nat.ne_of_gt (Nat.sub_pos_of_lt j.isLt)))).2

/-- The finite maximum `max_{j<n} |a_j/a_n|^(1/(n-j))` from the source. -/
def radialCoefficientMax (v : AbsoluteValue K F) (p : K[X]) (hn : 0 < p.natDegree) : F :=
  univ.sup' ⟨⟨0, hn⟩, mem_univ _⟩ (radialCoefficientRoot v p)

theorem radialCoefficientRoot_le_max (v : AbsoluteValue K F) (p : K[X])
    (hn : 0 < p.natDegree) (j : Fin p.natDegree) :
    radialCoefficientRoot v p j ≤ radialCoefficientMax v p hn :=
  le_sup' (radialCoefficientRoot v p) (mem_univ j)

theorem radialCoefficientMax_nonneg (v : AbsoluteValue K F) (p : K[X])
    (hn : 0 < p.natDegree) : 0 ≤ radialCoefficientMax v p hn :=
  (radialCoefficientRoot_nonneg v p ⟨0, hn⟩).trans
    (radialCoefficientRoot_le_max v p hn ⟨0, hn⟩)

/-- The radial bound `|z| ≤ 2M` in `polynomial:prop:rootbounds`. -/
theorem root_le_two_mul_radialCoefficientMax (v : AbsoluteValue K F) (p : K[X])
    (hn : 0 < p.natDegree) {z : K} (hz : p.IsRoot z) :
    v z ≤ 2 * radialCoefficientMax v p hn := by
  apply root_le_two_mul_of_coeff_le_pow v p (ne_zero_of_natDegree_gt hn) hz
    (radialCoefficientMax_nonneg v p hn)
  intro j hj
  rw [← radialCoefficientRoot_pow v p ⟨j, hj⟩]
  exact pow_le_pow_left₀ (radialCoefficientRoot_nonneg v p ⟨j, hj⟩)
    (radialCoefficientRoot_le_max v p hn ⟨j, hj⟩) _

/-- The zero radial maximum case is included, without dividing by the maximum. -/
theorem root_eq_zero_of_radialCoefficientMax_eq_zero (v : AbsoluteValue K F) (p : K[X])
    (hn : 0 < p.natDegree) {z : K} (hz : p.IsRoot z)
    (hM : radialCoefficientMax v p hn = 0) : z = 0 := by
  have h := root_le_two_mul_radialCoefficientMax v p hn hz
  rw [hM, mul_zero] at h
  exact v.eq_zero.mp (le_antisymm h (v.nonneg z))

end RealClosed

end Surreal.FinitePolynomial

namespace Surreal.Complexify

open Polynomial Surreal.FinitePolynomial

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F] [IsRealClosed F]

/-- The strict Cauchy bound for the base-field-valued surcomplex modulus. -/
theorem modulus_root_lt_cauchy_bound (p : (Complexify F)[X])
    (hn : 0 < p.natDegree) {z : Complexify F} (hz : p.IsRoot z) :
    modulus z < 1 + coefficientRatioMax modulusAbsoluteValue p hn :=
  root_lt_cauchy_bound modulusAbsoluteValue p hn hz

/-- The reciprocal strict lower bound for the surcomplex modulus. -/
theorem reciprocal_cauchy_bound_lt_modulus_root (p : (Complexify F)[X])
    (hn : 0 < p.natDegree) (h₀ : p.coeff 0 ≠ 0) {z : Complexify F} (hz : p.IsRoot z) :
    (1 + reciprocalCoefficientRatioMax modulusAbsoluteValue p hn)⁻¹ < modulus z :=
  reciprocal_cauchy_bound_lt_root modulusAbsoluteValue p hn h₀ hz

/-- The radial bound for the surcomplex modulus, including a zero maximum. -/
theorem modulus_root_le_two_mul_radialCoefficientMax (p : (Complexify F)[X])
    (hn : 0 < p.natDegree) {z : Complexify F} (hz : p.IsRoot z) :
    modulus z ≤ 2 * radialCoefficientMax modulusAbsoluteValue p hn :=
  root_le_two_mul_radialCoefficientMax modulusAbsoluteValue p hn hz

end Surreal.Complexify
