import GRHArticle.SingularModuli.PadicExpSubstitution
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Topology.MetricSpace.Contracting

/-!
# Bijection of the two disks in the p-adic exponential substitution

The normalized exponential differs from the identity by a strict
contraction on the closed unit disk. Banach's fixed-point theorem then
gives an inverse at every point of that disk.
-/

namespace GRHArticle.SingularModuli

open scoped BigOperators NNReal ENNReal Topology

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

private theorem norm_inv_factorial_succ_le (k : ℕ) :
    ‖((k + 1).factorial : ℂ_[p])⁻¹‖ ≤ factorialGrowthBound p ^ k := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hnat : (p - 1) * padicValNat p (k + 1).factorial ≤ k :=
    Nat.lt_succ_iff.mp (sub_one_mul_padicValNat_factorial_lt_of_ne_zero p (by omega))
  have hreal : ((p - 1 : ℕ) : ℝ) * (padicValNat p (k + 1).factorial : ℝ) ≤ (k : ℝ) := by
    exact_mod_cast hnat
  rw [Nat.cast_sub hp.out.one_lt.le, Nat.cast_one, mul_comm] at hreal
  have hval : (padicValNat p (k + 1).factorial : ℝ) ≤ (k : ℝ) / ((p : ℝ) - 1) :=
    (le_div_iff₀ (sub_pos.mpr hp1)).mpr hreal
  rw [norm_inv, padicComplex_norm_natCast (k + 1).factorial (Nat.factorial_ne_zero _),
    zpow_neg, inv_inv, zpow_natCast, ← Real.rpow_natCast,
    factorialGrowthBound, ← Real.rpow_mul_natCast (by positivity : (0 : ℝ) ≤ p)]
  exact Real.rpow_le_rpow_of_exponent_le hp1.le
    (by simpa only [div_mul_eq_mul_div, one_mul] using hval)

private noncomputable def tailCoeff (b : ℂ_[p]) (k : ℕ) : ℂ_[p] :=
  b ^ (k + 1) / (((k + 2).factorial : ℕ) : ℂ_[p])

private noncomputable def normalizedExpTail (b y : ℂ_[p]) : ℂ_[p] :=
  ∑' k, tailCoeff b k * y ^ (k + 2)

private theorem norm_tailCoeff_le (b : ℂ_[p]) (k : ℕ) :
    ‖tailCoeff b k‖ ≤ (‖b‖ * factorialGrowthBound p) ^ (k + 1) := by
  rw [tailCoeff, div_eq_mul_inv, norm_mul, norm_pow, mul_pow]
  exact mul_le_mul_of_nonneg_left (norm_inv_factorial_succ_le (p := p) (k + 1))
    (pow_nonneg (norm_nonneg b) _)

private theorem summable_normalizedExpTail (b y : ℂ_[p])
    (hb : ‖b‖ * factorialGrowthBound p < 1) (hy : ‖y‖ ≤ 1) :
    Summable (fun k => tailCoeff b k * y ^ (k + 2)) := by
  let r := ‖b‖ * factorialGrowthBound p
  have h₀ : 0 ≤ r := mul_nonneg (norm_nonneg b) (factorialGrowthBound_pos p).le
  have hs : Summable (fun k : ℕ => r ^ k) := summable_geometric_of_lt_one h₀ hb
  apply (hs.mul_left r).of_norm_bounded
  intro k
  rw [norm_mul, norm_pow, ← pow_succ']
  exact (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg y) hy)).trans
    (norm_tailCoeff_le b k)

private theorem norm_pow_sub_pow_le (y z : ℂ_[p]) (hy : ‖y‖ ≤ 1) (hz : ‖z‖ ≤ 1)
    (k : ℕ) : ‖y ^ k - z ^ k‖ ≤ ‖y - z‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have heq : y ^ (k + 1) - z ^ (k + 1) = (y ^ k - z ^ k) * y + z ^ k * (y - z) := by
      rw [pow_succ, pow_succ]
      ring
    rw [heq]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right ih (norm_nonneg y)).trans
        (mul_le_of_le_one_right (norm_nonneg _) hy)
    · rw [norm_mul, norm_pow]
      exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg z) hz)

private theorem norm_normalizedExpTail_sub_le (b y z : ℂ_[p])
    (hb : ‖b‖ * factorialGrowthBound p < 1) (hy : ‖y‖ ≤ 1) (hz : ‖z‖ ≤ 1) :
    ‖normalizedExpTail b y - normalizedExpTail b z‖ ≤
      (‖b‖ * factorialGrowthBound p) * ‖y - z‖ := by
  let r := ‖b‖ * factorialGrowthBound p
  have h₀ : 0 ≤ r := mul_nonneg (norm_nonneg b) (factorialGrowthBound_pos p).le
  unfold normalizedExpTail
  rw [← (summable_normalizedExpTail b y hb hy).tsum_sub (summable_normalizedExpTail b z hb hz)]
  apply IsUltrametricDist.norm_tsum_le_of_forall_le
  intro k
  rw [← mul_sub, norm_mul]
  exact mul_le_mul ((norm_tailCoeff_le b k).trans (pow_le_of_le_one h₀ hb.le (by omega)))
    (norm_pow_sub_pow_le y z hy hz _) (norm_nonneg _) h₀

private theorem normalizedExpTail_zero (b : ℂ_[p]) : normalizedExpTail b 0 = 0 := by
  have hz (k : ℕ) : (0 : ℂ_[p]) ^ (k + 2) = 0 := zero_pow (by omega)
  simp [normalizedExpTail, hz]

private theorem norm_normalizedExpTail_le_one (b y : ℂ_[p])
    (hb : ‖b‖ * factorialGrowthBound p < 1) (hy : ‖y‖ ≤ 1) :
    ‖normalizedExpTail b y‖ ≤ 1 := by
  have bound := norm_normalizedExpTail_sub_le b y 0 hb hy (by simp)
  rw [normalizedExpTail_zero, sub_zero, sub_zero] at bound
  exact bound.trans (mul_le_one₀ hb.le (norm_nonneg _) hy)

/-- The normalized exponential whose linear term is the identity. -/
noncomputable def normalizedExp (b y : ℂ_[p]) : ℂ_[p] :=
  (NormedSpace.exp (b * y) - 1) / b

private theorem normalizedExp_eq_add_tail (b y : ℂ_[p]) (hb₀ : b ≠ 0)
    (hb : ‖b‖ * factorialGrowthBound p < 1) (hy : ‖y‖ ≤ 1) :
    normalizedExp b y = y + normalizedExpTail b y := by
  have hby : ‖b * y‖ * factorialGrowthBound p < 1 := by
    have hnorm : ‖b * y‖ ≤ ‖b‖ := by
      rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg b) hy
    exact (mul_le_mul_of_nonneg_right hnorm (factorialGrowthBound_pos p).le).trans_lt hb
  have hs := NormedSpace.expSeries_div_summable_of_mem_ball ℂ_[p] (b * y)
    (mem_exp_ball_of_geometric_ratio_lt_one hby)
  have hsum : NormedSpace.exp (b * y) = (1 + b * y) + b * normalizedExpTail b y := by
    rw [NormedSpace.exp_eq_tsum_div]
    dsimp only
    rw [← hs.sum_add_tsum_nat_add 2]
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    simp only [pow_zero, pow_one, Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, div_one]
    congr 1
    unfold normalizedExpTail
    rw [← (summable_normalizedExpTail b y hb hy).tsum_mul_left]
    apply tsum_congr
    intro k
    simp only [tailCoeff, mul_pow, div_eq_mul_inv]
    rw [show k + 2 = k + 1 + 1 by omega, pow_succ b]
    ring
  rw [normalizedExp, hsum]
  field_simp
  ring

/-- The normalized exponential is a bijection from the closed unit disk
onto itself whenever the scaling factor lies inside the exponential radius. -/
theorem normalizedExp_bijOn_unitBall (b : ℂ_[p]) (hb₀ : b ≠ 0)
    (hb : ‖b‖ * factorialGrowthBound p < 1) :
    Set.BijOn (normalizedExp b) {y | ‖y‖ ≤ 1} {y | ‖y‖ ≤ 1} := by
  refine ⟨?_, ?_, ?_⟩
  · intro y hy
    change ‖normalizedExp b y‖ ≤ 1
    rw [normalizedExp_eq_add_tail b y hb₀ hb hy]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le hy (norm_normalizedExpTail_le_one b y hb hy))
  · intro y hy z hz hEq
    rw [normalizedExp_eq_add_tail b y hb₀ hb hy, normalizedExp_eq_add_tail b z hb₀ hb hz] at hEq
    have hdiff : y - z = normalizedExpTail b z - normalizedExpTail b y := by
      calc
        _ = (y + normalizedExpTail b y) - (z + normalizedExpTail b z) +
            (normalizedExpTail b z - normalizedExpTail b y) := by ring
        _ = _ := by rw [hEq, sub_self, zero_add]
    by_contra hne
    have hpos : 0 < ‖y - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    have hbound := norm_normalizedExpTail_sub_le b z y hb hz hy
    rw [← hdiff, norm_sub_rev z y] at hbound
    exact (not_le_of_gt (mul_lt_of_lt_one_left hpos hb)) hbound
  · intro x hx
    let S : Set ℂ_[p] := {y | ‖y‖ ≤ 1}
    let r : ℝ≥0 := ⟨‖b‖ * factorialGrowthBound p,
      mul_nonneg (norm_nonneg b) (factorialGrowthBound_pos p).le⟩
    let f : ℂ_[p] → ℂ_[p] := fun y => x - normalizedExpTail b y
    have hS : IsComplete S := (isClosed_le continuous_norm continuous_const).isComplete
    have hmaps : Set.MapsTo f S S := by
      intro y hy
      change ‖x - normalizedExpTail b y‖ ≤ 1
      rw [sub_eq_add_neg]
      apply (IsUltrametricDist.norm_add_le_max _ _).trans
      rw [norm_neg]
      exact max_le hx (norm_normalizedExpTail_le_one b y hb hy)
    have hcontract : ContractingWith r (hmaps.restrict f S S) := by
      refine ⟨hb, LipschitzWith.of_dist_le_mul ?_⟩
      intro y z
      change dist (f y) (f z) ≤ (r : ℝ) * dist (y : ℂ_[p]) (z : ℂ_[p])
      rw [dist_eq_norm, dist_eq_norm]
      have heq : f y - f z = normalizedExpTail b z - normalizedExpTail b y := by
        dsimp [f]
        ring
      rw [heq, norm_sub_rev (y : ℂ_[p]) (z : ℂ_[p])]
      exact norm_normalizedExpTail_sub_le b z y hb z.2 y.2
    obtain ⟨y, hy, hfix, _, _⟩ := hcontract.exists_fixedPoint' hS hmaps
      (x := (0 : ℂ_[p])) (by simp [S]) (edist_ne_top _ _)
    refine ⟨y, hy, ?_⟩
    rw [normalizedExp_eq_add_tail b y hb₀ hb hy]
    change x - normalizedExpTail b y = y at hfix
    exact (sub_eq_iff_eq_add.mp hfix).symm

/-- The original substitution identifies the closed unit disk with the
multiplicative disk around a of relative norm at most ‖b‖. -/
theorem expSubstitution_bijOn_unitBall (a b : ℂ_[p]) (ha : a ≠ 0) (hb₀ : b ≠ 0)
    (hb : ‖b‖ * factorialGrowthBound p < 1) :
    Set.BijOn (fun y : ℂ_[p] => a * NormedSpace.exp (b * y))
      {y | ‖y‖ ≤ 1} {x | ‖x / a - 1‖ ≤ ‖b‖} := by
  have hbij := normalizedExp_bijOn_unitBall b hb₀ hb
  have hbpos : 0 < ‖b‖ := norm_pos_iff.mpr hb₀
  have hpair (y : ℂ_[p]) : ((a * NormedSpace.exp (b * y)) / a - 1) / b = normalizedExp b y := by
    rw [normalizedExp]
    congr 2
    field_simp
  refine ⟨?_, ?_, ?_⟩
  · intro y hy
    change ‖(a * NormedSpace.exp (b * y)) / a - 1‖ ≤ ‖b‖
    have h := hbij.mapsTo hy
    change ‖normalizedExp b y‖ ≤ 1 at h
    rw [← hpair, norm_div, div_le_iff₀ hbpos, one_mul] at h
    exact h
  · intro y hy z hz hEq
    apply hbij.injOn hy hz
    change a * NormedSpace.exp (b * y) = a * NormedSpace.exp (b * z) at hEq
    rw [← hpair, ← hpair, hEq]
  · intro x hx
    change ‖x / a - 1‖ ≤ ‖b‖ at hx
    let y₀ := (x / a - 1) / b
    have htarget : y₀ ∈ ({y : ℂ_[p] | ‖y‖ ≤ 1} : Set ℂ_[p]) := by
      change ‖(x / a - 1) / b‖ ≤ 1
      rw [norm_div, div_le_iff₀ hbpos, one_mul]
      exact hx
    obtain ⟨y, hy, hEq⟩ := hbij.surjOn htarget
    refine ⟨y, hy, ?_⟩
    change normalizedExp b y = (x / a - 1) / b at hEq
    have hh := (div_left_inj' hb₀).mp ((hpair y).trans hEq)
    have hi : (a * NormedSpace.exp (b * y)) / a = x / a :=
      sub_left_injective hh
    exact (div_left_inj' ha).mp hi

end GRHArticle.SingularModuli
