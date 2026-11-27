import GRHArticle.ProgressionFree.PolynomialSmoothSeries
import GRHArticle.ProgressionFree.PolynomialCoefficientConcentration

/-!
# Moments of the tilted product of polynomial degree series

The degree of a product is additive. Expanding the first two moments of
the Cauchy product adds the normalized means and variances of its factors.
-/

namespace GRHArticle.ProgressionFree

open scoped BigOperators

/-- Evaluated contribution of the degree-`n` coefficient. -/
noncomputable def tiltedDegreeTerm (H : PowerSeries ℕ) (z : ℝ) (n : ℕ) : ℝ :=
  (PowerSeries.coeff (R := ℕ) n H : ℝ) * z ^ n

/-- The sums of the tilted coefficients and their first and second raw moments,
written in terms of the normalized mean and variance. -/
structure HasTiltedDegreeMoments (H : PowerSeries ℕ) (z m μ v : ℝ) : Prop where
  mass : HasSum (tiltedDegreeTerm H z) m
  first : HasSum (fun n ↦ tiltedDegreeTerm H z n * n) (m*μ)
  second : HasSum (fun n ↦ tiltedDegreeTerm H z n * (n:ℝ)^2) (m*(v+μ^2))

private def conv (a b : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n+1), a k * b (n-k)

private theorem hasSum_conv {a b : ℕ → ℝ} {x y : ℝ} (ha : HasSum a x) (hb : HasSum b y) :
    HasSum (conv a b) (x*y) := by
  unfold conv
  rw [← ha.tsum_eq, ← hb.tsum_eq]
  exact hasSum_sum_range_mul_of_summable_norm ha.summable.norm hb.summable.norm

private theorem tiltedDegreeTerm_mul (H G : PowerSeries ℕ) (z : ℝ) (n : ℕ) :
    tiltedDegreeTerm (H*G) z n = conv (tiltedDegreeTerm H z) (tiltedDegreeTerm G z) n := by
  unfold conv tiltedDegreeTerm
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Nat.cast_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hpow : z^n = z^k*z^(n-k) := by rw [← pow_add, Nat.add_sub_of_le hkn]
  rw [Nat.cast_mul, hpow]
  ring

theorem hasTiltedDegreeMoments_mul {H G : PowerSeries ℕ} {z m μ v m' μ' v' : ℝ}
    (h : HasTiltedDegreeMoments H z m μ v) (g : HasTiltedDegreeMoments G z m' μ' v') :
    HasTiltedDegreeMoments (H*G) z (m*m') (μ+μ') (v+v') := by
  constructor
  · exact (hasSum_conv h.mass g.mass).congr_fun (tiltedDegreeTerm_mul H G z)
  · have hx := (hasSum_conv h.first g.mass).add (hasSum_conv h.mass g.first)
    rw [show m*m'*(μ+μ') = m*μ*m'+m*(m'*μ') by ring]
    apply hx.congr_fun
    intro n
    simp only [tiltedDegreeTerm_mul, conv, Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [Nat.cast_sub hk']
    ring
  · have hx := ((hasSum_conv h.second g.mass).add ((hasSum_conv h.first g.first).mul_left 2)).add
      (hasSum_conv h.mass g.second)
    rw [show m*m'*(v+v'+(μ+μ')^2) = m*(v+μ^2)*m' + 2*((m*μ)*(m'*μ')) + m*(m'*(v'+μ'^2)) by ring]
    apply hx.congr_fun
    intro n
    simp only [tiltedDegreeTerm_mul, conv, Finset.sum_mul, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [Nat.cast_sub hk']
    ring

theorem hasTiltedDegreeMoments_one (z : ℝ) : HasTiltedDegreeMoments 1 z 1 0 0 := by
  have he (n : ℕ) : tiltedDegreeTerm 1 z n = if n=0 then 1 else 0 := by
    by_cases hn : n = 0 <;> simp [tiltedDegreeTerm, PowerSeries.coeff_one, hn]
  constructor
  · exact (hasSum_ite_eq 0 (1:ℝ)).congr_fun he
  · convert (hasSum_zero : HasSum (fun _ : ℕ ↦ (0:ℝ)) 0) using 1
    · funext n
      by_cases hn : n=0 <;> simp [he, hn]
    · ring
  · convert (hasSum_zero : HasSum (fun _ : ℕ ↦ (0:ℝ)) 0) using 1
    · funext n
      by_cases hn : n=0 <;> simp [he, hn]
    · ring

/-- Read the actual mass, mean and variance off the three convergent moment sums. -/
theorem HasTiltedDegreeMoments.normalized {H : PowerSeries ℕ} {z m μ v : ℝ}
    (h : HasTiltedDegreeMoments H z m μ v) (hm : m ≠ 0) :
    let A (n : ℕ) := (PowerSeries.coeff (R := ℕ) n H : ℝ)
    coefficientMass z A = m ∧ coefficientMean z A = μ ∧ coefficientVariance z A = v ∧
      Summable (fun n ↦ coefficientWeight z A n * n) ∧
      Summable (fun n ↦ coefficientWeight z A n * ((n:ℝ) - coefficientMean z A)^2) := by
  let A (n : ℕ) := (PowerSeries.coeff (R := ℕ) n H : ℝ)
  have hm' : coefficientMass z A = m := h.mass.tsum_eq
  have hw (n : ℕ) : coefficientWeight z A n = tiltedDegreeTerm H z n / m := by
    rw [coefficientWeight, hm']; rfl
  have hfirst : HasSum (fun n ↦ coefficientWeight z A n * n) μ := by
    have e : m*μ/m = μ := by field_simp [hm]
    rw [← e]
    apply (h.first.div_const m).congr_fun
    intro n; rw [hw]; ring
  have hμ : coefficientMean z A = μ := hfirst.tsum_eq
  have hv := ((h.second.sub (h.first.mul_right (2*μ))).add (h.mass.mul_right (μ^2))).div_const m
  have hvar : HasSum (fun n ↦ coefficientWeight z A n * ((n:ℝ)-coefficientMean z A)^2) v := by
    have e : (m*(v+μ^2)-m*μ*(2*μ)+m*μ^2)/m = v := by field_simp [hm]; ring
    rw [e] at hv
    apply hv.congr_fun
    intro n; rw [hw,hμ]; ring
  exact ⟨hm', hμ, hvar.tsum_eq, hfirst.summable, hvar.summable⟩

end GRHArticle.ProgressionFree
