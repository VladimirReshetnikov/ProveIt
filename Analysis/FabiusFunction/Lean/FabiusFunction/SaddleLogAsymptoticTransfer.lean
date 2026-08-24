import FabiusFunction.SaddleLogExpansionPowerSeries
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Log

/-!
# Logarithms of full Poincaré expansions

This module turns a real full expansion with constant coefficient one into
the corresponding full expansion of its logarithm.  The formal component
identifies `SaddleExpansion.logCoeff` with the coefficients of `logOf`, then
proves that the finite Taylor-polynomial discrepancy is divisible by `X^N`.

For parameter-dependent bounded coefficients, a small polynomial calculus
shows that evaluating this formal discrepancy is `O(scale^N)`.  The analytic
component supplies the logarithmic Taylor remainder and stability under an
`O(scale^N)` perturbation.  These pieces culminate in
`HasAsymptoticExpansion.real_log`.
-/

set_option autoImplicit false

open Filter Asymptotics Finset

namespace Fabius.SaddleExpansion

open PowerSeries

noncomputable section

variable {R : Type*} [CommRing R] [Algebra ℚ R]

def truncatedLogTaylorSeries (N : ℕ) (A : R⟦X⟧) : R⟦X⟧ :=
  ∑ j ∈ Finset.range N,
    PowerSeries.coeff j (PowerSeries.log R) • (A - 1) ^ j

omit [Algebra ℚ R] in
lemma coeff_pow_eq_zero_of_lt {u : R⟦X⟧}
    (hu : PowerSeries.constantCoeff u = 0) {k j : ℕ} (hkj : k < j) :
    PowerSeries.coeff k (u ^ j) = 0 := by
  apply PowerSeries.coeff_of_lt_order
  exact lt_of_lt_of_le (by exact_mod_cast hkj)
    (PowerSeries.le_order_pow_of_constantCoeff_eq_zero j hu)

theorem coeff_truncatedLogTaylorSeries_eq_logCoeff
    (a : ℕ → R) (ha0 : a 0 = 1) {N k : ℕ} (hk : k < N) :
    PowerSeries.coeff k (truncatedLogTaylorSeries N (massSeries a)) =
      logCoeff a k := by
  have hu : PowerSeries.HasSubst (massSeries a - 1) := by
    apply PowerSeries.HasSubst.of_constantCoeff_zero'
    simp [massSeries, ha0]
  rw [← coeff_logSeries, logSeries_eq_logOf a ha0,
    PowerSeries.logOf_eq, PowerSeries.coeff_subst' hu]
  have hu0 : PowerSeries.constantCoeff (massSeries a - 1) = 0 := by
    simp [massSeries, ha0]
  rw [finsum_eq_sum_of_support_subset (s := Finset.range N)]
  · unfold truncatedLogTaylorSeries
    simp only [map_sum, PowerSeries.coeff_smul]
  · intro j hj
    simp only [Function.mem_support] at hj
    by_contra hjrange
    have hjN : N ≤ j := Nat.le_of_not_gt fun hjlt => hjrange (Finset.mem_range.2 hjlt)
    apply hj
    rw [coeff_pow_eq_zero_of_lt hu0 (hk.trans_le hjN)]
    simp

def massPolynomial (a : ℕ → R) (N : ℕ) : Polynomial R :=
  ∑ k ∈ Finset.range N, Polynomial.monomial k (a k)

omit [Algebra ℚ R] in
theorem coeff_massPolynomial_of_lt (a : ℕ → R) {N k : ℕ} (hk : k < N) :
    (massPolynomial a N).coeff k = a k := by
  simp [massPolynomial, Polynomial.coeff_monomial, hk]

omit [Algebra ℚ R] in
theorem coeff_massPolynomial_of_ge (a : ℕ → R) {N k : ℕ} (hk : N ≤ k) :
    (massPolynomial a N).coeff k = 0 := by
  simp [massPolynomial, Polynomial.coeff_monomial, hk.not_gt]

def truncatedLogTaylorPolynomial (N : ℕ) (p : Polynomial R) : Polynomial R :=
  ∑ j ∈ Finset.range N,
    Polynomial.C (PowerSeries.coeff j (PowerSeries.log R)) * (p - 1) ^ j

theorem coe_truncatedLogTaylorPolynomial (N : ℕ) (p : Polynomial R) :
    (truncatedLogTaylorPolynomial N p : R⟦X⟧) =
      truncatedLogTaylorSeries N (p : R⟦X⟧) := by
  ext k
  simp [truncatedLogTaylorPolynomial, truncatedLogTaylorSeries,
    PowerSeries.coeff_log, Algebra.smul_def]
  apply Finset.sum_congr rfl
  intro j _hj
  by_cases hj0 : j = 0
  · simp [hj0]
  · simp only [hj0, ↓reduceIte]
    congr 1
    have hcoe : ((p - 1 : Polynomial R) : R⟦X⟧) = (p : R⟦X⟧) - 1 := by
      rw [Polynomial.coe_sub]
      simp
    rw [← hcoe, ← Polynomial.coe_pow, Polynomial.coeff_coe]

omit [Algebra ℚ R] in
theorem coe_massPolynomial (a : ℕ → R) (N : ℕ) :
    (massPolynomial a N : R⟦X⟧) =
      massSeries (fun j => (massPolynomial a N).coeff j) := by
  ext k
  simp [massSeries]

theorem coeff_truncatedLogTaylorPolynomial_mass_eq_logCoeff
    (a : ℕ → R) (ha0 : a 0 = 1) {N k : ℕ} (hk : k < N) :
    (truncatedLogTaylorPolynomial N (massPolynomial a N)).coeff k =
      logCoeff a k := by
  rw [← Polynomial.coeff_coe, coe_truncatedLogTaylorPolynomial,
    coe_massPolynomial,
    coeff_truncatedLogTaylorSeries_eq_logCoeff
      (fun j => (massPolynomial a N).coeff j)
      (by rw [coeff_massPolynomial_of_lt a (by omega)]; exact ha0) hk]
  apply logCoeff_congr k
  intro j hj
  exact coeff_massPolynomial_of_lt a (hj.trans_lt hk)

theorem X_pow_dvd_truncatedLogTaylorPolynomial_sub_logPolynomial
    (a : ℕ → R) (ha0 : a 0 = 1) (N : ℕ) :
    Polynomial.X ^ N ∣
      truncatedLogTaylorPolynomial N (massPolynomial a N) -
        ∑ k ∈ Finset.range N, Polynomial.monomial k (logCoeff a k) := by
  rw [Polynomial.X_pow_dvd_iff]
  intro k hk
  rw [Polynomial.coeff_sub,
    coeff_truncatedLogTaylorPolynomial_mass_eq_logCoeff a ha0 hk]
  simp [Polynomial.coeff_monomial, hk]

end

end Fabius.SaddleExpansion

namespace Fabius.SaddleExpansion

noncomputable section

open scoped BigOperators Topology

section AnalyticTransfer

variable {α : Type*} {l : Filter α}

/-- Every coefficient of a polynomial over parameter-dependent real
functions is bounded along `l`. -/
def HasBoundedPolynomialCoefficients
    (l : Filter α) (p : Polynomial (α → ℝ)) : Prop :=
  ∀ n, (p.coeff n) =O[l] (fun _ : α => (1 : ℝ))

theorem HasBoundedPolynomialCoefficients.add
    {p q : Polynomial (α → ℝ)}
    (hp : HasBoundedPolynomialCoefficients l p)
    (hq : HasBoundedPolynomialCoefficients l q) :
    HasBoundedPolynomialCoefficients l (p + q) := by
  intro n
  rw [Polynomial.coeff_add]
  exact (hp n).add (hq n)

theorem HasBoundedPolynomialCoefficients.neg
    {p : Polynomial (α → ℝ)} (hp : HasBoundedPolynomialCoefficients l p) :
    HasBoundedPolynomialCoefficients l (-p) := by
  intro n
  rw [Polynomial.coeff_neg]
  exact (hp n).neg_left

theorem HasBoundedPolynomialCoefficients.sub
    {p q : Polynomial (α → ℝ)}
    (hp : HasBoundedPolynomialCoefficients l p)
    (hq : HasBoundedPolynomialCoefficients l q) :
    HasBoundedPolynomialCoefficients l (p - q) := by
  rw [sub_eq_add_neg]
  exact hp.add hq.neg

theorem hasBoundedPolynomialCoefficients_C
    {c : α → ℝ} (hc : c =O[l] (fun _ : α => (1 : ℝ))) :
    HasBoundedPolynomialCoefficients l (Polynomial.C c) := by
  intro n
  by_cases hn : n = 0
  · subst n
    simpa using hc
  · rw [Polynomial.coeff_C, if_neg hn]
    exact isBigO_zero (fun _ : α => (1 : ℝ)) l

theorem hasBoundedPolynomialCoefficients_X :
    HasBoundedPolynomialCoefficients l
      (Polynomial.X : Polynomial (α → ℝ)) := by
  intro n
  by_cases hn : 1 = n
  · subst n
    simpa using isBigO_const_one ℝ (1 : ℝ) l
  · rw [Polynomial.coeff_X, if_neg hn]
    exact isBigO_zero (fun _ : α => (1 : ℝ)) l

theorem HasBoundedPolynomialCoefficients.mul
    {p q : Polynomial (α → ℝ)}
    (hp : HasBoundedPolynomialCoefficients l p)
    (hq : HasBoundedPolynomialCoefficients l q) :
    HasBoundedPolynomialCoefficients l (p * q) := by
  intro n
  rw [Polynomial.coeff_mul]
  have hsum :
      (fun x => ∑ ij ∈ Finset.antidiagonal n,
        p.coeff ij.1 x * q.coeff ij.2 x) =O[l]
          (fun _ : α => (1 : ℝ)) := by
    apply IsBigO.sum
    intro ij hij
    simpa only [one_mul] using (hp ij.1).mul (hq ij.2)
  apply hsum.congr'
  · filter_upwards with x
    simp
  · rfl

theorem HasBoundedPolynomialCoefficients.pow
    {p : Polynomial (α → ℝ)}
    (hp : HasBoundedPolynomialCoefficients l p) :
    ∀ n, HasBoundedPolynomialCoefficients l (p ^ n)
  | 0 => by
      rw [pow_zero, ← Polynomial.C_1]
      exact
        hasBoundedPolynomialCoefficients_C
          (isBigO_const_one ℝ (1 : ℝ) l)
  | n + 1 => by
      rw [pow_succ]
      exact (hp.pow n).mul hp

theorem hasBoundedPolynomialCoefficients_sum
    {ι : Type*} (s : Finset ι) {p : ι → Polynomial (α → ℝ)}
    (hp : ∀ i ∈ s, HasBoundedPolynomialCoefficients l (p i)) :
    HasBoundedPolynomialCoefficients l (∑ i ∈ s, p i) := by
  induction s using Finset.cons_induction with
  | empty =>
      intro n
      simp only [Finset.sum_empty, Polynomial.coeff_zero]
      exact isBigO_zero (fun _ : α => (1 : ℝ)) l
  | cons i s hi ih =>
      rw [Finset.sum_cons hi]
      exact (hp i (Finset.mem_cons_self i s)).add
        (ih fun j hj => hp j (Finset.mem_cons_of_mem hj))

theorem logCoeff_isBigO_one
    {a : ℕ → α → ℝ}
    (ha : ∀ n, (a n) =O[l] (fun _ : α => (1 : ℝ))) :
    ∀ n, (logCoeff a n) =O[l] (fun _ : α => (1 : ℝ)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero =>
          rw [logCoeff_zero]
          exact isBigO_zero (fun _ : α => (1 : ℝ)) l
      | succ n =>
          have hsum :
              (fun x => ∑ j ∈ Finset.range n,
                ((n - j : ℕ) : ℝ) * logCoeff a (n - j) x *
                  a (j + 1) x) =O[l]
                  (fun _ : α => (1 : ℝ)) := by
            apply IsBigO.sum
            intro j hj
            have hjlt : j < n := Finset.mem_range.1 hj
            have hlog := ih (n - j) (by omega)
            have hconst := isBigO_const_one ℝ ((n - j : ℕ) : ℝ) l
            simpa only [one_mul] using hconst.mul hlog |>.mul (ha (j + 1))
          have hscaled := hsum.const_mul_left
            ((((n + 1 : ℚ)⁻¹ : ℚ) : ℝ))
          rw [logCoeff_succ]
          apply (ha (n + 1)).sub
          simpa [Algebra.smul_def] using hscaled

theorem massPolynomial_hasBoundedCoefficients
    {a : ℕ → α → ℝ}
    (ha : ∀ n, (a n) =O[l] (fun _ : α => (1 : ℝ))) (N : ℕ) :
    HasBoundedPolynomialCoefficients l (massPolynomial a N) := by
  intro k
  by_cases hk : k < N
  · rw [coeff_massPolynomial_of_lt a hk]
    exact ha k
  · rw [coeff_massPolynomial_of_ge a (Nat.le_of_not_gt hk)]
    exact isBigO_zero (fun _ : α => (1 : ℝ)) l

theorem truncatedLogTaylorPolynomial_hasBoundedCoefficients
    {p : Polynomial (α → ℝ)}
    (hp : HasBoundedPolynomialCoefficients l p) (N : ℕ) :
    HasBoundedPolynomialCoefficients l
      (truncatedLogTaylorPolynomial N p) := by
  unfold truncatedLogTaylorPolynomial
  apply hasBoundedPolynomialCoefficients_sum
  intro j hj
  apply HasBoundedPolynomialCoefficients.mul
  · apply hasBoundedPolynomialCoefficients_C
    rw [PowerSeries.coeff_log]
    split_ifs
    · exact isBigO_const_one ℝ (0 : ℝ) l
    · exact isBigO_const_one ℝ _ l
  · exact (hp.sub (hasBoundedPolynomialCoefficients_C
      (isBigO_const_one ℝ (1 : ℝ) l))).pow j

theorem hasBoundedPolynomialCoefficients_monomial
    {c : α → ℝ} (hc : c =O[l] (fun _ : α => (1 : ℝ))) (n : ℕ) :
    HasBoundedPolynomialCoefficients l (Polynomial.monomial n c) := by
  rw [← Polynomial.C_mul_X_pow_eq_monomial]
  exact (hasBoundedPolynomialCoefficients_C hc).mul
    (hasBoundedPolynomialCoefficients_X.pow n)

theorem logPolynomial_hasBoundedCoefficients
    {a : ℕ → α → ℝ}
    (ha : ∀ n, (a n) =O[l] (fun _ : α => (1 : ℝ))) (N : ℕ) :
    HasBoundedPolynomialCoefficients l
      (∑ k ∈ Finset.range N, Polynomial.monomial k (logCoeff a k)) := by
  apply hasBoundedPolynomialCoefficients_sum
  intro k hk
  exact hasBoundedPolynomialCoefficients_monomial
    (logCoeff_isBigO_one ha k) k

theorem polynomial_eval₂_isBigO_one
    {p : Polynomial (α → ℝ)} {z : α → ℝ}
    (hp : HasBoundedPolynomialCoefficients l p)
    (hz : z =O[l] (fun _ : α => (1 : ℝ))) :
    (fun x => p.eval₂ (Pi.evalRingHom (fun _ : α => ℝ) x) (z x)) =O[l]
      (fun _ : α => (1 : ℝ)) := by
  have hsum :
      (fun x => ∑ k ∈ Finset.range (p.natDegree + 1),
        p.coeff k x * z x ^ k) =O[l] (fun _ : α => (1 : ℝ)) := by
    apply IsBigO.sum
    intro k hk
    simpa only [one_mul, one_pow] using (hp k).mul (hz.pow k)
  apply hsum.congr'
  · filter_upwards with x
    rw [Polynomial.eval₂_eq_sum_range]
    simp
  · rfl

def realLogTaylor (N : ℕ) (u : ℝ) : ℝ :=
  ∑ j ∈ Finset.range N,
    PowerSeries.coeff j (PowerSeries.log ℝ) * u ^ j

theorem eval₂_massPolynomial
    (a : ℕ → α → ℝ) (z : α → ℝ) (N : ℕ) (x : α) :
    (massPolynomial a N).eval₂
        (Pi.evalRingHom (fun _ : α => ℝ) x) (z x) =
      partialSum z a N x := by
  simp [massPolynomial, partialSum, Polynomial.eval₂_finsetSum,
    Polynomial.eval₂_monomial, smul_eq_mul, mul_comm]

theorem eval₂_truncatedLogTaylorPolynomial
    (p : Polynomial (α → ℝ)) (N : ℕ) (z : α → ℝ) (x : α) :
    (truncatedLogTaylorPolynomial N p).eval₂
        (Pi.evalRingHom (fun _ : α => ℝ) x) (z x) =
      realLogTaylor N
        (p.eval₂ (Pi.evalRingHom (fun _ : α => ℝ) x) (z x) - 1) := by
  unfold truncatedLogTaylorPolynomial realLogTaylor
  simp only [Polynomial.eval₂_finsetSum, Polynomial.eval₂_mul,
    Polynomial.eval₂_C, Polynomial.eval₂_pow, Polynomial.eval₂_sub,
    Polynomial.eval₂_one, PowerSeries.coeff_log]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hj0 : j = 0
  · simp [hj0]
  · simp only [hj0, ↓reduceIte]
    rfl

theorem eval₂_logPolynomial
    (a : ℕ → α → ℝ) (z : α → ℝ) (N : ℕ) (x : α) :
    (∑ k ∈ Finset.range N, Polynomial.monomial k (logCoeff a k)).eval₂
        (Pi.evalRingHom (fun _ : α => ℝ) x) (z x) =
      partialSum z (fun k x => logCoeff a k x) N x := by
  simp [partialSum, Polynomial.eval₂_finsetSum,
    Polynomial.eval₂_monomial, smul_eq_mul, mul_comm]

theorem formalLogRemainderEvaluation_isBigO
    {a : ℕ → α → ℝ} {z : α → ℝ}
    (ha : ∀ n, (a n) =O[l] (fun _ : α => (1 : ℝ)))
    (ha0 : a 0 = fun _ => 1)
    (hz : z =O[l] (fun _ : α => (1 : ℝ))) (N : ℕ) :
    (fun x => realLogTaylor N (partialSum z a N x - 1) -
      partialSum z (fun k x => logCoeff a k x) N x) =O[l]
        (fun x => z x ^ N) := by
  let D : Polynomial (α → ℝ) :=
    truncatedLogTaylorPolynomial N (massPolynomial a N) -
      ∑ k ∈ Finset.range N, Polynomial.monomial k (logCoeff a k)
  have hD : HasBoundedPolynomialCoefficients l D :=
    (truncatedLogTaylorPolynomial_hasBoundedCoefficients
      (massPolynomial_hasBoundedCoefficients ha N) N).sub
        (logPolynomial_hasBoundedCoefficients ha N)
  have hdvd : Polynomial.X ^ N ∣ D := by
    exact X_pow_dvd_truncatedLogTaylorPolynomial_sub_logPolynomial a ha0 N
  obtain ⟨q, hqD⟩ := hdvd
  have hq : HasBoundedPolynomialCoefficients l q := by
    intro k
    have hk := hD (k + N)
    rw [hqD, Polynomial.coeff_X_pow_mul] at hk
    exact hk
  have hevalq := polynomial_eval₂_isBigO_one hq hz
  have hscaled := (isBigO_refl (fun x => z x ^ N) l).mul hevalq
  apply hscaled.congr'
  · filter_upwards with x
    let ev := Pi.evalRingHom (fun _ : α => ℝ) x
    calc
      z x ^ N * q.eval₂ ev (z x) =
          (Polynomial.X ^ N).eval₂ ev (z x) * q.eval₂ ev (z x) := by simp
      _ = (Polynomial.X ^ N * q).eval₂ ev (z x) := by
        rw [Polynomial.eval₂_mul]
      _ = D.eval₂ ev (z x) := by rw [hqD]
      _ = realLogTaylor N (partialSum z a N x - 1) -
          partialSum z (fun k x => logCoeff a k x) N x := by
        rw [show D = truncatedLogTaylorPolynomial N (massPolynomial a N) -
          ∑ k ∈ Finset.range N,
            Polynomial.monomial k (logCoeff a k) by rfl,
          Polynomial.eval₂_sub, eval₂_truncatedLogTaylorPolynomial,
          eval₂_massPolynomial, eval₂_logPolynomial]
  · filter_upwards with x
    simp

theorem ofReal_realLogTaylor (N : ℕ) (u : ℝ) :
    (realLogTaylor N u : ℂ) = Complex.logTaylor N (u : ℂ) := by
  unfold realLogTaylor Complex.logTaylor
  push_cast
  apply Finset.sum_congr rfl
  intro j hj
  rw [PowerSeries.coeff_log]
  by_cases hj0 : j = 0
  · simp [hj0]
  · simp [hj0]
    ring

theorem realLog_sub_realLogTaylor_isBigO (N : ℕ) :
    (fun u : ℝ => Real.log (1 + u) - realLogTaylor N u) =O[𝓝 0]
      (fun u : ℝ => u ^ N) := by
  cases N with
  | zero =>
      have hconst : Tendsto (fun _ : ℝ => (1 : ℝ)) (𝓝 0) (𝓝 1) :=
        tendsto_const_nhds
      have hid : Tendsto (fun u : ℝ => u) (𝓝 0) (𝓝 0) := tendsto_id
      have hadd : Tendsto (fun u : ℝ => 1 + u) (𝓝 0) (𝓝 1) := by
        convert hconst.add hid using 1
        norm_num
      have ht : Tendsto (fun u : ℝ => Real.log (1 + u)) (𝓝 0) (𝓝 0) := by
        convert (Real.continuousAt_log one_ne_zero).tendsto.comp hadd using 1 <;>
          simp [Function.comp_def]
      simpa [realLogTaylor] using ht.isBigO_one ℝ
  | succ n =>
      have hc := (Complex.log_sub_logTaylor_isBigO n).comp_tendsto
        (Complex.continuous_ofReal.tendsto 0)
      have hcast :
          (fun u : ℝ => ((Real.log (1 + u) - realLogTaylor (n + 1) u : ℝ) : ℂ))
              =O[𝓝 0] (fun u : ℝ => ((u ^ (n + 1) : ℝ) : ℂ)) := by
        apply hc.congr'
        · filter_upwards [eventually_norm_sub_lt (0 : ℝ) one_pos] with u hu
          rw [sub_zero, Real.norm_eq_abs] at hu
          have hu_nonneg : 0 ≤ 1 + u := by
            rw [abs_lt] at hu
            linarith
          rw [Complex.ofReal_sub, Complex.ofReal_log hu_nonneg,
            Complex.ofReal_add, Complex.ofReal_one,
            ofReal_realLogTaylor]
          rfl
        · filter_upwards with u
          push_cast
          rfl
      exact Complex.isBigO_ofReal_right.mp
        (Complex.isBigO_ofReal_left.mp hcast)

theorem pow_sub_pow_isBigO_of_isBigO_one
    {u v r : α → ℝ}
    (huv : (fun x => u x - v x) =O[l] r)
    (hu : u =O[l] (fun _ : α => (1 : ℝ)))
    (hv : v =O[l] (fun _ : α => (1 : ℝ))) (n : ℕ) :
    (fun x => u x ^ n - v x ^ n) =O[l] r := by
  have hgeom :
      (fun x => ∑ i ∈ Finset.range n,
        u x ^ i * v x ^ (n - 1 - i)) =O[l]
          (fun _ : α => (1 : ℝ)) := by
    apply IsBigO.sum
    intro i hi
    simpa only [one_pow, one_mul] using
      (hu.pow i).mul (hv.pow (n - 1 - i))
  have hmul := huv.mul hgeom
  apply hmul.congr'
  · filter_upwards with x
    exact (Commute.all (u x) (v x)).mul_geom_sum₂ n
  · filter_upwards with x
    simp

theorem realLogTaylor_sub_isBigO
    {u v r : α → ℝ}
    (huv : (fun x => u x - v x) =O[l] r)
    (hu : u =O[l] (fun _ : α => (1 : ℝ)))
    (hv : v =O[l] (fun _ : α => (1 : ℝ))) (N : ℕ) :
    (fun x => realLogTaylor N (u x) - realLogTaylor N (v x)) =O[l] r := by
  have hsum :
      (fun x => ∑ j ∈ Finset.range N,
        PowerSeries.coeff j (PowerSeries.log ℝ) *
          (u x ^ j - v x ^ j)) =O[l] r := by
    apply IsBigO.sum
    intro j hj
    have hc := isBigO_const_one ℝ
      (PowerSeries.coeff j (PowerSeries.log ℝ)) l
    simpa only [one_mul] using hc.mul
      (pow_sub_pow_isBigO_of_isBigO_one huv hu hv j)
  apply hsum.congr'
  · filter_upwards with x
    unfold realLogTaylor
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  · rfl

/-- A full real Poincaré expansion with constant coefficient one is carried
by `Real.log` to the recursively generated logarithmic expansion. -/
theorem HasAsymptoticExpansion.real_log
    {scale f : α → ℝ} {coeff : ℕ → α → ℝ}
    (h : HasAsymptoticExpansion l scale f coeff)
    (hscale : Tendsto scale l (𝓝 0))
    (hcoeff0 : coeff 0 = fun _ => 1)
    (_hfpos : ∀ᶠ x in l, 0 < f x) :
    HasAsymptoticExpansion l scale (Real.log ∘ f)
      (fun k x => logCoeff (fun j => coeff j x) k) := by
  have hscaleO : scale =O[l] (fun _ : α => (1 : ℝ)) :=
    hscale.isBigO_one ℝ
  have hlogCoeff := logCoeff_isBigO_one h.1
  constructor
  · intro k
    apply (hlogCoeff k).congr'
    · filter_upwards with x
      exact logCoeff_apply coeff k x
    · rfl
  · intro N
    have hf1raw := h.remainder_isBigO 1
    have hf1 : (fun x => f x - 1) =O[l] scale := by
      apply hf1raw.congr'
      · filter_upwards with x
        simp [partialSum, hcoeff0]
      · filter_upwards with x
        simp
    have huTendsto : Tendsto (fun x => f x - 1) l (𝓝 0) :=
      hf1.trans_tendsto hscale
    have huOne : (fun x => f x - 1) =O[l] (fun _ : α => (1 : ℝ)) :=
      hf1.trans hscaleO
    have hrem := h.remainder_isBigO N
    have hscalePowOne : (fun x => scale x ^ N) =O[l]
        (fun _ : α => (1 : ℝ)) := by
      simpa only [one_pow] using hscaleO.pow N
    have hremOne :
        (fun x => f x - partialSum scale coeff N x) =O[l]
          (fun _ : α => (1 : ℝ)) :=
      hrem.trans hscalePowOne
    have hvOne :
        (fun x => partialSum scale coeff N x - 1) =O[l]
          (fun _ : α => (1 : ℝ)) := by
      apply (huOne.sub hremOne).congr'
      · filter_upwards with x
        ring
      · rfl
    have huv :
        (fun x => (f x - 1) - (partialSum scale coeff N x - 1)) =O[l]
          (fun x => scale x ^ N) := by
      apply hrem.congr'
      · filter_upwards with x
        ring
      · rfl
    have hTaylor :=
      (realLog_sub_realLogTaylor_isBigO N).comp_tendsto huTendsto
    have hA := hTaylor.trans (hf1.pow N)
    have hB := realLogTaylor_sub_isBigO huv huOne hvOne N
    have hC := formalLogRemainderEvaluation_isBigO h.1 hcoeff0 hscaleO N
    have htotal := hA.add hB |>.add hC
    apply htotal.congr'
    · filter_upwards with x
      have hpartial :
          partialSum scale (fun k x => logCoeff coeff k x) N x =
            partialSum scale
              (fun k x => logCoeff (fun j => coeff j x) k) N x := by
        unfold partialSum
        apply Finset.sum_congr rfl
        intro k hk
        change scale x ^ k • logCoeff coeff k x =
          scale x ^ k • logCoeff (fun j => coeff j x) k
        rw [logCoeff_apply]
      dsimp [Function.comp_def]
      rw [show 1 + (f x - 1) = f x by ring, hpartial]
      ring
    · rfl

end AnalyticTransfer

end

end Fabius.SaddleExpansion
