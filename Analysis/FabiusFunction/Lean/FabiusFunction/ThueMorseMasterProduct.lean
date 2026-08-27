import FabiusFunction.ThueMorseDirichlet
import FabiusFunction.RealZPowProduct

/-!
# The two-parameter master product

The atlas's master product `G(a,b) = ∏ ((n+a)/(n+b))^(ε(n))`, in
logarithmic form: the sign-weighted log-series
`L(a,b) = ∑ ε(n)·log((n+a)/(n+b))` converges for all `a, b > 0` by
Dirichlet's test, is a cocycle in the parameters, and satisfies the
atlas's dyadic functional equation by even/odd interleaving.

* `mpLog` / `mpLimit` — the partial sums and their limit `L(a,b)`.
* `tendsto_mpLimit` — convergence.
* `mpLimit_self` / `mpLimit_symm` / `mpLimit_cocycle` — the cocycle
  identities of `thm:G-functional`.
* `mpLimit_dyadic` — **the dyadic functional equation**
  (`thm:G-functional`, logarithmic form):
  `L(a,b) = L(a/2,b/2) - L((a+1)/2,(b+1)/2)`.
* `tendsto_masterProduct` / `tendsto_masterProduct_affine` — the normalized
  product and its common nonzero affine scaling converge to `exp (L(a,b))`.
-/

set_option autoImplicit false

open Finset Filter Topology

namespace Fabius

/-- Partial sums of the master log-series. -/
noncomputable def mpLog (a b : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ range N, (thueMorseSign n : ℝ) *
    Real.log (((n : ℝ) + a) / ((n : ℝ) + b))

/-- The shifted log-ratio tends to zero. -/
private theorem tendsto_log_shift_ratio (a b : ℝ) (hb : 0 < b) :
    Tendsto (fun n : ℕ => Real.log (((n : ℝ) + a) / ((n : ℝ) + b)))
      atTop (𝓝 0) := by
  have hall : ∀ n : ℕ, ((n : ℝ) + a) / ((n : ℝ) + b) =
      1 + (a - b) / ((n : ℝ) + b) := by
    intro n
    have h0 : (0 : ℝ) < (n : ℝ) + b := by positivity
    field_simp
    ring
  simp only [hall]
  have h2 : Tendsto (fun n : ℕ => (a - b) / ((n : ℝ) + b)) atTop
      (𝓝 0) := by
    apply Tendsto.div_atTop tendsto_const_nhds
    exact tendsto_atTop_add_const_right _ b tendsto_natCast_atTop_atTop
  have h1 : Tendsto (fun n : ℕ => 1 + (a - b) / ((n : ℝ) + b)) atTop
      (𝓝 1) := by
    simpa using tendsto_const_nhds.add h2
  have h3 := ((Real.continuousAt_log
    (by norm_num : (1 : ℝ) ≠ 0)).tendsto).comp h1
  rw [Real.log_one] at h3
  exact h3

private theorem mpLog_cauchy_of_le (a b : ℝ) (hb : 0 < b)
    (hab : b ≤ a) :
    CauchySeq (mpLog a b) := by
  have ha : 0 < a := lt_of_lt_of_le hb hab
  have hform : mpLog a b = fun N => ∑ n ∈ range N,
      Real.log (((n : ℝ) + a) / ((n : ℝ) + b)) •
        (thueMorseSign n : ℝ) := by
    funext N
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [smul_eq_mul]
    ring
  rw [hform]
  refine Antitone.cauchySeq_series_mul_of_tendsto_zero_of_bounded
    ?_ (tendsto_log_shift_ratio a b hb) (b := 1)
    norm_sum_thueMorseSign_le_one
  intro p q hpq
  apply Real.log_le_log (by positivity)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hle : (p : ℝ) ≤ (q : ℝ) := Nat.cast_le.mpr hpq
  nlinarith

/-- The log-partials flip sign when the parameters swap. -/
private theorem mpLog_flip (a b : ℝ) :
    mpLog a b = fun N => -(mpLog b a N) := by
  funext N
  rw [mpLog, mpLog, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [show ((n : ℝ) + a) / ((n : ℝ) + b) =
      (((n : ℝ) + b) / ((n : ℝ) + a))⁻¹ from by rw [inv_div],
    Real.log_inv]
  ring

/-- Convergence of the master log-series. -/
theorem mpLog_cauchy (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    CauchySeq (mpLog a b) := by
  rcases le_total b a with h | h
  · exact mpLog_cauchy_of_le a b hb h
  · rw [mpLog_flip]
    exact (mpLog_cauchy_of_le b a ha h).neg

/-- The limit `L(a,b)` of the master log-series. -/
noncomputable def mpLimit (a b : ℝ) : ℝ := limUnder atTop (mpLog a b)

/-- **Convergence of the master log-series**: for `a, b > 0` the partial
sums `mpLog a b` converge to `L(a,b)`. -/
theorem tendsto_mpLimit (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Tendsto (mpLog a b) atTop (𝓝 (mpLimit a b)) := by
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete (mpLog_cauchy a b ha hb)
  rwa [mpLimit, hL.limUnder_eq]

/-- `L(a,a) = 0`. -/
theorem mpLimit_self (a : ℝ) (ha : 0 < a) : mpLimit a a = 0 := by
  have hzero : mpLog a a = fun _ => 0 := by
    funext N
    rw [mpLog]
    refine Finset.sum_eq_zero fun n _ => ?_
    have h0 : (0 : ℝ) < (n : ℝ) + a := by positivity
    rw [div_self h0.ne', Real.log_one, mul_zero]
  have h1 : Tendsto (mpLog a a) atTop (𝓝 0) := by
    rw [hzero]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique (tendsto_mpLimit a a ha ha) h1

/-- Antisymmetry: `L(b,a) = -L(a,b)`. -/
theorem mpLimit_symm (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    mpLimit b a = -mpLimit a b := by
  have h1 : Tendsto (mpLog b a) atTop (𝓝 (-mpLimit a b)) := by
    have h2 := (tendsto_mpLimit a b ha hb).neg
    refine h2.congr fun N => ?_
    have := congrFun (mpLog_flip b a) N
    rw [this]
  exact tendsto_nhds_unique (tendsto_mpLimit b a hb ha) h1

/-- The cocycle identity: `L(a,b) + L(b,c) = L(a,c)`. -/
theorem mpLimit_cocycle (a b c : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) :
    mpLimit a b + mpLimit b c = mpLimit a c := by
  have hpart : ∀ N, mpLog a b N + mpLog b c N = mpLog a c N := by
    intro N
    rw [mpLog, mpLog, mpLog, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [← mul_add,
      ← Real.log_mul (by positivity) (by positivity)]
    congr 2
    have h1 : ((n : ℝ) + b) ≠ 0 := by positivity
    field_simp
    try ring
  have h1 : Tendsto (fun N => mpLog a b N + mpLog b c N) atTop
      (𝓝 (mpLimit a b + mpLimit b c)) :=
    (tendsto_mpLimit a b ha hb).add (tendsto_mpLimit b c hb hc)
  have h2 : Tendsto (fun N => mpLog a b N + mpLog b c N) atTop
      (𝓝 (mpLimit a c)) := by
    refine (tendsto_mpLimit a c ha hc).congr fun N => (hpart N).symm
  exact tendsto_nhds_unique h1 h2

/-- Interleaving: `mpLog a b (2N)` splits dyadically. -/
private theorem mpLog_two_mul (a b : ℝ) (hb : 0 < b)
    (N : ℕ) :
    mpLog a b (2 * N) =
      mpLog (a / 2) (b / 2) N - mpLog ((a + 1) / 2) ((b + 1) / 2) N := by
  rw [mpLog, sum_range_two_mul]
  have hterm : ∀ j ∈ range N,
      ((thueMorseSign (2 * j) : ℝ) *
          Real.log ((((2 * j : ℕ) : ℝ) + a) / (((2 * j : ℕ) : ℝ) + b)) +
        (thueMorseSign (2 * j + 1) : ℝ) *
          Real.log ((((2 * j + 1 : ℕ) : ℝ) + a) /
            (((2 * j + 1 : ℕ) : ℝ) + b))) =
      (thueMorseSign j : ℝ) *
          Real.log (((j : ℝ) + a / 2) / ((j : ℝ) + b / 2)) -
        (thueMorseSign j : ℝ) *
          Real.log (((j : ℝ) + (a + 1) / 2) /
            ((j : ℝ) + (b + 1) / 2)) := by
    intro j _
    have hsign1 : (thueMorseSign (2 * j) : ℝ) =
        (thueMorseSign j : ℝ) := by
      exact_mod_cast congrArg (fun z : ℤ => (z : ℝ))
        (thueMorseSign_two_mul j)
    have hsign2 : (thueMorseSign (2 * j + 1) : ℝ) =
        -(thueMorseSign j : ℝ) := by
      have h := thueMorseSign_two_mul_add_one j
      push_cast [h]
      ring
    have hr1 : (((2 * j : ℕ) : ℝ) + a) / (((2 * j : ℕ) : ℝ) + b) =
        ((j : ℝ) + a / 2) / ((j : ℝ) + b / 2) := by
      have h1 : (((2 * j : ℕ) : ℝ) + b) ≠ 0 := by positivity
      have h2 : ((j : ℝ) + b / 2) ≠ 0 := by positivity
      rw [div_eq_div_iff h1 h2]
      push_cast
      ring
    have hr2 : (((2 * j + 1 : ℕ) : ℝ) + a) /
        (((2 * j + 1 : ℕ) : ℝ) + b) =
        ((j : ℝ) + (a + 1) / 2) / ((j : ℝ) + (b + 1) / 2) := by
      have h1 : (((2 * j + 1 : ℕ) : ℝ) + b) ≠ 0 := by positivity
      have h2 : ((j : ℝ) + (b + 1) / 2) ≠ 0 := by positivity
      rw [div_eq_div_iff h1 h2]
      push_cast
      ring
    rw [hsign1, hsign2, hr1, hr2]
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib]
  rfl

/-- **The dyadic functional equation** (`thm:G-functional`,
logarithmic form): `L(a,b) = L(a/2,b/2) - L((a+1)/2,(b+1)/2)`. -/
theorem mpLimit_dyadic (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    mpLimit a b =
      mpLimit (a / 2) (b / 2) - mpLimit ((a + 1) / 2) ((b + 1) / 2) := by
  have hdouble : Tendsto (fun N : ℕ => 2 * N) atTop atTop :=
    tendsto_atTop_mono (fun n => (by omega : n ≤ 2 * n)) tendsto_id
  have h1 : Tendsto (fun N => mpLog a b (2 * N)) atTop
      (𝓝 (mpLimit a b)) :=
    (tendsto_mpLimit a b ha hb).comp hdouble
  have h2 : Tendsto (fun N =>
      mpLog (a / 2) (b / 2) N - mpLog ((a + 1) / 2) ((b + 1) / 2) N)
      atTop (𝓝 (mpLimit (a / 2) (b / 2) -
        mpLimit ((a + 1) / 2) ((b + 1) / 2))) :=
    (tendsto_mpLimit _ _ (by linarith) (by linarith)).sub
      (tendsto_mpLimit _ _ (by linarith) (by linarith))
  refine tendsto_nhds_unique ?_ h2
  exact h1.congr fun N => mpLog_two_mul a b hb N

/-- The master product converges to `exp (L(a,b))`. -/
theorem tendsto_masterProduct (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun N => ∏ n ∈ range N,
      (((n : ℝ) + a) / ((n : ℝ) + b)) ^ (thueMorseSign n)) atTop
      (𝓝 (Real.exp (mpLimit a b))) :=
  tendsto_prod_zpow_of_tendsto_sum (fun N : ℕ => range N)
    (fun n : ℕ => ((n : ℝ) + a) / ((n : ℝ) + b)) thueMorseSign
    (fun n => by positivity) (tendsto_mpLimit a b ha hb)

/-- Common nonzero affine scaling leaves the master product unchanged: for
`s ≠ 0` and `a,b > 0`, the product with factors
`(s*n+s*a)/(s*n+s*b)` converges to `exp (L(a,b))`.  The scale may have
either sign. -/
theorem tendsto_masterProduct_affine (s a b : ℝ) (hs : s ≠ 0)
    (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun N => ∏ n ∈ range N,
      ((s * (n : ℝ) + s * a) / (s * (n : ℝ) + s * b)) ^
        (thueMorseSign n)) atTop
      (𝓝 (Real.exp (mpLimit a b))) := by
  refine (tendsto_masterProduct a b ha hb).congr fun N => ?_
  refine Finset.prod_congr rfl fun n _ => ?_
  congr 1
  rw [← mul_add, ← mul_add, mul_div_mul_left _ _ hs]

end Fabius
