import Lib.Weil.Fock.Basic

/-!
# Moments on Fock space, approximation by polynomial vectors, bounds for functionals

The Fock space `New.Fock.fockSpace` consists of functions on ℂ^ι reproduced by the Gaussian. This
file defines weighted L¹ norms ∫ (1 + ‖y‖)^N |v y| dy on it, with values in [0, ∞], and proves
growth estimates that justify integrals and limits at the real places. Vectors whose moments are all
finite are approximated in all these norms by polynomial vectors. A functional controlled by its
differences under short Heisenberg translations is then bounded by moments.

## Main definitions and results

* `New.Fock.fockMoment`: the weighted L¹ norm ∫ (1 + ‖y‖)^N |v y| dy, with values in [0, ∞];
  `New.Exchange.IsSchwartzVector`: all these norms are finite (a Schwartz vector).
* `New.Fock.fockMoment_realHeisenbergOp_le`, `New.Fock.fockMoment_realWeil_le`,
  `New.Fock.fockMoment_integral_le`: bounds under the Heisenberg translations
  `New.Fock.realHeisenbergOp`, the Weil representation `New.Fock.realWeil`, and integrals of
  vectors.
* `New.Fock.fockMoment_polyVector_ne_top`, `New.Fock.exists_tendsto_fockMoment`: the vectors
  polynomial times Gaussian (`New.Fock.polyVector`) have finite norms, and approximate in all norms
  at once every vector whose norms are finite.
* `New.Fock.exists_norm_realHeisenbergOp_polyVector_le`: for a functional ℓ controlled by its
  differences under translations of size at most t ≤ 1, the value at the translate by z of a
  polynomial vector is at most C ‖ℓ‖ tᴺ (1 + ‖z‖)ᴺ.
* `New.Fock.exists_enorm_le_mul_fockMoment_of_norm_sub_le`: the bound ‖ℓ v‖ ≤ C ‖ℓ‖ tᴺ times the
  N-th moment of v, for every vector v.

Notions from other files:
* `New.Fock.fockSpace`: the Fock space of integrable functions c on ℂ^ι with c(x) = ∫ c(y) β(y,x)
  e(x−y) dy, where e is the Gaussian exp(−|x|²/2), under the L¹ norm.
* `New.Fock.realHeisenberg`: For signs ε, the Heisenberg datum on ℂ^ι given by the continuous
  unit-modulus bicharacter β(x,y) = exp((y*εx − x*εy)/2) = exp(i Im y*εx).
* `New.Fock.realHeisenbergOp` y: the Heisenberg translation c ↦ (z ↦ β(y,z) c(z − y)) on the Fock
  space.
* `New.Fock.vacVector`: the Gaussian `New.Fock.realVac` as a vector of the Fock space.
* `New.Fock.holomorphicCoord` ε x: the holomorphic coordinates of x, x̄ᵢ where εᵢ = 1 and xᵢ
  otherwise.

## Relation to the literature

Known; see `Lib.Weil.Fock.OscillatorPair` for sources.
-/

/-!
## Moments, Schwartz vectors and polynomial approximation

The common device: a vector v is the integral of the translates of the vacuum weighted by v.
-/

namespace New.Fock

open MeasureTheory Matrix Heisenberg.IsVacuum Norms.Operator Complex Filter Finset Real

variable {ι : Type _} [Fintype ι] [DecidableEq ι]
  {ε : ι → ℤˣ} (N : ℕ) (c : ℂ) (v : fockSpace ε)
  {Y : Type*} [MeasurableSpace Y] {ν : Measure Y} [SFinite ν] {F : Y → fockSpace ε}

/-! ### The weighted norms -/

/-- The moment `fockMoment N v` = ∫ (1 + ‖y‖)^N |v(y)| dy in [0, ∞], with ‖y‖ the sup norm and dy
Lebesgue measure divided by π^|ι|. -/
noncomputable def fockMoment : ENNReal := ∫⁻ y : ι → ℂ,
  (1 + ‖y‖ₑ) ^ N * ‖v y‖ₑ ∂normalizedVolume ι

private lemma integrable_fockVector (f : fockSpace ε) : Integrable (⇑f) (normalizedVolume ι) :=
  f.prop.1

private lemma enorm_eq_lintegral_enorm (f : fockSpace ε) :
    ‖f‖ₑ = ∫⁻ x : ι → ℂ, ‖f x‖ₑ ∂normalizedVolume ι := by
  rw [← ofReal_norm, Heisenberg.IsVacuum.norm_eq_integral_norm f,
    ofReal_integral_norm_eq_lintegral_enorm (integrable_fockVector f)]

/-- The moment of order 0 is the L¹ norm of the Fock vector `v`. -/
lemma fockMoment_zero : fockMoment 0 v = ‖v‖ₑ := by
  simp [fockMoment, enorm_eq_lintegral_enorm]

lemma fockMoment_smul : fockMoment N (c • v) = ‖c‖ₑ * fockMoment N v := by
  simp [fockMoment, mul_comm, ← lintegral_const_mul', ← mul_assoc]

lemma fockMoment_eq :
    fockMoment N v =
      ∫⁻ y : ι → ℂ, ENNReal.ofReal ((1 + ‖y‖) ^ N * ‖v y‖) ∂normalizedVolume ι := by
  simp (disch := bound) [fockMoment, ENNReal.ofReal_add]

/-- The Heisenberg translation by `y` multiplies the moment of order `N` by at most
`(1 + ‖y‖) ^ N`. -/
lemma fockMoment_realHeisenbergOp_le (y : ι → ℂ) :
    fockMoment N (realHeisenbergOp y v) ≤ (1 + ‖y‖ₑ) ^ N * fockMoment N v := by
  -- Substitute `x + y`: then `‖realHeisenbergOp y v (x + y)‖ = ‖v x‖`, and the weight is
  -- submultiplicative.
  have h_weight (x : ι → ℂ) : 1 + ‖x + y‖ₑ ≤ (1 + ‖y‖ₑ) * (1 + ‖x‖ₑ) := by
    grw [enorm_add_le]
    exact le_self_add.trans_eq (b := 1 + (‖x‖ₑ + ‖y‖ₑ) + ‖y‖ₑ * ‖x‖ₑ) (by ring)
  calc
    fockMoment N (realHeisenbergOp y v) = ∫⁻ x,
      (1 + ‖x + y‖ₑ) ^ N * ‖v x‖ₑ ∂normalizedVolume ι := by
      rw [fockMoment, ← lintegral_add_right_eq_self _ y]
      simp [← ofReal_norm, Heisenberg.norm_eq_one]
    _ ≤ ∫⁻ x, ((1 + ‖y‖ₑ) * (1 + ‖x‖ₑ)) ^ N * ‖v x‖ₑ ∂normalizedVolume ι := by
      gcongr with x
      exact h_weight x
    _ = (1 + ‖y‖ₑ) ^ N * fockMoment N v := by
      simp [fockMoment, mul_pow, mul_assoc, lintegral_const_mul']

/-- The Fock vector v is a Schwartz vector: all its moments `fockMoment N v` are finite. -/
def _root_.New.Exchange.IsSchwartzVector : Prop := ∀ N : ℕ, fockMoment N v ≠ ⊤

variable {v}

/-! ### Functionals, polynomial vectors and integrals -/

/-- A bounded functional `ℓ` that is at most `S (1 + ‖z‖)ᴺ` on the translate of the vacuum by `z`,
for all `z`, is at most `S` times the `N`-th moment on every vector `v`. The bound is stated in [0,
∞], so no finiteness is assumed. -/
lemma enorm_le_mul_fockMoment {S : ℝ} {ℓ : fockSpace ε →L[ℂ] ℂ}
    (h_bound : ∀ z : ι → ℂ, ‖ℓ (realHeisenbergOp z vacVector)‖ / (1 + ‖z‖) ^ N ≤ S) :
    ‖ℓ v‖ₑ ≤ ENNReal.ofReal S * fockMoment N v := by
  -- Write `ℓ v = ∫ v z • ℓ (realHeisenbergOp z vacVector)` and bound the integrand by `h_bound`.
  have h_le (z : ι → ℂ) : ‖ℓ (realHeisenbergOp z vacVector)‖ ≤ S * (1 + ‖z‖) ^ N :=
    (div_le_iff₀ (by positivity)).mp (h_bound z)
  calc
    ‖ℓ v‖ₑ ≤ ∫⁻ z, .ofReal ‖v z‖ * .ofReal (S * (1 + ‖z‖) ^ N) ∂normalizedVolume ι := by
      grw [map_eq_integral, enorm_integral_le_lintegral_enorm, ← h_le]
      simp
    _ = .ofReal S * fockMoment N v := by
      rw [fockMoment_eq, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      simp (disch := bound) [ENNReal.ofReal_mul', mul_comm, mul_left_comm]

/-- For every complex polynomial `P`, the polynomial vector `polyVector ε P` has finite moment of
every order `N`. Here `polyVector ε P` is x ↦ P(ζ(x)) exp(−|x|²/2), with ζ(x)ᵢ equal to x̄ᵢ where
`ε i = 1` and xᵢ otherwise. `fockMoment N c` = ∫ (1 + ‖y‖)^N |c(y)| dy, with ‖y‖ the sup norm and dy
Lebesgue measure divided by π^|ι|. -/
lemma fockMoment_polyVector_ne_top (P : MvPolynomial ι ℂ) :
    fockMoment N (polyVector ε P) ≠ ⊤ := by
  -- The integrand is at most `|C| * exp ((N + k) * ‖y‖) * ‖realVac y‖`, which is integrable.
  obtain ⟨k, C, h_eval⟩ : ∃ (k : ℕ) (C : ℝ), ∀ l : ι → ℂ,
      ‖MvPolynomial.eval l P‖ ≤ |C| * Real.exp (k * ‖l‖) := exists_norm_eval_le_exp P
  have h_int : Integrable (fun y : ι → ℂ ↦ |C| * (Real.exp ((N + k) * ‖y‖) * ‖realVac y‖))
      (normalizedVolume ι) :=
    (integrable_exp_mul_realVac _).const_mul _
  rw [fockMoment_eq, ← lt_top_iff_ne_top]
  refine lt_of_le_of_lt (lintegral_mono fun y ↦ ENNReal.ofReal_le_ofReal ?_) h_int.lintegral_lt_top
  -- Use `1 + ‖y‖ ≤ exp ‖y‖` and `‖holomorphicCoord ε y‖ = ‖y‖`.
  calc
    _ = (1 + ‖y‖) ^ N * ‖MvPolynomial.eval (holomorphicCoord ε y) P‖ * ‖realVac y‖ := by
      simp [← mul_assoc]
    _ ≤ Real.exp ‖y‖ ^ N * (|C| * Real.exp (k * ‖holomorphicCoord ε y‖)) * ‖realVac y‖ := by
      grw [h_eval, add_comm, add_one_le_exp]
    _ = |C| * (Real.exp ((N + k) * ‖y‖) * ‖realVac y‖) := by
      simp only [norm_holomorphicCoord, add_mul, Real.exp_add, Real.exp_nat_mul]
      ring

lemma isSchwartzVector_vacVector : Exchange.IsSchwartzVector (vacVector : fockSpace ε) := fun N ↦ by
  simpa only [polyVector_one] using fockMoment_polyVector_ne_top (ε := ε) N 1

/-- Minkowski's inequality for moments: for a family `F t` of Fock vectors over an s-finite measure
`ν`, the moment of the Bochner integral `∫ F t dν(t)` is at most the lower integral of the moments
`fockMoment N (F t)`. -/
lemma fockMoment_integral_le :
    fockMoment N (integral ν F) ≤ ∫⁻ t : Y, fockMoment N (F t) ∂ν := by
  by_cases hF : Integrable F ν
  · -- `F t y` is the value at `0` of `realHeisenbergOp (-y) (F t)`, which is jointly continuous in
    -- `y` and `F t`; hence it is jointly measurable in `t` and `y`.
    have h_cont : Continuous (Function.uncurry fun (y : ι → ℂ) (f : fockSpace ε) ↦
        valueAt (0 : ι → ℂ) (realHeisenbergOp (-y) f)) := by fun_prop
    have h_meas :
        AEStronglyMeasurable (fun p : Y × (ι → ℂ) ↦ F p.1 p.2) (ν.prod (normalizedVolume ι)) := by
      simpa using h_cont.comp_aestronglyMeasurable₂
        (aestronglyMeasurable_id (μ := normalizedVolume ι)).comp_snd
          hF.aestronglyMeasurable.comp_fst
    -- Evaluation at `y` commutes with the integral.
    have h_apply (y : ι → ℂ) : (∫ t, F t ∂ν) y = ∫ t, F t y ∂ν := by
      rw [← valueAt_apply y, ← ContinuousLinearMap.integral_comp_comm (valueAt y) hF]
      simp only [valueAt_apply]
    -- Then the triangle inequality and Tonelli (`measurability` uses `h_meas`).
    calc
      _ ≤ ∫⁻ y, (1 + ‖y‖ₑ) ^ N * ∫⁻ t, ‖F t y‖ₑ ∂ν ∂normalizedVolume ι := by
        simp only [fockMoment, h_apply]
        grw [enorm_integral_le_lintegral_enorm]
      _ = ∫⁻ y, ∫⁻ t, (1 + ‖y‖ₑ) ^ N * ‖F t y‖ₑ ∂ν ∂normalizedVolume ι :=
        lintegral_congr fun y ↦ (lintegral_const_mul' _ _ (by finiteness)).symm
      _ = _ := (lintegral_lintegral_swap (by measurability)).symm
  · simp [fockMoment, integral_undef hF]

/-- Let `F` be almost everywhere strongly measurable, with finite lower integral of every moment of
`F t`. Then `F` is Bochner integrable and its integral has all moments finite. -/
lemma isSchwartzVector_integral (hF_meas : AEStronglyMeasurable F ν)
    (h_fin : ∀ N : ℕ, ∫⁻ y : Y, fockMoment N (F y) ∂ν ≠ ⊤) :
    Integrable F ν ∧ Exchange.IsSchwartzVector (integral ν F) := by
  -- The moment of order 0 is the L¹ norm, so order 0 gives integrability.
  have h_int : Integrable F ν :=
    ⟨hF_meas, hasFiniteIntegral_iff_enorm.mpr (by simpa [fockMoment_zero] using (h_fin 0).lt_top)⟩
  exact ⟨h_int, fun N ↦ ne_top_of_le_ne_top (h_fin N) (fockMoment_integral_le N)⟩

/-- Let `F y` be Fock vectors (for signs `η` on `κ`) whose moment of order `N'` is at most
`C (1 + ‖y‖) ^ N`. Then `∫ fockMoment N' (v y • F y) dy` is at most `C` times the moment of order
`N` of `v`. -/
lemma lintegral_fockMoment_smul_le {κ : Type*} [Fintype κ] [DecidableEq κ] {η : κ → ℤˣ}
    {F : (ι → ℂ) → fockSpace (ι := κ) η} {N N' : ℕ} {C : ENNReal}
    (h_growth : ∀ y : ι → ℂ, fockMoment N' (F y) ≤ C * (1 + ‖y‖ₑ) ^ N) :
    ∫⁻ y : ι → ℂ, fockMoment N' (v y • F y) ∂normalizedVolume ι ≤ C * fockMoment N v := by
  calc
    _ ≤ ∫⁻ y : ι → ℂ, ‖v y‖ₑ * (C * (1 + ‖y‖ₑ) ^ N) ∂normalizedVolume ι := by
      simp only [fockMoment_smul]
      grw [h_growth]
    _ = C * fockMoment N v := by
      rw [fockMoment, ← lintegral_const_mul C (by fun_prop)]
      simp only [mul_comm, mul_left_comm]

/-! ### Approximation by polynomial vectors -/

omit [DecidableEq ι] in
/-- For reals s, t ≥ 0 and u in ℂ^ι with s ≤ (‖u‖ + 1)t, where ‖u‖ is the sup norm, the
Gaussian absorbs the factor: s^N · ‖realVac u‖ ≤ exp(N²) · t^N, where
‖realVac u‖ = exp(−Σ |u_i|² / 2). -/
lemma pow_mul_realVac_le {s t : ℝ} {u : ι → ℂ} (h_le_mul : s ≤ (‖u‖ + 1) * t) (hs_nonneg : 0 ≤ s)
    (ht_nonneg : 0 ≤ t) :
    s ^ N * ‖realVac u‖ ≤ Real.exp (N ^ 2) * t ^ N := by
  -- Use `‖u‖ + 1 ≤ exp ‖u‖`; the exponents compare because `‖u‖ ^ 2 ≤ (star u ⬝ᵥ u).re`.
  have h_exp : -(Star.star u ⬝ᵥ u).re / 2 + N * ‖u‖ ≤ N ^ 2 := by
    nlinarith [norm_sq_le_re_star_dotProduct_self u]
  grw [h_le_mul, add_one_le_exp, mul_comm, mul_pow, ← h_exp]
  simp [realVac, norm_exp, ← Real.exp_nsmul, ← mul_assoc, ← Real.exp_add]

/-- Gaussian domination of the Fock kernel: for `y, w` in ℂ^ι with sup norms,
`(1 + ‖w‖)^N · |e(w)| · |e(y)| · exp |Σᵢ conj(ζ(y)ᵢ) ζ(w)ᵢ| ≤ exp(N²) · (1 + ‖y‖)^N`. Here
`e = realVac` is the Gaussian x ↦ exp(−|x|²/2), and `ζ = holomorphicCoord ε` has i-th coordinate x̄ᵢ
if `ε i = 1` and xᵢ otherwise. So the kernel trades a polynomial weight in `w` for one in `y`. -/
lemma pow_mul_realVac_mul_realVac_mul_exp_le (y w : ι → ℂ) :
    (1 + ‖w‖) ^ N * (‖realVac w‖ * ‖realVac y‖ * rexp ‖Star.star (holomorphicCoord ε y) ⬝ᵥ
      holomorphicCoord ε w‖) ≤
      rexp (N ^ 2) * (1 + ‖y‖) ^ N := by
  -- Completing the square bounds the bracket by the Gaussian at `u`, `u i = ‖y i‖ - ‖w i‖`.
  let u : ι → ℂ := fun i ↦ ‖y i‖ - ‖w i‖
  -- In the coordinates, `‖realVac x‖ = exp (-∑ ‖x i‖² / 2)`, and `|ζ(y)* ζ(w)| ≤ ∑ ‖y i‖ ‖w i‖`.
  have h_norm_realVac (x : ι → ℂ) : ‖realVac x‖ = rexp (-(∑ i, ‖x i‖ ^ 2) / 2) := by
    simp [realVac, norm_exp, star_dotProduct_self_eq_sum, neg_div, -ofReal_pow]
  have h_s_le : ‖Star.star (holomorphicCoord ε y) ⬝ᵥ holomorphicCoord ε w‖ ≤ ∑ i,
    ‖y i‖ * ‖w i‖ := by
    grw [dotProduct, norm_sum_le]
    simp
  have h_norm_u (i : ι) : ‖u i‖ ^ 2 = (‖y i‖ - ‖w i‖) ^ 2 := by simp [u, ← ofReal_sub, sq_abs]
  have h_sum_u : ∑ i, ‖u i‖ ^ 2 =
      ∑ i, ‖w i‖ ^ 2 + ∑ i, ‖y i‖ ^ 2 - 2 * ∑ i, ‖y i‖ * ‖w i‖ := by
    simp only [h_norm_u, mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
    exact sum_congr rfl fun i _ ↦ by ring
  have h_sq :
      ‖realVac w‖ * ‖realVac y‖ * rexp ‖Star.star (holomorphicCoord ε y) ⬝ᵥ holomorphicCoord ε w‖ ≤
        ‖realVac u‖ := by
    simp only [h_norm_realVac, ← Real.exp_add, Real.exp_le_exp]
    linarith [h_s_le, h_sum_u]
  have h_tri : 1 + ‖w‖ ≤ (‖u‖ + 1) * (1 + ‖y‖) := by
    have h_norm_w_le : ‖w‖ ≤ ‖y‖ + ‖u‖ := by
      simpa [u, Pi.norm_def, ← ofReal_sub] using norm_le_insert (‖y ·‖) (‖w ·‖)
    nlinarith [norm_nonneg y, norm_nonneg u]
  grw [h_sq, pow_mul_realVac_le N h_tri (by positivity) (by positivity)]

/-- The monomial `∏ j, X (p j)` of a word `p : Fin k → ι`. -/
private noncomputable def prodX {k : ℕ} (p : Fin k → ι) : MvPolynomial ι ℂ := ∏ j, .X (p j)

/-- The `n`-th partial sum of the exponential series of the reproducing kernel, as an operator:
`∑_{k < n} (1 / k!) ∑_{p : Fin k → ι} ⟨w_p, ·⟩ w_p`, where `w_p` is the polynomial vector of
`prodX p`, and `⟨a, ·⟩` is the continuous linear functional `fockInner a`, linear in the second
slot. -/
private noncomputable def partialKernelOp (ε : ι → ℤˣ) (n : ℕ) : fockSpace ε →L[ℂ] fockSpace ε :=
  ∑ k ∈ range n, ∑ p : Fin k → ι,
    (k.factorial⁻¹ : ℂ) • (fockInner (polyVector ε (prodX p))).smulRight (polyVector ε (prodX p))

/-- The kernel of `1 - partialKernelOp ε n`: its value on the translate of the vacuum by `y`, at
`w`, is `e(w) e(y)` times the tail `exp s - ∑_{k < n} sᵏ / k!` of the exponential series at
`s = ζ(y)* ζ(w)`, with `e` the Gaussian and `ζ = holomorphicCoord ε`. Here it is multiplied by
`v y`. -/
private lemma smul_one_sub_partialKernelOp_apply (v : fockSpace ε) (n : ℕ) (y w : ι → ℂ) :
    (v y • (1 - partialKernelOp ε n) (realHeisenbergOp y vacVector)) w =
      v y * realVac w * realVac y *
        (NormedSpace.exp (Star.star (holomorphicCoord ε y) ⬝ᵥ holomorphicCoord ε w) -
          ∑ k ∈ range n, (Star.star (holomorphicCoord ε y) ⬝ᵥ holomorphicCoord ε w) ^ k /
            k.factorial) := by
  set s : ℂ := Star.star (holomorphicCoord ε y) ⬝ᵥ holomorphicCoord ε w with hs_def
  -- Pairing with the translate of the vacuum evaluates at `y` (`modelInner_heisenbergOp_vacElem`).
  have h_apply : (v y • (1 - partialKernelOp ε n) (realHeisenbergOp y vacVector)) w =
      v y * ((realHeisenbergOp y vacVector : fockSpace ε) w - ∑ k ∈ range n, ∑ p : Fin k → ι,
        (k.factorial : ℂ)⁻¹ * starRingEnd ℂ (polyVector ε (prodX p) y) *
          polyVector ε (prodX p) w) := by
    simp [partialKernelOp, ← conj_modelInner (realHeisenbergOp _ _),
      modelInner_heisenbergOp_vacElem, ← valueAt_apply, ← mul_assoc]
  -- A translate of the vacuum is two Gaussians times `exp s` (`beta_mul_realVac`).
  have h_translate : (realHeisenbergOp y vacVector : fockSpace ε) w =
      realVac w * realVac y * NormedSpace.exp s := by
    simp [hs_def, beta_mul_realVac, exp_eq_exp_ℂ]
  -- Pairing the vectors of the monomial of a word `p` gives two Gaussians times a product.
  have h_word {k : ℕ} (p : Fin k → ι) :
      starRingEnd ℂ (polyVector ε (prodX p) y) * polyVector ε (prodX p) w = realVac w *
        (realVac y *
          ∏ j, Star.star (holomorphicCoord ε y (p j)) * holomorphicCoord ε w (p j)) := by
    simp [prodX, (isVacuum_realVac (ε := ε)).conj_apply, prod_mul_distrib]
    ring
  -- Their sum over all words of length `k` is the multinomial expansion of `s ^ k`.
  have h_pow (k : ℕ) :
      ∑ p : Fin k → ι, ∏ j, Star.star (holomorphicCoord ε y (p j)) * holomorphicCoord ε w (p j) =
        s ^ k := by
    simp [hs_def, dotProduct, Fintype.sum_pow]
  have h_sum : ∑ k ∈ range n, ∑ p : Fin k → ι, (k.factorial : ℂ)⁻¹ *
      starRingEnd ℂ (polyVector ε (prodX p) y) * polyVector ε (prodX p) w =
        realVac w * realVac y * ∑ k ∈ range n, s ^ k / k.factorial := by
    rw [mul_sum]
    refine sum_congr rfl fun k _ ↦ ?_
    simp only [mul_assoc, h_word, ← mul_sum, h_pow]
    ring
  rw [h_apply, h_translate, h_sum]
  ring

/-- Domination of the partial sums: with `ζ = holomorphicCoord ε`, `e = realVac` the Gaussian and
`s = ζ(y)* ζ(w)`, the weighted `n`-th partial sum `(1 + ‖w‖)^N v(y) e(w) e(y) ∑_{k < n} sᵏ / k!` has
norm at most `exp((m + N)²) (1 + ‖y‖)^(m + N) |v(y)| (1 + ‖w‖)^(-m)`, for every `n` and `m`. -/
private lemma norm_smul_mul_sum_le (N m n : ℕ) (v : fockSpace ε) (y w : ι → ℂ) :
    ‖(1 + ‖w‖) ^ N • (v y * realVac w * realVac y *
        ∑ k ∈ range n, (Star.star (holomorphicCoord ε y) ⬝ᵥ holomorphicCoord ε w) ^ k /
          k.factorial)‖ ≤
      rexp ((m + N : ℕ) ^ 2) * ((1 + ‖y‖ₑ) ^ (m + N) * ‖v y‖ₑ).toReal *
        (1 + ‖w‖) ^ (-(m : ℝ)) := by
  set s : ℂ := Star.star (holomorphicCoord ε y) ⬝ᵥ holomorphicCoord ε w with hs_def
  have h_series : ‖∑ k ∈ range n, s ^ k / k.factorial‖ ≤ rexp ‖s‖ := by
    grw [norm_sum_le, ← sum_le_exp_of_nonneg (norm_nonneg _) n]
    simp
  calc
    _ ≤ (1 + ‖w‖) ^ N * (‖v y‖ * ‖realVac w‖ * ‖realVac y‖ * rexp ‖s‖) := by
      grw [norm_smul_of_nonneg (by positivity), norm_mul, h_series, norm_mul, norm_mul]
    _ = (1 + ‖w‖) ^ (m + N) * (‖realVac w‖ * ‖realVac y‖ * rexp ‖s‖) * ‖v y‖ /
        (1 + ‖w‖) ^ m := by field
    _ ≤ _ := by
      grw [hs_def, pow_mul_realVac_mul_realVac_mul_exp_le]
      simp [ENNReal.toReal_add, div_eq_mul_inv, ← mul_assoc]

/-- For a Fock vector `v` all of whose moments are finite, there is a single sequence of polynomials
`P n` such that `fockMoment N (v - polyVector ε (P n))` tends to 0 for every `N`. Here
`fockMoment N c` = ∫ (1 + ‖y‖)^N |c(y)| dy in [0, ∞], with ‖y‖ the sup norm on ℂ^ι and dy Lebesgue
measure divided by π^|ι|. `polyVector ε P` is the Fock vector x ↦ P(ζ(x)) exp(−|x|²/2), where ζ(x)ᵢ
is x̄ᵢ if `ε i = 1` and xᵢ if `ε i = -1`. -/
lemma exists_tendsto_fockMoment (hv : Exchange.IsSchwartzVector v) :
    ∃ P : ℕ → MvPolynomial ι ℂ, ∀ N : ℕ,
      Tendsto (fun n : ℕ ↦ fockMoment N (v - polyVector ε (P n))) atTop (nhds 0) := by
  -- The operator `partialKernelOp ε n` is the sum, over `k < n` and `p : Fin k → ι`, of `1 / k!`
  -- times the rank-one operator of the monomial `prodX p`. Its value at `v` is a polynomial
  -- vector, and `1 - partialKernelOp ε n` has as kernel two Gaussians times the tail of the
  -- exponential series, which tends to `0` dominatedly.
  -- `fun_prop` uses `h_cont` for the measurability of the integrands below.
  have h_cont : Continuous (realVac : (ι → ℂ) → ℂ) := (isVacuum_realVac (ε := ε)).cont
  let P (n : ℕ) : MvPolynomial ι ℂ := ∑ k ∈ range n, ∑ p : Fin k → ι,
    ((k.factorial⁻¹ : ℂ) * fockInner (polyVector ε (prodX p)) v) • prodX p
  have hP_eq (n : ℕ) : polyVector ε (P n) = partialKernelOp ε n v := by
    simp [P, partialKernelOp, smul_smul]
  refine ⟨P, fun N ↦ ?_⟩
  -- `G n` is the weighted integrand for the `n`-th partial sum of the series, `g` its limit.
  let s (p : (ι → ℂ) × (ι → ℂ)) : ℂ := Star.star (holomorphicCoord ε p.1) ⬝ᵥ holomorphicCoord ε p.2
  let G (n : ℕ) (p : (ι → ℂ) × (ι → ℂ)) : ℂ :=
    (1 + ‖p.2‖) ^ N • (v p.1 * realVac p.2 * realVac p.1 * ∑ k ∈ range n, s p ^ k / k.factorial)
  let g (p : (ι → ℂ) × (ι → ℂ)) : ℂ :=
    (1 + ‖p.2‖) ^ N • (v p.1 * realVac p.2 * realVac p.1 * NormedSpace.exp (s p))
  have h_le (n : ℕ) : fockMoment N (v - polyVector ε (P n)) ≤
      ∫⁻ p, .ofReal ‖G n p - g p‖ ∂(normalizedVolume ι).prod (normalizedVolume ι) :=
    calc
      _ = fockMoment N
          (∫ y, v y • (1 - partialKernelOp ε n) (realHeisenbergOp y vacVector)
            ∂normalizedVolume ι) := by
        rw [← map_eq_integral, hP_eq, _root_.sub_apply, one_apply_eq_self]
      _ ≤ ∫⁻ y, fockMoment N (v y • (1 - partialKernelOp ε n) (realHeisenbergOp y vacVector))
          ∂normalizedVolume ι :=
        fockMoment_integral_le N
      _ = ∫⁻ y, ∫⁻ w, .ofReal ((1 + ‖w‖) ^ N * ‖v y * realVac w * realVac y *
            (NormedSpace.exp (s (y, w)) - ∑ k ∈ range n, s (y, w) ^ k / k.factorial)‖)
            ∂normalizedVolume ι ∂normalizedVolume ι := by
        simp only [fockMoment_eq, smul_one_sub_partialKernelOp_apply, s]
      _ = _ := by
        rw [lintegral_prod _ (by fun_prop)]
        simp (disch := positivity) only [G, g, ← smul_sub, ← mul_sub, norm_smul, norm_mul,
          norm_sub_rev (NormedSpace.exp _), norm_of_nonneg]
  -- Dominated convergence for `G n → g`. With `m = (normalizedVolume ι).integrablePower` the weight
  -- `(1 + ‖p.2‖) ^ (-m)` is integrable.
  set m : ℕ := (normalizedVolume ι).integrablePower
  let bound (p : (ι → ℂ) × (ι → ℂ)) : ℝ :=
    rexp ((m + N : ℕ) ^ 2) * ((1 + ‖p.1‖ₑ) ^ (m + N) * ‖v p.1‖ₑ).toReal * (1 + ‖p.2‖) ^ (-(m : ℝ))
  have h_int_weight : Integrable (fun y : ι → ℂ ↦ ((1 + ‖y‖ₑ) ^ (m + N) * ‖v y‖ₑ).toReal)
      (normalizedVolume ι) :=
    integrable_toReal_of_lintegral_ne_top (by fun_prop) (hv (m + N))
  have h_int : Integrable bound ((normalizedVolume ι).prod (normalizedVolume ι)) :=
    (h_int_weight.const_mul _).mul_prod (normalizedVolume ι).integrable_pow_neg_integrablePower
  have h_dom (n : ℕ) (p : (ι → ℂ) × (ι → ℂ)) : ‖G n p‖ ≤ bound p :=
    norm_smul_mul_sum_le N m n v p.1 p.2
  have h_lim (p : (ι → ℂ) × (ι → ℂ)) : Tendsto (G · p) atTop (nhds (g p)) :=
    ((NormedSpace.expSeries_div_hasSum_exp (s p)).tendsto_sum_nat.const_mul _).const_smul _
  have h_tendsto : Tendsto
      (fun n : ℕ ↦ ∫⁻ p, .ofReal ‖G n p - g p‖ ∂(normalizedVolume ι).prod (normalizedVolume ι))
      atTop (nhds 0) :=
    tendsto_lintegral_norm_of_dominated_convergence (fun n ↦ by fun_prop) h_int.hasFiniteIntegral
      (fun n ↦ .of_forall (h_dom n)) (.of_forall h_lim)
  exact tendsto_nhds_bot_mono' h_tendsto h_le

/-! ### The Weil representation -/

omit [DecidableEq ι] in
/-- For the sup norms on vectors and the induced operator norm on matrices,
`1 + ‖A y‖ ≤ (1 + ‖A‖) (1 + ‖y‖)`. -/
lemma one_add_enorm_mulVec_le {p : Type*} [Fintype p] (A : Matrix ι p ℂ) (y : p → ℂ) :
    1 + ‖A *ᵥ y‖ₑ ≤ (1 + ‖A‖ₑ) * (1 + ‖y‖ₑ) := by
  grw [enorm_eq_nnnorm, linfty_opNNNorm_mulVec, mul_one_add, ENNReal.coe_mul]
  bound

/-- The Weil operator of `u` as an integral: `realWeil u v` is `realMultiplier u` times
`∫ v(y) realHeisenbergOp (u y) vacVector dy`. This is the definition of the Weil representation. -/
private lemma realWeil_eq_integral (u : USign ε) (v : fockSpace ε) :
    realWeil u v = realMultiplier u • ∫ y : ι → ℂ,
      v y • realHeisenbergOp ((u : Matrix ι ι ℂ) *ᵥ y) (vacVector : fockSpace ε)
        ∂normalizedVolume ι := by
  rw [realWeil, weilRep]
  rfl

/-- The Weil representation of `u` multiplies the `N`-th moment `fockMoment N v` = ∫ (1 + ‖y‖)ᴺ
|v(y)| dy in [0, ∞] (sup norm ‖y‖, Lebesgue measure divided by π^|ι|) by at most
`‖realMultiplier u‖` (the scalar factor of the Weil operator) times `(1 + ‖u‖)ᴺ` times the moment of
the vacuum. Here `u : USign ε` acts through its matrix `(u : Matrix ι ι ℂ)`, and `‖u‖` is the
operator norm, for the sup norms, of the matrix of `u`. -/
lemma fockMoment_realWeil_le (u : USign ε) :
    fockMoment N (realWeil u v) ≤
      ‖realMultiplier u‖ₑ *
        ((1 + ‖(u : Matrix ι ι ℂ)‖ₑ) ^ N * fockMoment N (vacVector : fockSpace ε) *
          fockMoment N v) := by
  -- Write `realWeil u v` as `realMultiplier u` times the integral of
  -- `v y • realHeisenbergOp (u y) vacVector`, and bound each translate of the vacuum.
  have h_point (y : ι → ℂ) :
      fockMoment N (realHeisenbergOp ((u : Matrix ι ι ℂ) *ᵥ y) (vacVector : fockSpace ε)) ≤
        (1 + ‖(u : Matrix ι ι ℂ)‖ₑ) ^ N * fockMoment N (vacVector : fockSpace ε) *
          (1 + ‖y‖ₑ) ^ N := by
    calc
      _ ≤ (1 + ‖(u : Matrix ι ι ℂ) *ᵥ y‖ₑ) ^ N * fockMoment N (vacVector : fockSpace ε) :=
        fockMoment_realHeisenbergOp_le N vacVector _
      _ ≤ _ := by grw [one_add_enorm_mulVec_le, mul_pow, mul_right_comm]
  calc
    fockMoment N (realWeil u v) = ‖realMultiplier u‖ₑ * fockMoment N
        (∫ y, v y • realHeisenbergOp ((u : Matrix ι ι ℂ) *ᵥ y) (vacVector : fockSpace ε)
          ∂normalizedVolume ι) := by rw [realWeil_eq_integral, fockMoment_smul]
    _ ≤ ‖realMultiplier u‖ₑ * ∫⁻ y, fockMoment N
        (v y • realHeisenbergOp ((u : Matrix ι ι ℂ) *ᵥ y) (vacVector : fockSpace ε))
          ∂normalizedVolume ι := by
      grw [fockMoment_integral_le]
    _ ≤ _ := by grw [lintegral_fockMoment_smul_le h_point]

end New.Fock

/-!
## Bounds for functionals controlled by short differences

The hypothesis: ℓ is a bounded functional whose values are controlled by its differences under
Heisenberg translations `New.Fock.realHeisenbergOp` of size at most t.
-/

section MomentDifference

open Complex MeasureTheory ENNReal Matrix

/-- The derivative of a translate of a polynomial vector along a line. Let `ρ` be the Heisenberg
translation `realHeisenbergOp` and `v_P = polyVector ε P` the product of a polynomial and the
Gaussian. For `y`, `z` in `ℂ^ι`, the curve `s ↦ ρ(s y) ρ(z) v_P` has the derivative
`ρ(s y) ρ(z) v_Q` with `Q = κ P + heisenbergDeriv ε y P`. Here `heisenbergDeriv ε y` is the
derivative of `ρ(s y)` at `0` on polynomials, and `κ = z* ε y - y* ε z`, with `ε` the diagonal
matrix of signs, comes from commuting `ρ(s y)` with `ρ(z)`. -/
lemma New.Fock.hasDerivAt_realHeisenbergOp_realHeisenbergOp {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ε : ι → ℤˣ} (y z : ι → ℂ) (P : MvPolynomial ι ℂ) (s : ℝ) :
    HasDerivAt (fun r : ℝ ↦ realHeisenbergOp (r • y) (realHeisenbergOp z (polyVector ε P)))
      (realHeisenbergOp (s • y) (realHeisenbergOp z (polyVector ε
        ((star z ⬝ᵥ signMatrix ε *ᵥ y - star y ⬝ᵥ signMatrix ε *ᵥ z) • P + heisenbergDeriv ε y P))))
      s := by
  -- Along a line `ρ` is a homomorphism, so it is enough to differentiate at `0`, where
  -- `ρ(r y) ρ(z) = exp (r κ) ρ(z) ρ(r y)`.
  set κ : ℂ := star z ⬝ᵥ signMatrix ε *ᵥ y - star y ⬝ᵥ signMatrix ε *ᵥ z with hκ
  have h_comm (r : ℝ) (v : fockSpace ε) :
      realHeisenbergOp (r • y) (realHeisenbergOp z v) = exp (r * κ) • realHeisenbergOp z
        (realHeisenbergOp (r • y) v) := by
    have h_phase : (realHeisenberg ε).β (r • y) z = exp (r * κ) * (realHeisenberg ε).β z
      (r • y) := by
      simp only [realHeisenberg, ← exp_add, hκ, star_smul, star_trivial, Matrix.mulVec_smul,
        smul_dotProduct, dotProduct_smul, real_smul]
      congr 1
      ring
    rw [Heisenberg.Rep.mul, Heisenberg.Rep.mul, h_phase, mul_smul, add_comm]
  have h_line (r : ℝ) (v : fockSpace ε) :
      realHeisenbergOp (r • y) v = realHeisenbergOp (s • y) (realHeisenbergOp ((r - s) • y) v) := by
    have h_phase : (realHeisenberg ε).β (s • y) ((r - s) • y) = 1 := by
      simp only [realHeisenberg, star_smul, star_trivial, Matrix.mulVec_smul, smul_dotProduct,
        dotProduct_smul, smul_comm s, sub_self, zero_div, exp_zero]
    rw [Heisenberg.Rep.mul, h_phase, one_smul, ← add_smul, add_sub_cancel]
  have h_exp : HasDerivAt (fun r : ℝ ↦ exp (r * κ)) κ 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const κ).cexp
  have h_zero : HasDerivAt (fun r : ℝ ↦ realHeisenbergOp (r • y)
    (realHeisenbergOp z (polyVector ε P)))
      (realHeisenbergOp z (polyVector ε (κ • P + heisenbergDeriv ε y P))) 0 := by
    simp only [h_comm]
    simpa [add_comm] using
      h_exp.fun_smul ((hasDerivAt_realHeisenbergOp y P).map_clm (realHeisenbergOp z))
  rw [funext fun r : ℝ ↦ h_line r (realHeisenbergOp z (polyVector ε P))]
  exact (HasDerivAt.comp_sub_const s s (by rwa [sub_self])).map_clm (realHeisenbergOp (s • y))

/-- Each derivative gains a factor `t` and costs a factor `1 + ‖z‖`. For each `N` and polynomial `P`
there is `C` as follows. Let `0 ≤ t ≤ 1`, and let `ℓ` be a bounded functional on the Fock space such
that, for every `f`, a bound for all `‖ℓ f - ℓ (ρ(y) f)‖` with `‖y‖ ≤ t` bounds `‖ℓ f‖`; here `ρ` is
the Heisenberg translation `realHeisenbergOp`. Then `‖ℓ (ρ(z) v_P)‖ ≤ C ‖ℓ‖ t ^ N (1 + ‖z‖) ^ N` for
all `z`, where `v_P = polyVector ε P` is the product of `P` and the Gaussian. -/
lemma New.Fock.exists_norm_realHeisenbergOp_polyVector_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ε : ι → ℤˣ} (N : ℕ) (P : MvPolynomial ι ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : ℝ) (ℓ : fockSpace ε →L[ℂ] ℂ), 0 ≤ t → t ≤ 1 →
      (∀ (f : fockSpace ε) (B : ℝ),
        (∀ y : ι → ℂ, ‖y‖ ≤ t → ‖ℓ f - ℓ (realHeisenbergOp y f)‖ ≤ B) → ‖ℓ f‖ ≤ B) →
      ∀ z : ι → ℂ, ‖ℓ (realHeisenbergOp z (polyVector ε P))‖ ≤ C * ‖ℓ‖ * t ^ N * (1 + ‖z‖) ^ N := by
  -- A difference is at most the supremum of the derivative along the segment from `0` to `y`. The
  -- derivative is `ℓ` at translates of polynomial vectors, with coefficients `O(t (1 + ‖z‖))`.
  induction N generalizing P with
  | zero =>
    refine ⟨‖polyVector ε P‖, norm_nonneg _, fun t ℓ _ _ _ z ↦ ?_⟩
    simpa [mul_comm, Heisenberg.Rep.norm_map] using
      ℓ.le_opNorm (realHeisenbergOp z (polyVector ε P))
  | succ N ih =>
    choose C hC h_bound using ih
    let D : ℝ := ∑ i : ι, (2 * C P + C (raiseOp ε i P) + C (lowerOp ε i P))
    have hD : 0 ≤ D := Finset.sum_nonneg fun i _ ↦ by
      linarith [hC P, hC (raiseOp ε i P), hC (lowerOp ε i P)]
    refine ⟨D * 2 ^ N, by positivity, fun t ℓ ht ht_le hℓ z ↦ hℓ _ _ fun y hy ↦ ?_⟩
    -- On the segment, `ρ(s y) ρ(z)` is a phase times a translation of size at most `1 + ‖z‖`.
    let m : ℝ := ‖ℓ‖ * t ^ N * (2 * (1 + ‖z‖)) ^ N
    have h_shift (s : ℝ) (hs : s ∈ Set.Ico (0 : ℝ) 1) (Q : MvPolynomial ι ℂ) :
        ‖ℓ (realHeisenbergOp (s • y) (realHeisenbergOp z (polyVector ε Q)))‖ ≤ C Q * m := by
      have h_norm : 1 + ‖s • y + z‖ ≤ 2 * (1 + ‖z‖) := by
        grw [norm_add_le, norm_smul, Real.norm_of_nonneg hs.1, hs.2, hy, ht_le]
        linarith [norm_nonneg z]
      rw [Heisenberg.Rep.mul, map_smul, norm_smul, Heisenberg.norm_eq_one, one_mul]
      grw [h_bound Q t ℓ ht ht_le hℓ, h_norm]
      · exact le_of_eq (by ring)
      · positivity [hC Q]
    -- The polynomial in the derivative, coordinate by coordinate.
    let κ : ℂ := star z ⬝ᵥ signMatrix ε *ᵥ y - star y ⬝ᵥ signMatrix ε *ᵥ z
    let c (i : ι) : ℂ := star (z i) * (ε i * y i) - star (y i) * (ε i * z i)
    have h_sum : κ • P + heisenbergDeriv ε y P = ∑ i : ι,
        (c i • P + y i • raiseOp ε i P - star (y i * ε i) • lowerOp ε i P) := by
      simp [κ, c, heisenbergDeriv, dotProduct, signMatrix, Matrix.mulVec_diagonal,
        ← Finset.sum_sub_distrib, Finset.sum_smul, ← Finset.sum_add_distrib, add_sub_assoc]
    have hy_i (i : ι) : ‖y i‖ ≤ t * (1 + ‖z‖) :=
      ((norm_le_pi_norm y i).trans hy).trans (le_mul_of_one_le_right ht (by simp))
    have h_sign (i : ι) : ‖(ε i : ℂ)‖ = 1 := by simp [abs_unit_intCast]
    have hc (i : ι) : ‖c i‖ ≤ 2 * (t * (1 + ‖z‖)) := by
      have h_term : ‖y i‖ * ‖z i‖ ≤ t * (1 + ‖z‖) := by
        grw [norm_le_pi_norm y, hy, norm_le_pi_norm z, ← le_add_of_nonneg_left zero_le_one]
      grw [norm_sub_le]
      simp only [norm_mul, norm_star, h_sign, one_mul]
      linarith
    have h_deriv (s : ℝ) (hs : s ∈ Set.Ico (0 : ℝ) 1) :
        ‖ℓ (realHeisenbergOp (s • y) (realHeisenbergOp z
          (polyVector ε (κ • P + heisenbergDeriv ε y P))))‖ ≤
          D * m * (t * (1 + ‖z‖)) := by
      simp only [h_sum, map_sum, map_sub, map_add, map_smul, D, Finset.sum_mul]
      refine norm_sum_le_of_le _ fun i _ ↦ ?_
      have h_star : ‖star (y i * ε i)‖ = ‖y i‖ := by rw [norm_star, norm_mul, h_sign, mul_one]
      -- Each of the three terms is a coefficient times a value bounded by `h_shift`.
      grw [norm_sub_le, norm_add_le]
      simp only [norm_smul, h_star]
      grw [hc, hy_i, h_shift s hs, h_shift s hs, h_shift s hs]
      exact le_of_eq (by ring)
    have h_mean_value := norm_image_sub_le_of_norm_deriv_le_segment_01'
      (fun s _ ↦ ((hasDerivAt_realHeisenbergOp_realHeisenbergOp y z P s).map_clm
        ℓ).hasDerivWithinAt) h_deriv
    calc ‖ℓ (realHeisenbergOp z (polyVector ε P)) -
           ℓ (realHeisenbergOp y (realHeisenbergOp z (polyVector ε P)))‖
      _ ≤ D * m * (t * (1 + ‖z‖)) := by simpa [norm_sub_rev] using h_mean_value
      _ = D * 2 ^ N * ‖ℓ‖ * t ^ (N + 1) * (1 + ‖z‖) ^ (N + 1) := by
        simp only [m, mul_pow]
        ring

/-- For each `N` there is a constant `C ≥ 0` as follows. Let `t ≥ 0` and let `ℓ` be a bounded
functional on the Fock space. Suppose that, if `t < 1`, every real `B` that bounds
`‖ℓ f - ℓ (realHeisenbergOp y f)‖` for all `y` with `‖y‖ ≤ t` also bounds `‖ℓ f‖`, for every vector
`f`. Then `‖ℓ v‖` is at most `C ‖ℓ‖ tᴺ` times the `N`-th moment of `v`, for every vector `v`. -/
lemma New.Fock.exists_enorm_le_mul_fockMoment_of_norm_sub_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ε : ι → ℤˣ} (N : ℕ) :
    ∃ C : NNReal, ∀ (t : ℝ) (ℓ : fockSpace ε →L[ℂ] ℂ) {v : fockSpace ε}, 0 ≤ t →
      (t < 1 → ∀ (f : fockSpace ε) (B : ℝ),
        (∀ y : ι → ℂ, ‖y‖ ≤ t → ‖ℓ f - ℓ (realHeisenbergOp y f)‖ ≤ B) → ‖ℓ f‖ ≤ B) →
      ‖ℓ v‖ₑ ≤ ENNReal.ofReal (C * ‖ℓ‖ * t ^ N) * fockMoment N v := by
  -- By superposition (`enorm_le_mul_fockMoment`) it is enough to bound `ℓ` on the translates of the
  -- vacuum. For `t ≥ 1` the norm of `ℓ` suffices.
  obtain ⟨C, hC, h_bound⟩ := exists_norm_realHeisenbergOp_polyVector_le (ε := ε) N 1
  refine ⟨⟨C, hC⟩ + ‖(vacVector : fockSpace ε)‖₊, fun t ℓ v ht h_diff ↦
    enorm_le_mul_fockMoment N fun z ↦ (div_le_iff₀ (by positivity)).2 ?_⟩
  rcases lt_or_ge t 1 with ht_lt | ht_ge
  · calc ‖ℓ (realHeisenbergOp z vacVector)‖
      _ ≤ C * ‖ℓ‖ * t ^ N * (1 + ‖z‖) ^ N := by
        simpa using h_bound t ℓ ht ht_lt.le (h_diff ht_lt) z
      _ ≤ (C + ‖(vacVector : fockSpace ε)‖) * ‖ℓ‖ * t ^ N * (1 + ‖z‖) ^ N := by
        gcongr
        exact le_add_of_nonneg_right (norm_nonneg _)
  · calc ‖ℓ (realHeisenbergOp z vacVector)‖
      _ ≤ ‖(vacVector : fockSpace ε)‖ * ‖ℓ‖ * 1 * 1 := by
        grw [ℓ.le_opNorm, Heisenberg.Rep.norm_map, mul_one, mul_one, mul_comm]
      _ ≤ (C + ‖(vacVector : fockSpace ε)‖) * ‖ℓ‖ * t ^ N * (1 + ‖z‖) ^ N := by
        gcongr
        · exact le_add_of_nonneg_left hC
        · exact one_le_pow₀ ht_ge
        · exact one_le_pow₀ (le_add_of_nonneg_right (norm_nonneg z))

end MomentDifference
