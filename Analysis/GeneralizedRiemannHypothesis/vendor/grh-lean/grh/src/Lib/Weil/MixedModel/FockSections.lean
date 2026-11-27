import Lib.General.Analysis.MeanValueAndTaylor
import Lib.Weil.Fock.WeightedNorms

/-!
# Mixed Schrödinger–Fock models and rapid sections with prescribed values

A mixed model reads a vector `Φ` of a large Fock space `New.Fock.fockSpace` as a function
`x ↦ h.slice x Φ` on `ℂ ^ p` with values in a smaller Fock space. An adapted splitting of a
hermitian space induces one at the infinite places (`New.Space.Splitting.IsAdapted.mixedModel`). A
vector is a Schwartz vector (`New.Exchange.IsSchwartzVector`) if all its moments `fockMoment N
v = ∫⁻ y, (1 + ‖y‖) ^ N * ‖v y‖ ∂normalizedVolume` are finite; `New.Fock.realWeil` is the Weil
representation.

The file shows that the values of a mixed model decay rapidly. It also constructs Schwartz vectors
with prescribed smooth compactly supported values, using Fourier inversion in `x` and non-stationary
phase.

## Main definitions and results

* `New.Fock.MixedModel`: the structure, described by the action of the Heisenberg operators
  `New.Fock.realHeisenbergOp` and by the value of the vacuum.
* `New.Fock.MixedModel.exists_fockMoment_slice_le`: the values decay rapidly in `x`, in the moments
  `New.Fock.fockMoment`.
* `New.Fock.MixedModel.exists_isSchwartzVector_slice_eq`: if `τ` is smooth of compact support, `u`
  is a smooth unitary family and `ξ` is a Schwartz vector, then `x ↦ τ x • realWeil (u x) ξ` is
  `x ↦ h.slice x Φ` for a Schwartz vector `Φ`.

Notions from other files:
* `New.Fock.fockSpace`: the Fock space: integrable functions c on ℂ^ι with c(x) = ∫ c(y)β(y,x)e(x−y)
  dy, e the Gaussian exp(−|x|²/2), under the L¹ norm for the measure `New.Fock.normalizedVolume` on
  ℂ^ι.
* `New.Fock.vacVector`: the Gaussian exp(−|x|²/2) regarded as an element of the Fock space.
* `New.Fock.realHeisenberg`: for signs ε, the Heisenberg datum on ℂ^ι given by the continuous
  unit-modulus bicharacter β(x,y) = exp((y*εx − x*εy)/2) = exp(i Im y*εx), where ε stands for
  `signMatrix ε`, the diagonal matrix of the signs.

## Relation to the literature

Known; see `Lib.Weil.MixedModel.ZeroTerm` for sources.
-/

namespace New.Fock

/-! ## Mixed Schrödinger–Fock models and rapid decay of their values -/

section MixedFockModel

open Matrix ENNReal Exchange

variable {ι ι' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] (ε' : ι' → ℤˣ)
  (ε : ι → ℤˣ) (p : Type*) [Fintype p] [DecidableEq p]

/-- A mixed (Schrödinger–Fock) model for a decomposition `ℂ^ι' = L ℂ^p + I ℂ^ι + K ℂ^p`: a vector
`v` of the large Fock space is read as the function `a ↦ slice a v` on `ℂ^p` with values in the
small one. The Heisenberg operator of `L a' + I w + K b` translates `a` by `a'`, acts by `w`
on the value and multiplies by `exp (i Im b* (2 a + a'))`. The vacuum is `exp (-|a|²)` times
the small vacuum. -/
structure MixedModel where
  /-- The matrix of the directions that translate the argument in `ℂ^p`. -/
  L : Matrix ι' p ℂ
  /-- The matrix of the directions that multiply by a character of `ℂ^p`. -/
  K : Matrix ι' p ℂ
  /-- The matrix of the directions that act on the values, in the small Fock space. -/
  I : Matrix ι' ι ℂ
  /-- The value at `a ∈ ℂ^p`: a bounded map from the large Fock space to the small one. -/
  slice : (p → ℂ) → fockSpace ε' →L[ℂ] fockSpace ε
  /-- Every vector `y` is `L a + I w + K b` with `a`, `w`, `b` given by matrices applied to `y`, so
  that their norms are bounded by a multiple of that of `y`. -/
  exists_decomp :
    ∃ (A : Matrix p ι' ℂ) (W : Matrix ι ι' ℂ) (B : Matrix p ι' ℂ),
      ∀ y : ι' → ℂ, L *ᵥ A *ᵥ y + I *ᵥ W *ᵥ y + K *ᵥ B *ᵥ y = y
  /-- The Heisenberg operator of `L a' + I w + K b` translates the argument by `a'`, applies the
  operator of `w` to the value and multiplies by the phase `β (2 a + a') b`. -/
  slice_realHeisenbergOp (a a' : p → ℂ) (w : ι → ℂ) (b : p → ℂ) (v : fockSpace ε') :
      slice a (realHeisenbergOp (L *ᵥ a' + I *ᵥ w + K *ᵥ b) v) =
        (realHeisenberg 1).β (2 • a + a') b • realHeisenbergOp w (slice (a + a') v)
  /-- The vacuum is the Gaussian `exp (-|a|²)` times the vacuum of the small space. -/
  slice_vac (a : p → ℂ) : slice a vacVector = Complex.exp (-(star a ⬝ᵥ a)) • vacVector

variable {ε' ε p} (h : MixedModel ε' ε p)

/-- Rapid decay in a mixed model: for all `N`, `M` there is a finite `C` with
`(1 + ‖a‖) ^ M * fockMoment N (slice a v) ≤ C * fockMoment (N + M) v` for all `a` and `v`. -/
lemma MixedModel.exists_fockMoment_slice_le (N M : ℕ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (a : p → ℂ) (v : fockSpace ε'),
      (1 + ‖a‖ₑ) ^ M * fockMoment N (h.slice a v) ≤ C * fockMoment (N + M) v := by
  -- Expand `v` into translates `realHeisenbergOp y vacVector` and split
  -- `y = L A y + I W y + K B y`. Up to a phase, `h.slice a (realHeisenbergOp y vacVector)` is
  -- `exp (-|a + A y|²)` times the translate of the small vacuum by `W y`. The Gaussian turns the
  -- weight `(1 + ‖a‖) ^ M` into a multiple of `(1 + ‖A y‖) ^ M`.
  obtain ⟨A, W, B, h_span⟩ := h.exists_decomp
  obtain ⟨cA, hcA, hA⟩ : ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ ∀ y : ι' → ℂ, 1 + ‖A *ᵥ y‖ₑ ≤ c * (1 + ‖y‖ₑ) :=
    ⟨_, by simp, one_add_enorm_mulVec_le A⟩
  obtain ⟨cW, hcW, hW⟩ : ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ ∀ y : ι' → ℂ, 1 + ‖W *ᵥ y‖ₑ ≤ c * (1 + ‖y‖ₑ) :=
    ⟨_, by simp, one_add_enorm_mulVec_le W⟩
  have h_gauss (a b : p → ℂ) :
      (1 + ‖a‖ₑ) ^ M * ‖(-(star (a + b) ⬝ᵥ (a + b))).exp‖ₑ ≤
        .ofReal (.exp (M ^ 2)) * (1 + ‖b‖ₑ) ^ M := by
    have h_tri : 1 + ‖a‖ ≤ (‖a + b‖ + 1) * (1 + ‖b‖) := by
      nlinarith [norm_le_add_norm_add a b, norm_nonneg (a + b), norm_nonneg b]
    -- `exp (-|x|²) ≤ exp (-|x|² / 2) = realVac x`, and `pow_mul_realVac_le` turns `h_tri` into
    -- `(1 + ‖a‖) ^ M * ‖realVac (a + b)‖ ≤ exp (M ^ 2) * (1 + ‖b‖) ^ M`.
    have h_half : ‖(-(star (a + b) ⬝ᵥ (a + b))).exp‖ ≤ ‖realVac (a + b)‖ := by
      -- (`↓` applies the norm identity before the default simp lemmas)
      simp [realVac, Complex.norm_exp, ↓star_dotProduct_self_eq_norm_sq, neg_div, sq,
        mul_self_nonneg]
    grw [← ofReal_norm (Complex.exp _), h_half]
    simpa (disch := bound) [ENNReal.ofReal_add] using
      ofReal_le_ofReal (pow_mul_realVac_le M h_tri (by positivity) (by positivity))
  set C : ℝ≥0∞ :=
    .ofReal (.exp (M ^ 2)) * cA ^ M * (cW ^ N * fockMoment N (vacVector : fockSpace ε))
  have h_transl (a : p → ℂ) (y : ι' → ℂ) :
      (1 + ‖a‖ₑ) ^ M * fockMoment N (h.slice a (realHeisenbergOp y vacVector)) ≤
        C * (1 + ‖y‖ₑ) ^ (N + M) := by
    calc
      _ = (1 + ‖a‖ₑ) ^ M * ‖(-(star (a + A *ᵥ y) ⬝ᵥ (a + A *ᵥ y))).exp‖ₑ *
          fockMoment N (realHeisenbergOp (W *ᵥ y) (vacVector : fockSpace ε)) := by
        conv_lhs => rw [← h_span y, slice_realHeisenbergOp, slice_vac, map_smul]
        simp [fockMoment_smul, mul_assoc, ← ofReal_norm, Heisenberg.norm_eq_one]
      _ ≤ .ofReal (.exp (M ^ 2)) * (cA * (1 + ‖y‖ₑ)) ^ M *
          ((cW * (1 + ‖y‖ₑ)) ^ N * fockMoment N (vacVector : fockSpace ε)) := by
        grw [h_gauss, fockMoment_realHeisenbergOp_le, hA, hW]
      _ = _ := by simp only [C, mul_pow, pow_add, mul_assoc, mul_comm, mul_left_comm]
  refine ⟨C, ?_, fun a v ↦ ?_⟩
  · simp [C, isSchwartzVector_vacVector N, mul_eq_top, hcA, hcW]
  · -- Integrate `h_transl` against `v`, with the finite non-zero weight moved to the right.
    obtain ⟨h_ne_zero, h_ne_top⟩ : (1 + ‖a‖ₑ) ^ M ≠ 0 ∧ (1 + ‖a‖ₑ) ^ M ≠ ⊤ := by simp
    rw [mul_le_iff_le_inv h_ne_zero h_ne_top, ← mul_assoc, isVacuum_realVac.map_eq_integral]
    refine (fockMoment_integral_le N).trans (lintegral_fockMoment_smul_le fun y ↦ ?_)
    grw [mul_assoc, ← mul_le_iff_le_inv h_ne_zero h_ne_top, h_transl]

/-- In a mixed model, each value of a Schwartz vector (one with all moments finite) is a Schwartz
vector. -/
lemma MixedModel.isSchwartzVector_slice (a : p → ℂ) {v : fockSpace ε'} (hv : IsSchwartzVector v) :
    IsSchwartzVector (h.slice a v) := fun N ↦ by
  obtain ⟨C, hC, h_le⟩ := h.exists_fockMoment_slice_le N 0
  have h_bound : fockMoment N (h.slice a v) ≤ C * fockMoment N v := by simpa using h_le a v
  exact ne_top_of_le_ne_top (mul_ne_top hC (hv N)) h_bound

end MixedFockModel

/-! ## Rapid sections with prescribed values -/

section RapidSections

open MeasureTheory Function ContinuousLinearMap Real Complex Heisenberg IsVacuum Matrix Finset
  Exchange Norms.Elementwise ContDiff Continuous ENNReal

variable {ι ι' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
  {ε : ι → ℤˣ} {ε' : ι' → ℤˣ} {p : Type} [Fintype p] [DecidableEq p] (h : MixedModel ε' ε p)

/-- The coherent state at `a`, the translate of the vacuum by `a`, takes at `w` the value of the
bicharacter at `(a, w)` times the vacuum at `w - a`, both exponentials. -/
private lemma realHeisenbergOp_vacVector_apply {ι' : Type} [Fintype ι'] [DecidableEq ι']
    {ε' : ι' → ℤˣ} (a w : ι' → ℂ) :
    (realHeisenbergOp a vacVector : fockSpace ε') w =
      cexp ((star w ⬝ᵥ signMatrix ε' *ᵥ a - star a ⬝ᵥ signMatrix ε' *ᵥ w) / 2) *
        cexp (-(star (w - a) ⬝ᵥ (w - a)) / 2) := by
  rw [heisenbergOp_apply]
  rfl

omit [DecidableEq ι] [DecidableEq p] in
/-- Let `A x` be a smooth family of real-linear maps from `ℂ ^ ι` to `ℂ ^ ι'`. The value at `w` of
the coherent state at `A x y` (the translate `realHeisenbergOp (A x y) vacVector` of the vacuum) is
`exp q`, with `q` smooth in `((y, w), x)` and homogeneous of degree two in `(y, w)`. -/
lemma exists_smooth_exponent_coherent {A : EuclideanSpace ℂ p → (ι → ℂ) →L[ℝ] ι' → ℂ}
    (hA : ContDiff ℝ ∞ A) :
    ∃ q : ((ι → ℂ) × (ι' → ℂ)) × EuclideanSpace ℂ p → ℂ,
      (∀ (y : ι → ℂ) (w : ι' → ℂ) (x : EuclideanSpace ℂ p),
        cexp (q ((y, w), x)) = (realHeisenbergOp (A x y) vacVector : fockSpace ε') w) ∧
      ContDiff ℝ ∞ q ∧
      ∀ r > (0 : ℝ), ∀ (t : (ι → ℂ) × (ι' → ℂ)) (x : EuclideanSpace ℂ p),
        q (r⁻¹ • t, x) / (r : ℂ)⁻¹ ^ 2 = q (t, x) := by
  -- `e a w` is the exponent of the bicharacter `β a w` plus that of the Gaussian at `w - a`.
  let e (a w : ι' → ℂ) : ℂ := (star w ⬝ᵥ signMatrix ε' *ᵥ a - star a ⬝ᵥ signMatrix ε' *ᵥ w) / 2 +
    -(star (w - a) ⬝ᵥ (w - a)) / 2
  refine ⟨fun ((y, w), x) ↦ e (A x y) w, fun y w x ↦ ?_, ?_, ?_⟩
  · show cexp (e (A x y) w) = realHeisenbergOp (A x y) vacVector w
    rw [realHeisenbergOp_vacVector_apply, ← Complex.exp_add]
  · simp only [e, dotProduct, Pi.star_apply, RCLike.star_def, mulVec, Pi.sub_apply, star_sub]
    fun_prop
  · intro r hr t x
    have hr_ne : (r : ℂ) ≠ 0 := mod_cast hr.ne'
    simp [e, mulVec_smul, star_trivial, field]

omit [DecidableEq ι] [DecidableEq p] in
/-- For `d` smooth of compact support and `A x` a smooth family of real-linear maps, the Fourier
transform in `x` of `d x` times the value at `w` of the coherent state
`realHeisenbergOp (A x y) vacVector` decays rapidly in `b` and `w`, with polynomial growth in `y`:
for all `M`, `n` its product with `(1 + ‖b‖) ^ M * (1 + ‖w‖) ^ n` is at most
`C * (1 + ‖y‖) ^ (2 * M + n)`. -/
lemma exists_norm_fourier_coherent_le {d : EuclideanSpace ℂ p → ℂ} (d_smooth : ContDiff ℝ ∞ d)
    (d_supp : HasCompactSupport d) {A : EuclideanSpace ℂ p → (ι → ℂ) →L[ℝ] ι' → ℂ}
    (hA : ContDiff ℝ ∞ A) (M n : ℕ) :
    ∃ C : ℝ, ∀ (y : ι → ℂ) (w : ι' → ℂ) (b : EuclideanSpace ℂ p),
      (1 + ‖b‖) ^ M * (1 + ‖w‖) ^ n *
          ‖FourierTransform.fourier
            (fun x : EuclideanSpace ℂ p ↦
              d x * (realHeisenbergOp (A x y) vacVector : fockSpace ε') w)
            b‖ ≤
        C * (1 + ‖y‖) ^ (2 * M + n) := by
  obtain ⟨B, B_pos, hB⟩ := (d_supp.image hA.continuous).isBounded.exists_pos_norm_le
  -- The coherent state at `A x y` takes the value `exp (q ((y, w), x))` at `w`.
  obtain ⟨q, exp_q, q_smooth, q_homog⟩ := exists_smooth_exponent_coherent (ε' := ε') hA
  -- Non-stationary phase, for the functions `d x * exp (q (s, x) / a)`.
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ (b : EuclideanSpace ℂ p) (s : (ι → ℂ) × (ι' → ℂ)) (a : ℂ) (D : ℝ),
      ‖s‖ ≤ 1 → ‖a‖ ≤ 1 → a ≠ 0 → (∀ x ∈ tsupport d, ‖cexp (q (s, x) / a)‖ ≤ D) →
        (‖a‖ * (1 + ‖b‖)) ^ M *
          ‖FourierTransform.fourier (fun x ↦ d x * cexp (q (s, x) / a)) b‖ ≤ C * D :=
    exists_pow_mul_norm_fourier_le d_supp M (d_smooth.comp contDiff_snd) q_smooth
      fun _ _ ↦ image_eq_zero_of_notMem_tsupport
  set m : ℕ := 2 * M + n
  refine ⟨C * (rexp (m ^ 2) * (1 + B) ^ m), fun y w b ↦ ?_⟩
  simp only [← exp_q]
  set f : ℂ := FourierTransform.fourier (fun x ↦ d x * cexp (q ((y, w), x))) b
  let D : ℝ := rexp (m ^ 2) * (1 + B) ^ m * (1 + ‖y‖) ^ m
  set ρ : ℝ := 1 + ‖y‖ + ‖w‖ with hρ
  have ρ_pos : 0 < ρ := by positivity
  -- The Gaussian centred at `A x y` is at most `D / ρ ^ m` at `w`, as `‖A x‖ ≤ B`.
  have h_gauss (x : EuclideanSpace ℂ p) (hx : x ∈ tsupport d) :
      ‖cexp (q ((y, w), x))‖ ≤ D / ρ ^ m := by
    have h_rho_le : ρ ≤ (‖w - A x y‖ + 1) * ((1 + B) * (1 + ‖y‖)) := by
      unfold ρ
      grw [norm_le_norm_sub_add w (A x y), le_opNorm, hB _ ⟨x, hx, rfl⟩]
      nlinarith [norm_nonneg y, norm_nonneg (w - A x y), mul_nonneg B_pos.le (norm_nonneg y)]
    simpa [D, exp_q, le_div_iff₀, mul_comm _ (ρ ^ m), mul_assoc, ← mul_pow, ρ_pos,
      norm_eq_one] using
      pow_mul_realVac_le m h_rho_le ρ_pos.le (by positivity)
  -- Non-stationary phase at the rescaled point `ρ⁻¹ • (y, w)`, with parameter `a = ρ⁻¹ ^ 2`.
  have h_decay : (ρ⁻¹ ^ 2 * (1 + ‖b‖)) ^ M * ‖f‖ ≤ C * (D / ρ ^ m) := by
    -- `‖y‖, ‖w‖ ≤ ρ` and `1 ≤ ρ`, so the rescaled point and the parameter lie in the unit ball.
    have h_one_le : 1 ≤ ρ := by linarith [norm_nonneg y, norm_nonneg w, hρ]
    have h_point : ‖ρ⁻¹ • (y, w)‖ ≤ 1 := by
      rw [norm_smul, norm_inv, norm_of_nonneg ρ_pos.le, inv_mul_le_one₀ ρ_pos, Prod.norm_mk]
      exact max_le (by linarith [norm_nonneg w, hρ]) (by linarith [norm_nonneg y, hρ])
    have h_param : ‖(ρ : ℂ)⁻¹ ^ 2‖ ≤ 1 := by
      simpa [abs_of_pos ρ_pos] using inv_le_one_of_one_le₀ (one_le_pow₀ (n := 2) h_one_le)
    -- (`↓` applies the homogeneity of `q` before the default simp lemmas)
    simpa [f, ↓q_homog _ ρ_pos] using
      hC b (ρ⁻¹ • (y, w)) ((ρ : ℂ)⁻¹ ^ 2) (D / ρ ^ m) h_point h_param (by simp [ρ_pos.ne'])
        (by simpa only [q_homog _ ρ_pos] using h_gauss)
  -- The choice `m = 2 * M + n` makes the powers of `ρ` match.
  calc
    _ ≤ (1 + ‖b‖) ^ M * ρ ^ n * ‖f‖ := by
      gcongr
      simp [ρ]
    _ = (ρ⁻¹ ^ 2 * (1 + ‖b‖)) ^ M * ‖f‖ * ρ ^ m := by simp [m, field, pow_add, pow_mul, mul_pow]
    _ ≤ C * (D / ρ ^ m) * ρ ^ m := by gcongr
    _ = _ := by simp [D, field]

omit [DecidableEq p] in
/-- Finite moments of the superposition that `MixedModel.exists_isSchwartzVector_slice_eq`
integrates. Let `d` be smooth with compact support on `ℂ ^ p`, let `A x` be a smooth family of
real-linear maps from `ℂ ^ ι` to `ℂ ^ ι'`, let `ξ` be a Schwartz vector of the small Fock space and
`k` a continuous linear map. Put `G y x = d x • ξ y • realHeisenbergOp (A x y) vacVector` and let
`Ĝ y` be the Fourier transform of `G y` in `x`. Then for every `N` the integral over `(y, b)` of the
moment `fockMoment N (realHeisenbergOp (k b) (Ĝ y b))` is finite. -/
lemma lintegral_fockMoment_realHeisenbergOp_fourier_ne_top {d : EuclideanSpace ℂ p → ℂ}
    (d_smooth : ContDiff ℝ ∞ d) (d_supp : HasCompactSupport d)
    {A : EuclideanSpace ℂ p → (ι → ℂ) →L[ℝ] ι' → ℂ} (A_smooth : ContDiff ℝ ∞ A)
    {ξ : fockSpace ε} (hξ : IsSchwartzVector ξ) (k : EuclideanSpace ℂ p →L[ℂ] WithLp ⊤ (ι' → ℂ))
    (N : ℕ) :
    ∫⁻ z : (ι → ℂ) × EuclideanSpace ℂ p,
        fockMoment N (realHeisenbergOp (k z.2) (FourierTransform.fourier
          (fun x : EuclideanSpace ℂ p ↦
            d x • ξ z.1 • (realHeisenbergOp (A x z.1) vacVector : fockSpace ε')) z.2))
        ∂(normalizedVolume ι).prod volume ≠ ⊤ := by
  let G (y : ι → ℂ) (x : EuclideanSpace ℂ p) : fockSpace ε' :=
    d x • ξ y • realHeisenbergOp (A x y) vacVector
  have G_int (y : ι → ℂ) : Integrable (G y) :=
    integrable_of_hasCompactSupport (by fun_prop) d_supp.smul_right
  let Ĝ (y : ι → ℂ) : EuclideanSpace ℂ p → fockSpace ε' := FourierTransform.fourier (G y)
  -- The weights `(1 + ‖w‖) ^ (-r)` and `(1 + ‖b‖) ^ (-r')` are integrable.
  obtain ⟨r, int_w⟩ : (normalizedVolume ι').HasTemperateGrowth := inferInstance
  obtain ⟨r', int_b⟩ : (volume : Measure (EuclideanSpace ℂ p)).HasTemperateGrowth := inferInstance
  let M : ℕ := r' + ⌈‖k‖⌉₊ * N
  let m : ℕ := 2 * M + (r + N)
  -- Non-stationary phase bounds the Fourier transform of the values of the coherent states.
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ (y : ι → ℂ) (w : ι' → ℂ) (b : EuclideanSpace ℂ p),
      (1 + ‖b‖) ^ M * (1 + ‖w‖) ^ (r + N) * ‖FourierTransform.fourier (fun x : EuclideanSpace ℂ p ↦
        d x * (realHeisenbergOp (A x y) vacVector : fockSpace ε') w) b‖ ≤
        C * (1 + ‖y‖) ^ (2 * M + (r + N)) :=
    exists_norm_fourier_coherent_le d_smooth d_supp A_smooth M (r + N)
  -- A pointwise bound for the integrand of `(1 + ‖k b‖) ^ N * fockMoment N (Ĝ y b)`, which bounds
  -- the `N`-th moment of `realHeisenbergOp (k b) (Ĝ y b)`.
  have h_point (y : ι → ℂ) (b : EuclideanSpace ℂ p) (w : ι' → ℂ) :
      (1 + ‖k b‖) ^ N * (1 + ‖w‖) ^ N * ‖Ĝ y b w‖ ≤
      |C| * (1 + ‖y‖) ^ m * ‖ξ y‖ * ((1 + ‖b‖) ^ r')⁻¹ * ((1 + ‖w‖) ^ r)⁻¹ := by
    let f : ℂ := FourierTransform.fourier
      (fun x ↦ d x * (realHeisenbergOp (A x y) vacVector : fockSpace ε') w) b
    have hf : Ĝ y b w = ξ y * f := by
      -- the value at `w` is a continuous linear functional, so it passes under the integral
      change valueAt w (FourierTransform.fourier (G y) b) = ξ y * f
      rw [fourier_eq, ← integral_comp_comm _ (by simp [G_int])]
      simp [f, G, fourier_eq, ← integral_const_mul, Circle.smul_def, mul_left_comm]
    -- `M` is chosen so that the powers of `1 + ‖b‖` match.
    calc
      _ ≤ ((1 + ‖b‖) ^ ⌈‖k‖⌉₊) ^ N * (1 + ‖w‖) ^ N * (‖ξ y‖ * ‖f‖) := by
        grw [hf, norm_mul, k.le_opNorm, Nat.le_ceil ‖k‖,
          one_add_le_pow_of_two_add_nonneg (by bound)]
      _ = (1 + ‖b‖) ^ M * (1 + ‖w‖) ^ (r + N) * ‖f‖ * ‖ξ y‖ * ((1 + ‖b‖) ^ r')⁻¹ *
          ((1 + ‖w‖) ^ r)⁻¹ := by
        simp [M, field, pow_add, pow_mul]
      _ ≤ _ := by grw [hC y w b, le_abs_self C]
  -- The right side of `h_point` (with `C`) is integrable in `((y, b), w)`, since `ξ` is a Schwartz
  -- vector and the weights are integrable; it dominates the integrand.
  have int_y : Integrable (fun y : ι → ℂ ↦ ((1 + ‖y‖ₑ) ^ m * ‖ξ y‖ₑ).toReal) (normalizedVolume ι) :=
    integrable_toReal_of_lintegral_ne_top (by fun_prop) (hξ m)
  have h_dom : Integrable (fun z : ((ι → ℂ) × EuclideanSpace ℂ p) × (ι' → ℂ) ↦
      C * ((1 + ‖z.1.1‖ₑ) ^ m * ‖ξ z.1.1‖ₑ).toReal * (1 + ‖z.1.2‖) ^ (-(r' : ℝ)) *
        (1 + ‖z.2‖) ^ (-(r : ℝ))) (((normalizedVolume ι).prod volume).prod (normalizedVolume ι')) :=
    ((int_y.const_mul C).mul_prod int_b).mul_prod int_w
  refine (h_dom.hasFiniteIntegral.trans_le' ?_).ne
  -- `fockMoment N (realHeisenbergOp y v) ≤ (1 + ‖y‖) ^ N * fockMoment N v`, then compare the
  -- integrands.
  grw [lintegral_prod _ h_dom.aestronglyMeasurable.enorm, fockMoment_realHeisenbergOp_le,
    (fockMoment_eq ..).le, lintegral_const_mul_le]
  gcongr with ⟨y, b⟩ w
  -- (`↓` moves the comparison to real numbers, where `h_point` lives, before the other lemmas)
  simpa (disch := finiteness) [↓← toReal_le_toReal, toReal_add, abs_of_pos, ← mul_assoc] using
    h_point y b w

/-- At `(x + x, -π i b)`, the bicharacter of the positive signature is the Fourier character: both
are `exp (π i ∑ₖ (xₖ b̄ₖ + x̄ₖ bₖ))`. -/
private lemma realHeisenberg_β_eq_fourierChar (x : p → ℂ) (b : EuclideanSpace ℂ p) :
    ((realHeisenberg 1).β (x + x) ((-↑π * Complex.I) • b.ofLp) : ℂ) =
      (fourierChar (inner ℝ b (.toLp 2 x)) : ℂ) := by
  simp [realHeisenberg, PiLp.inner_apply, -neg_mul, dotProduct, mul_sum,
    ← sum_sub_distrib, -mul_re, re_eq_add_conj]
  simp only [Finset.sum_div]
  exact congrArg _ (sum_congr rfl fun i _ ↦ by ring)

/-- Let `τ` be smooth with compact support on `ℂ ^ p`, let `u x` be elements of the unitary group
`USign ε` of the signature `ε` whose matrices depend smoothly on `x`, and let `ξ` be a Schwartz
vector of the small Fock space. Then some Schwartz vector `Φ` of the large Fock space has the value
`τ x • realWeil (u x) ξ` at every `x` in the mixed model `h`. -/
lemma MixedModel.exists_isSchwartzVector_slice_eq {τ : (p → ℂ) → ℂ} (hτ : ContDiff ℝ ∞ τ)
    (hτ_supp : HasCompactSupport τ) {u : (p → ℂ) → USign ε}
    (hu : ContDiff ℝ ∞ fun x : p → ℂ ↦ ((u x : GL ι ℂ) : Matrix ι ι ℂ)) {ξ : fockSpace ε}
    (hξ : IsSchwartzVector ξ) :
    ∃ Φ : fockSpace ε', IsSchwartzVector Φ ∧ ∀ x : p → ℂ, h.slice x Φ = τ x • realWeil (u x) ξ := by
  -- `realWeil (u x) ξ` is a superposition, with density `ξ y`, of the coherent states
  -- `realHeisenbergOp (u x y) vacVector`. The slice at `x` of `G y x` is the `y`-part of
  -- `τ x • realWeil (u x) ξ`; take `Φ = ∬ realHeisenbergOp (k b) (Ĝ y b) db dy`, with `Ĝ y` the
  -- Fourier transform of `G y`. Fourier inversion gives the slices of `Φ`; non-stationary phase
  -- bounds its moments.
  set S : (p → ℂ) → Matrix ι ι ℂ := fun x ↦ ((u x : GL ι ℂ) : Matrix ι ι ℂ)
  -- `k b = K (-π i b)`: its Heisenberg operator multiplies slices by the Fourier character of `b`.
  let k : EuclideanSpace ℂ p →L[ℂ] WithLp ⊤ (ι' → ℂ) :=
    ((-π * Complex.I) • h.K.toLpLin 2 ⊤).toContinuousLinearMap
  -- `d x` is `τ x` times the multiplier of `realWeil (u x)`, over the Gaussian of `slice_vac`.
  let d (x : EuclideanSpace ℂ p) : ℂ :=
    τ x * (star (principalMinor (S x) (ε · = -1)) * cexp (star x ⬝ᵥ x))
  have d_supp : HasCompactSupport d := (hτ_supp.comp_homeomorph (PiLp.homeomorph ..)).mul_right
  have d_smooth : ContDiff ℝ ∞ d := by
    simp [d, principalMinor, dotProduct, det_apply, toSquareBlockProp]
    fun_prop
  -- `A x y = I (S x y)`.
  let A (x : EuclideanSpace ℂ p) : (ι → ℂ) →L[ℝ] ι' → ℂ :=
    (mulVecBilin ℝ ℝ).toContinuousBilinearMap (h.I * S x.ofLp)
  have A_smooth : ContDiff ℝ ∞ A := by fun_prop
  let G (y : ι → ℂ) (x : EuclideanSpace ℂ p) : fockSpace ε' :=
    d x • ξ y • realHeisenbergOp (A x y) vacVector
  have G_int (y : ι → ℂ) : Integrable (G y) :=
    integrable_of_hasCompactSupport (by fun_prop) d_supp.smul_right
  let Ĝ (y : ι → ℂ) : EuclideanSpace ℂ p → fockSpace ε' := FourierTransform.fourier (G y)
  have Ĝ_meas : StronglyMeasurable (uncurry Ĝ) := by
    simp only [uncurry_def, Ĝ, fourier_eq]
    exact .integral_prod_right (Continuous.stronglyMeasurable (by fun_prop))
  let F (z : (ι → ℂ) × EuclideanSpace ℂ p) : fockSpace ε' := realHeisenbergOp (k z.2) (Ĝ z.1 z.2)
  have h_mom (N : ℕ) : ∫⁻ z, fockMoment N (F z) ∂(normalizedVolume ι).prod volume ≠ ⊤ :=
    lintegral_fockMoment_realHeisenbergOp_fourier_ne_top d_smooth d_supp A_smooth hξ k N
  -- Finite integrated moments make `F` integrable, with integral a Schwartz vector.
  obtain ⟨F_int, F_rap⟩ := isSchwartzVector_integral (F := F) (by fun_prop) h_mom
  refine ⟨∫ z, F z ∂(normalizedVolume ι).prod volume, F_rap, fun x ↦ ?_⟩
  -- `realHeisenbergOp (k b)` multiplies the slice at `x` by the character of Fourier inversion.
  have h_inv (y : ι → ℂ) (hy : Integrable fun b ↦ F (y, b)) :
      ∫ b, h.slice x (F (y, b)) = h.slice x (G y (.toLp 2 x)) := by
    have Ĝ_int : Integrable (Ĝ y) :=
      hy.mono (by fun_prop) (.of_forall fun b ↦ by simp [F, Rep.norm_map])
    let χ (b : EuclideanSpace ℂ p) : Circle := fourierChar (inner ℝ b (.toLp 2 x))
    have h_slice_heisOp_K (c : p → ℂ) (v : fockSpace ε') :
        h.slice x (realHeisenbergOp (h.K *ᵥ c) v) =
          (realHeisenberg 1).β (x + x) c • h.slice x v := by
      simpa [two_mul] using h.slice_realHeisenbergOp x 0 0 c v
    calc
      _ = ∫ b, h.slice x (χ b • Ĝ y b) := by
        congr 1 with b : 1
        -- `k b = K (-π i b)`, and the bicharacter at `(x + x, -π i b)` is the Fourier character
        -- `χ b`: both are `exp (π i ∑ₖ (xₖ b̄ₖ + x̄ₖ bₖ))`.
        have h_kb : (k b).ofLp = h.K *ᵥ ((-↑π * Complex.I) • b.ofLp) := by
          simp [k, ← mulVec_smul, mulVec_neg]
        simp only [F, χ, h_kb, h_slice_heisOp_K, Circle.smul_def, map_smul,
          realHeisenberg_β_eq_fourierChar]
      _ = h.slice x (∫ b, χ b • Ĝ y b) := (h.slice x).integral_comp_comm
        (Ĝ_int.mono (by fun_prop) (.of_forall fun b ↦ by simp))
      _ = _ := by rw [← fourierInv_eq, fourierInv_fourier_eq (by fun_prop) (G_int y) Ĝ_int]
  rw [← integral_comp_comm _ F_int, integral_prod _ (by fun_prop),
    integral_congr_ae (F_int.prod_right_ae.mono h_inv)]
  have h_slice_heisOp_I (w : ι → ℂ) (v : fockSpace ε') :
      h.slice x (realHeisenbergOp (h.I *ᵥ w) v) = realHeisenbergOp w (h.slice x v) := by
    simpa using h.slice_realHeisenbergOp x 0 w 0 v
  -- `realWeil (u x) ξ` is by definition `∫ ξ y • realHeisenbergOp (S x y) vacVector` times the
  -- conjugate principal minor of `S x`; the factor `exp |x|²` of `d` cancels the Gaussian of
  -- `slice_vac`.
  simp [G, d, A, ← integral_smul, weilRep, Rep.integrated_apply, h_slice_heisOp_I, h.slice_vac,
    smul_smul, ← mulVec_mulVec, mul_assoc, Complex.exp_neg, mul_left_comm]
  rfl

end RapidSections

end New.Fock
