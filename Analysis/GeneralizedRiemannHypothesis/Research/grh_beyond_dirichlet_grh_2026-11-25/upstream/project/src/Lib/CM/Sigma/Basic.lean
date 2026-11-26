import Lib.General.NumberTheory.ImaginaryQuadraticField
import Lib.Shimura.ComplexTheta.DimensionFormula

/-!
# Sigma and Weierstrass functions, lattice invariants and lattices with complex multiplication

Let `L` be a period pair with lattice Λ, Weierstrass function ℘ and invariants g₂, g₃. The sigma
function `PeriodPair.σ` is built as an odd theta function for the form H(l, z) = (π/A)·l̄·z, where A
is the area of Λ; it differs from the classical sigma function by a factor exp(cz²). Its addition
formula and the description of the theta functions for twice the form give the duplication formula
of σ and the classical facts on ℘.

## Main definitions and results

* `New.IsAppellHumbert.theta_eq_zero_iff_mem_lattice`, `New.IsAppellHumbert.deriv_theta_ne_zero`,
  `New.IsAppellHumbert.thetaSpace_two_eq_span_pair`: a theta function f ≠ 0 for (H, χ) with
  f(0) = 0 has simple zeros exactly on Λ, and ℘f² and f² span the theta functions for (2H, χ²);
  `New.IsAppellHumbert.thetaSpace_two_eq_span` collects the three.
* `PeriodPair.σ`, `New.sigma_add_mul_sigma_sub`: for u and v outside Λ,
  σ(u + v)σ(u − v) = (℘(v) − ℘(u))σ(u)²σ(v)².
* `PeriodPair.exists_weierstrassP_eq_of_cubic`: every point of `y² = 4x³ - g₂x - g₃` is
  `(℘ z, ℘' z)`.
* `New.sigma_two_mul`: the duplication formula `σ(2z) = -℘'(z) σ(z)⁴`.
* `New.CMLattice d`: a lattice `Λ` with a point `t` of order two such that `℘''(t) = 2` and a
  square root `a₁` of `12 ℘(t)`. For `d ≠ 0` the lattice is also stable under multiplication by
  `New.quadInt d`, and neither `ω t` nor `ω̄ t` lies in it, where `ω = New.quadGen d`.
* `New.exists_lattice_eq_mul_tau`: every lattice is a(ℤτ + ℤ) with τ in the upper half plane.
* `New.g₂_eq_eisenstein`, `New.g₃_eq_eisenstein`, `New.g₂_pow_three_sub_g₃_sq_eq_discriminant`: g₂,
  g₃ and g₂³ − 27 g₃² of that lattice in terms of E₄(τ), E₆(τ) and Δ(τ).
* `New.exists_lattice_of_g₂_g₃`: conversely, every pair (a, b) with a³ − 27 b² ≠ 0 is (g₂, g₃) of a
  lattice (uniformization). The proof finds τ as a zero of a form of weight 12 that tends to 1 at
  the cusp: without a zero, its inverse would be a nonzero modular form of negative weight.

Notions from other files:
* `New.RealComplexForm.thetaSpace` Λ B χ: the entire f with f(z + l) = χ(l)·exp(B(l, z) + B(l,
  l)/2)·f(z) for l ∈ Λ. A `New.ThetaTori.LatticeForm Λ` is a form B that carries Λ in its type.
* `New.RealComplexForm.riemannForm`: the Riemann form of B, E(u, v) = Im(B(u, v) − B(v, u))/(2π).
* `New.IsAppellHumbert`: Appell–Humbert data: Re B is symmetric, and on Λ one has |χ| = 1 and
  χ(l + m) = χ(l)χ(m)·exp(πi E(m, l)).

## Relation to the literature

Known result: Sigma and theta functions of a lattice, their addition and doubling formulas, and
uniformisation. Here sigma is the odd section of a canonical factor of automorphy rather than a
product, and the origin is moved to a point of order two. Uniformisation comes from the vanishing of
modular forms of negative weight. Source: J. Silverman, The Arithmetic of Elliptic Curves, VI, and
Advanced Topics (1994), I.5; A. Weil, Elliptic Functions according to Eisenstein and Kronecker
(1976); for uniformisation, A. Sutherland, 18.783 Lecture 15 (2023), Cor. 15.12.
-/

noncomputable section

/-!
## The sigma function of a lattice and its addition formula

The sigma function is not defined by the Weierstrass product.
-/

section SigmaFunction

open Complex ComplexConjugate Module Basis PeriodPair Submodule New AddSubgroup Set IsAppellHumbert

variable (L : PeriodPair) {m : ℕ} {χ f g : ℂ → ℂ}

/-- Two entire functions `f` and `g` that agree off the translate `-t + L.lattice` of the lattice
of `L` agree everywhere. -/
lemma PeriodPair.eq_of_eq_off_lattice (t : ℂ) (hf_diff : Differentiable ℂ f)
    (hg_diff : Differentiable ℂ g) (h_eq : ∀ z : ℂ, z + t ∉ L.lattice → f z = g z) :
    ∀ z : ℂ, f z = g z := by
  -- The exceptional set is countable, so its complement is dense; the set where `f = g` is closed.
  have h_dense : Dense (range fun l : L.lattice ↦ (l : ℂ) - t)ᶜ :=
    (countable_range _).dense_compl ℝ
  exact congrFun <| hf_diff.continuous.ext_on h_dense hg_diff.continuous fun z hz ↦
    h_eq z fun h_mem ↦ hz ⟨⟨z + t, h_mem⟩, add_sub_cancel_right z t⟩

/-- The area of the period parallelogram spanned by `ω₁` and `ω₂`. -/
def PeriodPair.area : ℝ := |(conj L.ω₁ * L.ω₂).im|

/-- The hermitian form (l, z) ↦ (π/A)·l̄·z on ℂ, A the area of the lattice of L, as a map
real-linear in l and complex-linear in z. -/
def PeriodPair.hermitianForm : ThetaTori.LatticeForm L.lattice :=
  (Real.pi / L.area) • (ContinuousLinearMap.mul ℂ ℂ).restrictScalars ℝ ∘L conjCLE

/-- Multiplication by a maps the lattice of L into that of M, and a·ā·area(L) = N·area(M). For a ≠ 0
this says that multiplication by a is an isogeny of degree N from L to M. -/
@[simp] def PeriodPair.IsIsogeny (M : PeriodPair) (a : ℂ) (N : ℕ) : Prop :=
  (∀ x ∈ L.lattice, a * x ∈ M.lattice) ∧ a * conj a * L.area = N * M.area

namespace New

@[simp]
lemma area_pos : 0 < L.area := by
  -- The area is the absolute value of the determinant of the basis `ω₁, ω₂` against `1, I`.
  simpa [area, det, toMatrix, Matrix.det_succ_column_zero] using basisOneI.isUnit_det L.basis

open scoped Classical in
/-- The multiplier of the sigma function: `1` on twice the lattice, `-1` elsewhere. -/
def sigmaSign (w : ℂ) : ℂ := if w / 2 ∈ L.lattice then 1 else -1

lemma sigmaSign_neg (w : ℂ) : sigmaSign L (-w) = sigmaSign L w := by
  classical
  simp [sigmaSign, neg_div]

@[simp] lemma hermitianForm_apply (l z : ℂ) :
    L.hermitianForm l z = Real.pi / L.area * (z * conj l) := by
  simp [hermitianForm, field]

lemma two_nsmul_hermitianForm_apply (l z : ℂ) :
    (2 • L.hermitianForm) l z = 2 * L.hermitianForm l z := by
  simp [-hermitianForm_apply]

/-- The Riemann form of the hermitian form (π/A)·l̄z of a period lattice of area A takes (u, v)
to Im(ūv)/A. -/
lemma riemannForm_hermitianForm (u v : ℂ) :
    L.hermitianForm.riemannForm u v = (conj u * v).im / L.area := by
  have im_sub : (L.hermitianForm u v - L.hermitianForm v u).im =
      2 * Real.pi * ((conj u * v).im / L.area) := by simp; ring
  simp only [riemannForm, AddMonoidHom.mk'_apply, LinearMap.mk₂_apply, im_sub]
  field

/-- For some `k = ±1` the Riemann form of `L.hermitianForm` takes the value `k` at the two
periods. -/
lemma exists_riemannForm_periods_eq_sign :
    ∃ k ∈ ([1, -1] : List ℤ), L.hermitianForm.riemannForm L.ω₁ L.ω₂ = k := by
  -- The value is `Im (conj ω₁ * ω₂)` divided by its absolute value, the area.
  have abs_im : |(conj L.ω₁ * L.ω₂).im| = L.area := rfl
  simpa [riemannForm_hermitianForm, div_eq_iff (area_pos L).ne'] using eq_or_eq_neg_of_abs_eq abs_im

lemma half_mem_lattice_iff_even (m n : ℤ) :
    (m * L.ω₁ + n * L.ω₂) / 2 ∈ L.lattice ↔ Even m ∧ Even n := by
  have split : (m * L.ω₁ + n * L.ω₂) / 2 = (m / 2 : ℚ) * L.ω₁ + (n / 2 : ℚ) * L.ω₂ := by
    simp [field]
  rw [split, L.mul_ω₁_add_mul_ω₂_mem_lattice]
  simp [even_iff_two_dvd, ← Rat.den_div_intCast_eq_one_iff]

variable {L}

open scoped Classical in
/-- The form H(l, z) = (π/A)·l̄·z and the multiplier `New.sigmaSign` are Appell–Humbert data
for the lattice. -/
instance isAppellHumbert_hermitianForm : IsAppellHumbert L.hermitianForm (sigmaSign L) where
  re_symm u v := by simp [field]
  norm_eq_one l _ := by simp [sigmaSign, apply_ite]
  semicharacter l hl m hm := by
    -- Write `l` and `m` in the basis `ω₁, ω₂`; the Riemann form is their determinant times
    -- `k = ±1`, so both sides depend only on the parities of the coordinates.
    obtain ⟨a, b, rfl⟩ := mem_lattice.1 hl
    obtain ⟨c, d, rfl⟩ := mem_lattice.1 hm
    obtain ⟨k, hk, h_riem⟩ := exists_riemannForm_periods_eq_sign L
    have h_det : L.hermitianForm.riemannForm (c * L.ω₁ + d * L.ω₂) (a * L.ω₁ + b * L.ω₂) =
        ((c * b - d * a) * k : ℤ) := by
      rw [Int.cast_mul, ← h_riem]
      simp [riemannForm_hermitianForm]
      ring
    have h_sum : (a * L.ω₁ + b * L.ω₂ + (c * L.ω₁ + d * L.ω₂)) / 2 ∈ L.lattice ↔
        Even (a + c) ∧ Even (b + d) := by
      rw [← half_mem_lattice_iff_even]
      push_cast
      ring_nf
    have hk_odd : ¬ Even k := by fin_cases hk <;> simp
    have h_parity : ((if Even (a + c) ∧ Even (b + d) then 1 else -1) : ℂ) =
        (if Even a ∧ Even b then 1 else -1) * (if Even c ∧ Even d then 1 else -1) *
          (if Even ((c * b - d * a) * k) then 1 else -1) := by
      grind [Int.even_add, Int.even_sub]
    rw [h_det, ofReal_intCast, mul_comm (_ * I), exp_int_mul, exp_pi_mul_I]
    simpa only [sigmaSign, h_sum, half_mem_lattice_iff_even, neg_one_zpow_eq_ite] using h_parity

/-- If multiplication by the complex number a maps the lattice of L into the lattice of M, then
a·ā·area(L) = N·area(M) for some natural number N. -/
lemma exists_isIsogeny_of_mul_mem_lattice {M : PeriodPair} {a : ℂ}
    (ha : ∀ x ∈ L.lattice, a * x ∈ M.lattice) : ∃ N : ℕ, L.IsIsogeny M a N := by
  -- The Riemann form of `M` at `a ω₁, a ω₂` is an integer `n` with `|n| = |a|² area L / area M`.
  obtain ⟨n, hn⟩ : ∃ n : ℤ, M.hermitianForm.riemannForm (a * L.ω₁) (a * L.ω₂) = n :=
    isAppellHumbert_hermitianForm.le_dualLattice (ha _ L.ω₁_mem_lattice) _ (ha _ L.ω₂_mem_lattice)
  have form_eq : (n : ℝ) = ‖a‖ ^ 2 * (conj L.ω₁ * L.ω₂).im / M.area := by
    rw [← hn, riemannForm_hermitianForm, map_mul, mul_mul_mul_comm, conj_mul', ← ofReal_pow,
      im_ofReal_mul]
  have area_eq : ‖a‖ ^ 2 * L.area = (n.natAbs : ℝ) * M.area :=
    calc ‖a‖ ^ 2 * L.area = |‖a‖ ^ 2 * (conj L.ω₁ * L.ω₂).im| := by simp [area, abs_mul]
      _ = |(n : ℝ) * M.area| := by rw [form_eq, div_mul_cancel₀ _ (area_pos M).ne']
      _ = (n.natAbs : ℝ) * M.area := by simp [abs_mul, abs_of_pos (area_pos M)]
  exact ⟨n.natAbs, ha, by rw [mul_conj']; exact_mod_cast area_eq⟩

/-- The Riemann form `E` of `L.hermitianForm` is positive: `E(u, iu) > 0` for every `u ≠ 0`. -/
instance : IsPosRiemann L.hermitianForm := ⟨by simp [← normSq_apply, riemannForm_hermitianForm]⟩

/-- Expansion of `w` in the periods through the Riemann form `E` of `L.hermitianForm`:
`E(ω₁, ω₂) w = E(w, ω₂) ω₁ - E(w, ω₁) ω₂`. -/
lemma riemannForm_periods_mul_eq_sub (L : PeriodPair) (w : ℂ) :
    (L.hermitianForm.riemannForm L.ω₁ L.ω₂ : ℂ) * w =
      L.hermitianForm.riemannForm w L.ω₂ * L.ω₁ - L.hermitianForm.riemannForm w L.ω₁ * L.ω₂ := by
  apply Complex.ext <;> simp [riemannForm_hermitianForm] <;> ring

/-- Let `Λ` be the lattice of the period pair `L`, with covolume `A`, and let `H = L.hermitianForm`
be the hermitian form `(l, z) ↦ (π / A) · l̄ · z`. For `m ≠ 0`, `Λ` is `m` times the dual lattice of
`m H`, that is, of the points `v` at which the Riemann form of `m H` is integral against every
`l ∈ Λ`. Both sides are read as subgroups of that dual lattice. -/
lemma addSubgroupOf_dualLattice_nsmul_eq_range (L : PeriodPair) (m : ℕ) [NeZero m] :
    L.lattice.toAddSubgroup.addSubgroupOf (m • L.hermitianForm).dualLattice.toAddSubgroup =
      (nsmulAddMonoidHom m :
        (m • L.hermitianForm).dualLattice →+ (m • L.hermitianForm).dualLattice).range := by
  apply le_antisymm
  · rintro ⟨a, _⟩ (ha : a ∈ L.lattice)
    have h_mul : m • (a / m) = a := by simp [mul_div_cancel₀, NeZero.ne]
    -- The Riemann form of `H` is integral on the lattice, as `H` is part of Appell–Humbert data.
    have h_integral : a ∈ L.hermitianForm.dualLattice :=
      isAppellHumbert_hermitianForm.le_dualLattice ha
    exact ⟨⟨a / m, ThetaTori.mem_dualLattice_nsmul.2 (by rwa [h_mul])⟩, Subtype.ext h_mul⟩
  · rintro _ ⟨⟨x, hx⟩, rfl⟩
    obtain ⟨a, ha⟩ : ∃ a : ℤ, (m • L.hermitianForm).riemannForm x L.ω₁ = a :=
      hx _ L.ω₁_mem_lattice
    obtain ⟨b, hb⟩ : ∃ b : ℤ, (m • L.hermitianForm).riemannForm x L.ω₂ = b :=
      hx _ L.ω₂_mem_lattice
    obtain ⟨k, hk, h_riem⟩ := exists_riemannForm_periods_eq_sign L
    -- For the Riemann form `E`: `E (m x, ω₁) = a`, `E (m x, ω₂) = b` and `E (ω₁, ω₂) = k = ±1`
    -- give `m x = k b ω₁ - k a ω₂`.
    have h_expand : (k : ℂ) * (m • x) = b * L.ω₁ - a * L.ω₂ := by
      have ha' : L.hermitianForm.riemannForm (m • x) L.ω₁ = a := by simpa [-nsmul_eq_mul] using ha
      have hb' : L.hermitianForm.riemannForm (m • x) L.ω₂ = b := by simpa [-nsmul_eq_mul] using hb
      have h_periods : (k : ℂ) * (m • x) = L.hermitianForm.riemannForm (m • x) L.ω₂ * L.ω₁ -
          L.hermitianForm.riemannForm (m • x) L.ω₁ * L.ω₂ := by
        simpa [h_riem] using riemannForm_periods_mul_eq_sub L (m • x)
      rw [ha', hb'] at h_periods
      exact_mod_cast h_periods
    have hk_sq : (k : ℂ) * k = 1 := by fin_cases hk <;> simp
    refine mem_lattice.2 ⟨k * b, -k * a, ?_⟩
    have hk_sq : (k : ℂ) * k = 1 := by fin_cases hk <;> simp
    change ((k * b : ℤ) : ℂ) * L.ω₁ + ((-k * a : ℤ) : ℂ) * L.ω₂ = m • x
    push_cast
    linear_combination (m • x) * hk_sq - (k : ℂ) * h_expand

/-- For Appell–Humbert data `(H, χ)` with `H = L.hermitianForm` and `m ≠ 0`, the theta functions
for `(m H, χ ^ m)` form a space of dimension `m`.

This is Frobenius's dimension formula for theta functions, in one variable. -/
lemma IsAppellHumbert.finrank_thetaSpace_nsmul [h : IsAppellHumbert L.hermitianForm χ] [NeZero m] :
    finrank ℂ ((m • L.hermitianForm).thetaSpace (χ ^ m)) = m := by
  -- The square of the dimension is the index of `Λ` in the dual lattice `Λ'` for `m H`
  -- (`finrank_thetaSpace_sq`), and `Λ = m Λ'`; so the index is `m ^ 2`.
  let Λ' : Submodule ℤ ℂ := (m • L.hermitianForm).dualLattice
  have sq_eq : finrank ℂ ((m • L.hermitianForm).thetaSpace (χ ^ m)) ^ 2 = m ^ finrank ℤ Λ' :=
    calc _ = (L.lattice.toAddSubgroup.addSubgroupOf Λ'.toAddSubgroup).index :=
          (h.nsmul m).finrank_thetaSpace_sq
      _ = (nsmulAddMonoidHom m : Λ' →+ Λ').range.index :=
          congrArg index (addSubgroupOf_dualLattice_nsmul_eq_range L m)
      _ = m ^ finrank ℤ Λ' := index_range_nsmul Λ' m
  simpa [Λ', ZLattice.rank ℝ] using sq_eq

open scoped Classical in
/-- The function `℘ f²` for the lattice of `L`, given the value `f′²` at the lattice points,
where `℘` has its poles. -/
def _root_.PeriodPair.weierstrassPMulSq (L : PeriodPair) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  if z ∈ L.lattice then deriv f z ^ 2 else ℘[L] z * f z ^ 2

lemma _root_.PeriodPair.weierstrassPMulSq_of_mem {z : ℂ} (hz : z ∈ L.lattice) :
    L.weierstrassPMulSq f z = deriv f z ^ 2 :=
  ite_eq_left hz

/-- Off the lattice the value of `℘ f²` is the product of `℘` and `f²`. -/
lemma _root_.PeriodPair.weierstrassPMulSq_of_notMem {z : ℂ} (hz : z ∉ L.lattice) :
    L.weierstrassPMulSq f z = ℘[L] z * f z ^ 2 :=
  ite_eq_right hz

/-- For an entire function `f` vanishing at every point of the period lattice of `L`, the function
`L.weierstrassPMulSq f` is entire. This function equals `℘ f²` off the lattice and takes the value
`f′(l)²` at each lattice point `l`, where `℘` has its poles. -/
lemma differentiable_weierstrassPMulSq (f_diff : Differentiable ℂ f)
    (f_lattice : ∀ l ∈ L.lattice, f l = 0) :
    Differentiable ℂ (L.weierstrassPMulSq f) := by
  intro z
  by_cases hz : z ∈ L.lattice
  · -- Near a lattice point `z` the pole of `℘` is separated:
    -- `℘ w = 1 / (w - z) ^ 2 - 1 / z ^ 2 + ℘[L - z] w`, and `f w / (w - z)` is `dslope f z w`
    -- as `f z = 0`.
    have slope_analytic : AnalyticAt ℂ (dslope f z) z :=
      let ⟨_, hp⟩ := f_diff.analyticAt z
      hp.has_fpower_series_dslope_fslope.analyticAt
    have near : L.weierstrassPMulSq f =ᶠ[nhds z]
        dslope f z ^ 2 - (z⁻¹ • f) ^ 2 + ℘[L - z] * f ^ 2 := by
      filter_upwards [L.compl_lattice_sdiff_singleton_mem_nhds z] with w hw
      obtain rfl | hwz := eq_or_ne w z
      · simp [weierstrassPMulSq_of_mem hz, f_lattice w hz]
      · have hw_notMem : w ∉ L.lattice := fun hw_mem ↦ hw ⟨hw_mem, hwz⟩
        have slope_eq : dslope f z w = f w / (w - z) := by
          simp [dslope_of_ne f hwz, slope_def_field, f_lattice z hz]
        simp [weierstrassPMulSq_of_notMem hw_notMem, slope_eq, div_pow,
          ← L.weierstrassPExcept_add ⟨z, hz⟩ w]
        ring
    exact .congr_of_eventuallyEq (by fun_prop) near
  · -- Off the lattice `℘` is analytic.
    have weierstrassP_analytic : AnalyticAt ℂ ℘[L] z := L.analyticOnNhd_weierstrassP z hz
    exact .congr_of_eventuallyEq (f := ℘[L] * f ^ 2) (by fun_prop) <| by
      filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz] with w hw
      exact weierstrassPMulSq_of_notMem hw

/-- A theta function that vanishes at `0` vanishes on the lattice. -/
lemma theta_eq_zero_of_mem_lattice (hf : f ∈ L.hermitianForm.thetaSpace χ) (hf_zero : f 0 = 0)
    {l : ℂ} (hl : l ∈ L.lattice) : f l = 0 := by
  simpa [hf_zero] using hf.2 l hl 0

/-- If `f` is a theta function for `(H, χ)` with `f 0 = 0`, then `℘ f²` is a theta function for
`(2 H, χ²)`. Here `H` is `L.hermitianForm`. -/
lemma weierstrassPMulSq_mem_thetaSpace (hf : f ∈ L.hermitianForm.thetaSpace χ) (hf_zero : f 0 = 0) :
    L.weierstrassPMulSq f ∈ (2 • L.hermitianForm).thetaSpace (χ ^ 2) := by
  have entire : Differentiable ℂ (L.weierstrassPMulSq f) :=
    differentiable_weierstrassPMulSq hf.1 fun _ hl ↦ theta_eq_zero_of_mem_lattice hf hf_zero hl
  -- Both sides of the functional equation are entire, so it suffices to prove it off the lattice.
  -- There it is the square of the equation of `f`, times the periodic function `℘`.
  refine ⟨entire, fun l hl ↦ L.eq_of_eq_off_lattice 0 (by fun_prop) (by fun_prop) fun z hz ↦ ?_⟩
  rw [add_zero] at hz
  have periodic : ℘[L] (z + l) = ℘[L] z := L.weierstrassP_add_coe z ⟨l, hl⟩
  have factor_sq : exp (L.hermitianForm l z + L.hermitianForm l l / 2) ^ 2 =
      exp ((2 • L.hermitianForm) l z + (2 • L.hermitianForm) l l / 2) := by
    simp only [two_nsmul_hermitianForm_apply, ← exp_nat_mul]
    ring_nf
  rw [weierstrassPMulSq_of_notMem (by rwa [add_mem_cancel_right hl]), periodic, hf.2 l hl z,
    weierstrassPMulSq_of_notMem hz, Pi.pow_apply, ← factor_sq]
  ring

/-- If an entire function `f ≠ 0` vanishes on the lattice, then `f²` and `℘ f²` are linearly
independent. -/
lemma linearIndependent_sq_weierstrassPMulSq (f_diff : Differentiable ℂ f) (hf_ne : f ≠ 0)
    (f_lattice : ∀ l ∈ L.lattice, f l = 0) :
    LinearIndependent ℂ ![f ^ 2, L.weierstrassPMulSq f] := by
  -- If `℘ f² = c f²`, then `f` vanishes wherever `℘ ≠ c`, so near the pole `0`; hence `f = 0`.
  rw [LinearIndependent.pair_iff' (pow_ne_zero 2 hf_ne)]
  intro c hc
  have vanishes (z : ℂ) (hz_ne : ℘[L] z ≠ c) : f z = 0 := by
    by_cases hz : z ∈ L.lattice
    · exact f_lattice z hz
    · simpa [weierstrassPMulSq_of_notMem hz, hz_ne.symm] using congrFun hc z
  have pole : Filter.Tendsto ℘[L] (nhdsWithin 0 {0}ᶜ) (Bornology.cobounded ℂ) :=
    tendsto_cobounded_of_meromorphicOrderAt_neg (by simp +decide [order_weierstrassP])
  have frequently_zero : ∃ᶠ z : ℂ in nhdsWithin 0 {0}ᶜ, f z = 0 :=
    (pole.eventually_ne_cobounded c).frequently.mono vanishes
  exact hf_ne
    (f_diff.contDiff.analyticOnNhd.eq_of_frequently_eq analyticOnNhd_const frequently_zero)

/-- For Appell–Humbert data `(H, χ)` with `H = L.hermitianForm` and a theta function `f ≠ 0` with
`f 0 = 0`, the functions `℘ f²` (`L.weierstrassPMulSq f`) and `f²` span the theta functions for
`(2 H, χ²)`. -/
lemma IsAppellHumbert.thetaSpace_two_eq_span_pair [IsAppellHumbert L.hermitianForm χ]
    (hf : f ∈ L.hermitianForm.thetaSpace χ) (hf_ne : f ≠ 0) (hf_zero : f 0 = 0) :
    (2 • L.hermitianForm).thetaSpace (χ ^ 2) = span ℂ {L.weierstrassPMulSq f, f ^ 2} := by
  -- `f²` and `℘ f²` are independent elements of a space `V` of dimension two.
  let V : Submodule ℂ (ℂ → ℂ) := (2 • L.hermitianForm).thetaSpace (χ ^ 2)
  have dimension : finrank ℂ V = 2 := finrank_thetaSpace_nsmul
  have : FiniteDimensional ℂ V := FiniteDimensional.of_finrank_pos (by omega)
  have h_span : span ℂ {L.weierstrassPMulSq f, f ^ 2} ≤ V := span_le.2 <| pair_subset
    (weierstrassPMulSq_mem_thetaSpace hf hf_zero) (thetaSpace.pow hf 2)
  have independent : LinearIndependent ℂ ![f ^ 2, L.weierstrassPMulSq f] :=
    linearIndependent_sq_weierstrassPMulSq hf.1 hf_ne fun l hl ↦
      theta_eq_zero_of_mem_lattice hf hf_zero hl
  have span_finrank : finrank ℂ (span ℂ {L.weierstrassPMulSq f, f ^ 2}) = 2 := by
    rw [pair_comm, ← Matrix.range_cons_cons_empty (f ^ 2) (L.weierstrassPMulSq f) ![],
      finrank_span_eq_card independent, Fintype.card_fin]
  exact (eq_of_le_of_finrank_le h_span (by omega)).symm

/-- For Appell–Humbert data `(L.hermitianForm, χ)` and a theta function `f ≠ 0` with `f 0 = 0`,
the functions `℘ f²` and `f` have no common zero. -/
lemma IsAppellHumbert.weierstrassPMulSq_ne_zero [h : IsAppellHumbert L.hermitianForm χ]
    (hf : f ∈ L.hermitianForm.thetaSpace χ) (hf_ne : f ≠ 0) (hf_zero : f 0 = 0) {z : ℂ}
    (hz : f z = 0) : L.weierstrassPMulSq f z ≠ 0 := by
  -- The space of degree two has no base point: some `a ℘ f² + b f²` does not vanish at `z`.
  obtain ⟨g, hg, hg_ne⟩ : ∃ g ∈ (2 • L.hermitianForm).thetaSpace (χ ^ 2), g z ≠ 0 :=
    h.exists_mem_thetaSpace_nsmul_apply_ne_zero z 2 (by lia)
  obtain ⟨a, b, rfl⟩ := mem_span_pair.1 ((thetaSpace_two_eq_span_pair hf hf_ne hf_zero).le hg)
  exact fun h_zero ↦ hg_ne (by simp [h_zero, hz])

/-- For Appell–Humbert data `(L.hermitianForm, χ)`, the zeros of a theta function `f ≠ 0` with
`f 0 = 0` are the lattice points. -/
lemma IsAppellHumbert.theta_eq_zero_iff_mem_lattice [IsAppellHumbert L.hermitianForm χ]
    (hf : f ∈ L.hermitianForm.thetaSpace χ) (hf_ne : f ≠ 0) (hf_zero : f 0 = 0) {z : ℂ} :
    f z = 0 ↔ z ∈ L.lattice := by
  refine ⟨fun hz ↦ by_contra fun hz_notMem ↦ ?_, theta_eq_zero_of_mem_lattice hf hf_zero⟩
  -- Off the lattice `℘ f²` vanishes with `f`.
  exact weierstrassPMulSq_ne_zero hf hf_ne hf_zero hz
    (by simp [weierstrassPMulSq_of_notMem hz_notMem, hz])

/-- For Appell–Humbert data `(L.hermitianForm, χ)`, a theta function `f ≠ 0` with `f 0 = 0` has
simple zeros at the lattice points. -/
lemma IsAppellHumbert.deriv_theta_ne_zero [IsAppellHumbert L.hermitianForm χ]
    (hf : f ∈ L.hermitianForm.thetaSpace χ) (hf_ne : f ≠ 0) (hf_zero : f 0 = 0) {z : ℂ}
    (hz : z ∈ L.lattice) : deriv f z ≠ 0 := by
  simpa [weierstrassPMulSq_of_mem hz] using
    weierstrassPMulSq_ne_zero hf hf_ne hf_zero (theta_eq_zero_of_mem_lattice hf hf_zero hz)

/-- Let `(H, χ)` be Appell–Humbert data with `H = L.hermitianForm` (see `New.IsAppellHumbert`) and
`f ≠ 0` a theta function for them with `f 0 = 0`. The theorem combines three facts: the zeros of `f`
are the lattice points, they are simple, and `℘ f²` and `f²` span the theta functions for
`(2 H, χ²)`. -/
lemma IsAppellHumbert.thetaSpace_two_eq_span [IsAppellHumbert L.hermitianForm χ]
    (hf : f ∈ L.hermitianForm.thetaSpace χ) (hf_ne : f ≠ 0) (hf_zero : f 0 = 0) :
    (∀ z : ℂ, f z = 0 ↔ z ∈ L.lattice) ∧
    (∀ z ∈ L.lattice, deriv f z ≠ 0) ∧
    (2 • L.hermitianForm).thetaSpace (χ ^ 2) = span ℂ {L.weierstrassPMulSq f, f ^ 2} :=
  ⟨fun _ ↦ theta_eq_zero_iff_mem_lattice hf hf_ne hf_zero,
    fun _ ↦ deriv_theta_ne_zero hf hf_ne hf_zero, thetaSpace_two_eq_span_pair hf hf_ne hf_zero⟩

/-- If `f` is a theta function for `L.hermitianForm` and `sigmaSign L`, then so is `z ↦ f (-z)`. -/
lemma comp_neg_mem_thetaSpace (hf : f ∈ L.hermitianForm.thetaSpace (sigmaSign L)) :
    (fun z : ℂ ↦ f (-z)) ∈ L.hermitianForm.thetaSpace (sigmaSign L) := by
  refine ⟨hf.1.comp differentiable_neg, fun l hl z ↦ ?_⟩
  simpa [add_comm, sigmaSign_neg] using hf.2 (-l) (neg_mem hl) (-z)

/-- For `l = m ω₁ + ω₂`, a theta function `f` for `L.hermitianForm` and `sigmaSign L` satisfies
`f (l / 2) = -f (-l / 2)`. -/
lemma theta_half_period_eq_neg (hf : f ∈ L.hermitianForm.thetaSpace (sigmaSign L)) (m : ℤ) :
    f ((m * L.ω₁ + L.ω₂) / 2) = -f (-((m * L.ω₁ + L.ω₂) / 2)) := by
  -- At `z = -l / 2` the functional equation has exponent `0`, and `sigmaSign L l = -1`.
  set l : ℂ := m * L.ω₁ + L.ω₂
  have l_mem : l ∈ L.lattice := mem_lattice.2 ⟨m, 1, by simp [l]⟩
  have half_notMem : l / 2 ∉ L.lattice := by
    simpa [l] using (half_mem_lattice_iff_even L m 1).not
  have exponent_eq : L.hermitianForm l (-(l / 2)) + L.hermitianForm l l / 2 = 0 := by simp; ring
  have functional_eq : f (l / 2) = sigmaSign L l *
      exp (L.hermitianForm l (-(l / 2)) + L.hermitianForm l l / 2) * f (-(l / 2)) := by
    simpa [neg_add_eq_sub, sub_half, -hermitianForm_apply] using hf.2 l l_mem (-(l / 2))
  rw [exponent_eq, exp_zero, sigmaSign, ite_eq_right half_notMem] at functional_eq
  simpa using functional_eq

/-- A theta function `f ≠ 0` for `L.hermitianForm` and the multiplier `sigmaSign L` is not even. -/
lemma not_even_of_mem_thetaSpace (hf : f ∈ L.hermitianForm.thetaSpace (sigmaSign L))
    (hf_ne : f ≠ 0) : ¬ Function.Even f := by
  -- If `f` were even, it would vanish at `ω₂ / 2` and `(ω₁ + ω₂) / 2`; its translate by `ω₂ / 2`
  -- (a theta function for a shifted multiplier) would vanish at `0` and at `ω₁ / 2`, but by
  -- `theta_eq_zero_iff_mem_lattice` its zeros are the lattice points.
  intro h_even
  have half_zero (m : ℤ) : f ((m * L.ω₁ + L.ω₂) / 2) = 0 := by
    simpa [h_even _, self_eq_neg] using theta_half_period_eq_neg hf m
  let s : ℂ → ℂ := L.hermitianForm.thetaShift (L.ω₂ / 2) f
  have shift_ne : s ≠ 0 := fun s_eq ↦ hf_ne <| funext fun z ↦ by
    simpa [s, thetaShift_apply] using congrFun s_eq (z - L.ω₂ / 2)
  have shift_zero : s 0 = 0 := by simpa [s, thetaShift_apply] using half_zero 0
  have shift_half : s (L.ω₁ / 2) = 0 := by simpa [s, add_div, thetaShift_apply] using half_zero 1
  exact L.ω₁_div_two_notMem_lattice <| (theta_eq_zero_iff_mem_lattice
    (thetaShift_mem hf (L.ω₂ / 2)) shift_ne shift_zero).1 shift_half

/-- For a theta function `f ≠ 0` for `L.hermitianForm` and the multiplier `sigmaSign L`, the
function `z ↦ f z - f (-z)` is not zero. -/
lemma sub_comp_neg_ne_zero_of_mem_thetaSpace (hf : f ∈ L.hermitianForm.thetaSpace (sigmaSign L))
    (hf_ne : f ≠ 0) :
    (f - fun z : ℂ ↦ f (-z)) ≠ 0 :=
  fun h_zero ↦ not_even_of_mem_thetaSpace hf hf_ne fun z ↦
    (sub_eq_zero.1 (congrFun h_zero z)).symm

/-- There is an odd theta function with derivative `1` at `0` for `L.hermitianForm` and the
multiplier `sigmaSign L` (`1` on twice the lattice, `-1` elsewhere): an entire `f` with `f
(z + l) = sigmaSign L l * exp (H l z + H l l / 2) * f z` for lattice points `l`. Here `H` is
`L.hermitianForm`, the form `H l z = (π / A) * conj l * z` with `A` the area of the lattice.

Classically this follows from the quasi-periodicity of the Weierstrass sigma function and Legendre's
relation: every lattice has an odd entire function with derivative 1 at 0 satisfying the normalised
transformation law. -/
lemma exists_odd_mem_thetaSpace_deriv_eq_one :
    ∃ f ∈ L.hermitianForm.thetaSpace (sigmaSign L), Function.Odd f ∧ deriv f 0 = 1 := by
  -- Take `g z = f z - f (-z)` for a non-zero theta function `f` and normalise its derivative at 0.
  obtain ⟨f, hf, hf_ne⟩ := (isAppellHumbert_hermitianForm (L := L)).exists_mem_thetaSpace_ne_zero
  let g : ℂ → ℂ := f - fun z ↦ f (-z)
  have hg : g ∈ L.hermitianForm.thetaSpace (sigmaSign L) := sub_mem hf (comp_neg_mem_thetaSpace hf)
  have deriv_ne : deriv g 0 ≠ 0 :=
    deriv_theta_ne_zero hg (sub_comp_neg_ne_zero_of_mem_thetaSpace hf hf_ne) (by simp [g])
      (zero_mem _)
  refine ⟨(deriv g 0)⁻¹ • g, smul_mem _ _ hg, fun z ↦ by simp [g, mul_sub], ?_⟩
  exact (deriv_const_mul_field _).trans (inv_mul_cancel₀ deriv_ne)

/-- The sigma function of `L`: an odd theta function for `L.hermitianForm` and the multiplier
`sigmaSign L`, with derivative `1` at `0`. -/
def _root_.PeriodPair.σ (L : PeriodPair) : ℂ → ℂ :=
  (exists_odd_mem_thetaSpace_deriv_eq_one (L := L)).choose

lemma sigma_mem_thetaSpace : L.σ ∈ L.hermitianForm.thetaSpace (sigmaSign L) :=
  exists_odd_mem_thetaSpace_deriv_eq_one.choose_spec.1

/-- The functional equation of the sigma function: for a lattice point `l` and
`H = L.hermitianForm`, `σ (z + l) = sigmaSign L l * exp (H l z + H l l / 2) * σ z`. -/
lemma sigma_add_of_mem_lattice {l : ℂ} (hl : l ∈ L.lattice) (z : ℂ) :
    L.σ (z + l) = sigmaSign L l * exp (L.hermitianForm l z + L.hermitianForm l l / 2) * L.σ z :=
  sigma_mem_thetaSpace.2 l hl z

@[fun_prop]
lemma differentiable_sigma : Differentiable ℂ L.σ := sigma_mem_thetaSpace.1

@[simp]
lemma sigma_neg (z : ℂ) : L.σ (-z) = -L.σ z := by
  obtain ⟨-, h_odd, -⟩ := (exists_odd_mem_thetaSpace_deriv_eq_one (L := L)).choose_spec
  exact h_odd z

@[simp] lemma sigma_apply_zero : L.σ 0 = 0 :=
  Function.Odd.map_zero sigma_neg

@[simp] lemma deriv_sigma_zero : deriv L.σ 0 = 1 := by
  obtain ⟨-, -, h_deriv⟩ := (exists_odd_mem_thetaSpace_deriv_eq_one (L := L)).choose_spec
  exact h_deriv

lemma _root_.PeriodPair.sigma_ne_zero : L.σ ≠ 0 :=
  fun h_zero ↦ by simpa [h_zero] using deriv_sigma_zero (L := L)

/-- The sigma function `L.σ` of `L` vanishes at `z` if and only if `z` lies in the period lattice of
`L`. -/
@[simp] lemma sigma_eq_zero_iff {z : ℂ} : L.σ z = 0 ↔ z ∈ L.lattice :=
  theta_eq_zero_iff_mem_lattice sigma_mem_thetaSpace sigma_ne_zero sigma_apply_zero

/-- At every point `z` of the period lattice of `L`, the derivative of the sigma function `L.σ` is
non-zero, so the zeros of `L.σ` are simple. -/
lemma deriv_sigma_ne_zero {z : ℂ} (hz : z ∈ L.lattice) : deriv L.σ z ≠ 0 :=
  deriv_theta_ne_zero sigma_mem_thetaSpace sigma_ne_zero sigma_apply_zero hz

/-- Let H be the hermitian form (π/A)·l̄·z of the lattice of L, of area A, and χ the multiplier of σ
(1 on twice the lattice, −1 elsewhere). The entire function `℘ σ²` (`weierstrassPMulSq`) and σ²
span the theta functions for (2H, χ²). -/
lemma thetaSpace_two_eq_span_sigma :
    (2 • L.hermitianForm).thetaSpace (sigmaSign L ^ 2) =
      span ℂ {L.weierstrassPMulSq L.σ, L.σ ^ 2} :=
  thetaSpace_two_eq_span_pair sigma_mem_thetaSpace sigma_ne_zero sigma_apply_zero

/-- For every v the function z ↦ σ(z + v)σ(z − v) is a theta function for twice the hermitian form
of the lattice and the square of the multiplier of σ. -/
lemma sigma_add_mul_sigma_sub_mem_thetaSpace (v : ℂ) :
    (fun z : ℂ ↦ L.σ (z + v) * L.σ (z - v)) ∈
      (2 • L.hermitianForm).thetaSpace (sigmaSign L ^ 2) := by
  refine ⟨by fun_prop, fun l hl z ↦ ?_⟩
  -- The factors of automorphy at `z + v` and `z - v` multiply to the square of the one at `z`.
  have exponent : L.hermitianForm l (z + v) + L.hermitianForm l l / 2 +
      (L.hermitianForm l (z - v) + L.hermitianForm l l / 2) =
      (2 • L.hermitianForm) l z + (2 • L.hermitianForm) l l / 2 := by
    simp only [map_add, map_sub, two_nsmul_hermitianForm_apply]
    ring
  change L.σ (z + l + v) * L.σ (z + l - v) = (sigmaSign L ^ 2) l *
    exp ((2 • L.hermitianForm) l z + (2 • L.hermitianForm) l l / 2) * (L.σ (z + v) * L.σ (z - v))
  simp only [Pi.pow_apply, add_right_comm z l v, add_sub_right_comm z l v,
    sigma_add_of_mem_lattice hl, ← exponent, exp_add]
  ring

/-- The addition formula of the sigma function: for `u` and `v` off the lattice,
`σ (u + v) σ (u - v) = (℘ v - ℘ u) σ(u)² σ(v)²`. -/
lemma sigma_add_mul_sigma_sub {u v : ℂ} (hu : u ∉ L.lattice) (hv : v ∉ L.lattice) :
    L.σ (u + v) * L.σ (u - v) = (℘[L] v - ℘[L] u) * (L.σ u ^ 2 * L.σ v ^ 2) := by
  -- As a function of `z`, the product `σ (z + v) σ (z - v)` has degree `2`, so it is a combination
  -- `(a ℘ + b) σ²`; the values at `0` and `v` give `a` and `b`.
  obtain ⟨a, b, hab⟩ :
      ∃ a b : ℂ, a • L.weierstrassPMulSq L.σ + b • L.σ ^ 2 =
        fun z : ℂ ↦ L.σ (z + v) * L.σ (z - v) :=
    mem_span_pair.1 (thetaSpace_two_eq_span_sigma.le (sigma_add_mul_sigma_sub_mem_thetaSpace v))
  have at_zero : a = -(L.σ v * L.σ v) := by
    simpa [weierstrassPMulSq_of_mem (zero_mem L.lattice)] using congrFun hab 0
  have at_v : a * (℘[L] v * L.σ v ^ 2) + b * L.σ v ^ 2 = 0 := by
    simpa [weierstrassPMulSq_of_notMem hv] using congrFun hab v
  have at_u : a * (℘[L] u * L.σ u ^ 2) + b * L.σ u ^ 2 = L.σ (u + v) * L.σ (u - v) := by
    simpa [weierstrassPMulSq_of_notMem hu] using congrFun hab u
  have b_eq : b = -a * ℘[L] v :=
    mul_right_cancel₀ (pow_ne_zero 2 (mt sigma_eq_zero_iff.1 hv)) (by linear_combination at_v)
  linear_combination -at_u + L.σ u ^ 2 * b_eq + L.σ u ^ 2 * (℘[L] u - ℘[L] v) * at_zero

end New

end SigmaFunction

/-!
## Points of the Weierstrass cubic and derivatives of ℘

* `New.deriv_derivWeierstrassP`: `℘'' = 6 ℘² - g₂/2` off the lattice.
-/

section WeierstrassP

open PeriodPair Set Submodule New IsAppellHumbert

/-- Every complex solution (x, y) of y² = 4x³ − g₂x − g₃ is (℘(z), ℘′(z)) for some z outside the
lattice of L. -/
lemma PeriodPair.exists_weierstrassP_eq_of_cubic (L : PeriodPair) (x y : ℂ)
    (h_cubic : y ^ 2 = 4 * x ^ 3 - L.g₂ * x - L.g₃) :
    ∃ z : ℂ, z ∉ L.lattice ∧ ℘[L] z = x ∧ ℘'[L] z = y := by
  -- The theta function `(℘ - x) σ²` for `2 • L.hermitianForm` has a zero, since otherwise the
  -- Riemann form would vanish. Its zero `z` is off the lattice and has `℘ z = x`; then
  -- `℘' z = ± y` by the differential equation of `℘`, and replacing `z` by `-z` fixes the sign.
  have h_theta : L.weierstrassPMulSq L.σ - x • L.σ ^ 2 ∈
      (2 • L.hermitianForm).thetaSpace (sigmaSign L ^ 2) :=
    thetaSpace_two_eq_span_sigma.ge (mem_span_pair.2 ⟨1, -x, by module⟩)
  obtain ⟨z, h_zero⟩ : ∃ z : ℂ, (L.weierstrassPMulSq L.σ - x • L.σ ^ 2) z = 0 := by
    by_contra! h_ne
    -- The Riemann form would then vanish, but it is positive, hence nondegenerate.
    exact IsPosRiemann.nondegenerate.ne_zero (eq_exp_of_ne_zero h_theta h_ne).1
  -- On the lattice `σ z = 0`, so the value there is `σ' z ^ 2 ≠ 0`.
  have hz : z ∉ L.lattice := by
    intro hz_mem
    simp [weierstrassPMulSq_of_mem hz_mem, sigma_eq_zero_iff.2 hz_mem,
      deriv_sigma_ne_zero hz_mem] at h_zero
  have h_wp : ℘[L] z = x := by
    simpa [weierstrassPMulSq_of_notMem hz, hz, sub_eq_zero] using h_zero
  have h_sq : ℘'[L] z ^ 2 = y ^ 2 := by rw [L.derivWeierstrassP_sq z hz, h_wp, h_cubic]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h_sq with h_pos | h_neg
  · exact ⟨z, hz, h_wp, h_pos⟩
  · exact ⟨-z, by simpa, by simpa, by simp [h_neg]⟩

@[fun_prop]
lemma New.analyticAt_weierstrassP (L : PeriodPair) {z : ℂ} (hz : z ∉ L.lattice) :
    AnalyticAt ℂ ℘[L] z :=
  L.analyticOnNhd_weierstrassP z hz

@[fun_prop]
lemma New.analyticAt_derivWeierstrassP (L : PeriodPair) {z : ℂ} (hz : z ∉ L.lattice) :
    AnalyticAt ℂ ℘'[L] z :=
  L.analyticOnNhd_derivWeierstrassP z hz

/-- Duplication formula for the sigma function σ of L: for z outside the lattice,
σ(2z) = −℘′(z)·σ(z)⁴. -/
lemma New.sigma_two_mul (L : PeriodPair) {z : ℂ} (hz : z ∉ L.lattice) :
    L.σ (2 * z) = -℘'[L] z * L.σ z ^ 4 := by
  -- Differentiate `σ (z + v) σ (z - v) = (℘ v - ℘ z) (σ z)² (σ v)²` in `v`, at `v = z`. As
  -- `σ 0 = 0`, `σ' 0 = 1` and `℘ v - ℘ z` vanishes there, one term is left on each side.
  have h_deriv : deriv (fun v : ℂ ↦ L.σ (z + v) * L.σ (z - v)) z =
      deriv (fun v : ℂ ↦ (℘[L] v - ℘[L] z) * (L.σ z ^ 2 * L.σ v ^ 2)) z :=
    EqOn.deriv (fun v hv ↦ sigma_add_mul_sigma_sub hz hv) L.isClosed_lattice.isOpen_compl hz
  have key : -L.σ (z + z) = ℘'[L] z * (L.σ z ^ 2 * L.σ z ^ 2) := by
    simpa (disch := fun_prop) [deriv_comp_const_sub] using h_deriv
  rw [two_mul]
  linear_combination -key

lemma New.derivWeierstrassP_eq_zero_iff (L : PeriodPair) {z : ℂ} (hz : z ∉ L.lattice) :
    ℘'[L] z = 0 ↔ z + z ∈ L.lattice := by
  rw [← sigma_eq_zero_iff (L := L), ← two_mul, sigma_two_mul L hz]
  simp [hz]

/-- The second derivative of the Weierstrass function ℘ of L: for z outside the lattice,
℘′′(z) = 6℘(z)² − g₂/2. -/
lemma New.deriv_derivWeierstrassP (L : PeriodPair) {z : ℂ} (hz : z ∉ L.lattice) :
    deriv ℘'[L] z = 6 * ℘[L] z ^ 2 - L.g₂ / 2 := by
  have h_open : IsOpen (L.lattice : Set ℂ)ᶜ := L.isClosed_lattice.isOpen_compl
  -- Differentiate `℘' ^ 2 = 4 ℘ ^ 3 - g₂ ℘ - g₃`; where `℘'` is not zero, divide by `2 ℘'`.
  have h_first (w : ℂ) (hw : w ∉ L.lattice) :
      2 * ℘'[L] w * deriv ℘'[L] w = 4 * (3 * ℘[L] w ^ 2 * ℘'[L] w) - L.g₂ * ℘'[L] w := by
    simpa (disch := fun_prop) using EqOn.deriv L.derivWeierstrassP_sq h_open hw
  rcases ne_or_eq (℘'[L] z) 0 with h_ne | h_zero
  · apply mul_left_cancel₀ (mul_ne_zero two_ne_zero h_ne)
    linear_combination h_first z hz
  -- At a zero of `℘'`, differentiate once more; only the terms free of `℘'` remain.
  have h_second : 2 * deriv ℘'[L] z * deriv ℘'[L] z =
      4 * (3 * ℘[L] z ^ 2 * deriv ℘'[L] z) - L.g₂ * deriv ℘'[L] z := by
    simpa (disch := fun_prop) [h_zero] using EqOn.deriv h_first h_open hz
  -- There `℘''` is not zero: `2 z` is a lattice point, a simple zero of `σ`, and the derivative of
  -- the duplication formula reads `2 σ' (2 z) = -℘'' z σ z ^ 4`.
  have h_simple : deriv L.σ (2 * z) ≠ 0 :=
    deriv_sigma_ne_zero (by simpa [two_mul] using (derivWeierstrassP_eq_zero_iff L hz).1 h_zero)
  have h_sigma : 2 * deriv L.σ (2 * z) = -(deriv ℘'[L] z * L.σ z ^ 4) := by
    simpa (disch := fun_prop) [deriv_comp_mul_left, h_zero] using
      EqOn.deriv (fun w hw ↦ sigma_two_mul L hw) h_open hz
  apply mul_left_cancel₀ (fun h_eq ↦ h_simple (by simpa [h_eq] using h_sigma) : deriv ℘'[L] z ≠ 0)
  linear_combination h_second / 2

end WeierstrassP

/-!
## Lattices with complex multiplication and their coordinates

* `New.CMLattice.translatedX`, `New.CMLattice.translatedY`: the coordinates
  `x = ℘(z + t) - ℘(t)` and `y = (℘'(z + t) - a₁ x) / 2`.
-/

section CMLatticeDefs

open Complex PeriodPair ComplexConjugate NumberField

namespace New

/-! ### Taylor series -/

/-- The Taylor series ∑ f⁽ⁿ⁾(0) zⁿ/n! at 0 of a function f : ℂ → ℂ, as a formal power series. -/
def taylorAtZero (f : ℂ → ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun n ↦ iteratedDeriv n f 0 / n.factorial

/-- The Taylor series of f at 0 with the ring homomorphism ι : ℂ → K applied to its
coefficients. -/
abbrev taylorVia {K : Type*} [Semiring K] (ι : ℂ →+* K) (f : ℂ → ℂ) : PowerSeries K :=
  (taylorAtZero f).map ι

/-- The linear form ∑ c_i z_i, as a power series in the variables z_i. -/
def linearSeries {ι R : Type*} [Fintype ι] [CommSemiring R] (c : ι → R) : MvPowerSeries ι R :=
  ∑ i : ι, c i • MvPowerSeries.X i

/-! ### Lattices with complex multiplication -/

/-- The complex number ω = (1 + i√d)/2. -/
def quadGen (d : ℕ) : ℂ := (1 + I * √d) / 2

/-- The image in ℂ of the ring of integers of K = ℚ(i√d), as a subring of ℂ. -/
def quadInt (d : ℕ) : Subring ℂ :=
  ((algebraMap (QuadField d) ℂ).comp (algebraMap (𝓞 (QuadField d)) (QuadField d))).range

/-- A lattice `Λ` with a point `t` of order two modulo `Λ`, scaled so that `℘''(t) = 2`, and a
square root `a₁` of `12 ℘(t)`. If `d ≠ 0`, then moreover `Λ` is stable under the ring of integers of
`ℚ(√-d)`, and neither `ω t` nor `ω̄ t` lies in `Λ`, where `ω = (1 + √-d) / 2`. For `d = 0` these two
conditions are void. -/
structure CMLattice (d : ℕ) extends periodPair : PeriodPair where
  /-- The point `t`, of order two modulo the lattice. -/
  t : ℂ
  /-- A square root of `12 ℘(t)`. -/
  a₁ : ℂ
  /-- The scaling of the lattice: `g₂ = 12 ℘(t)² - 4`, which says `℘''(t) = 2` because
  `℘'' = 6 ℘² - g₂ / 2` off the lattice. -/
  g₂_eq : periodPair.g₂ = 12 * ℘[periodPair] t ^ 2 - 4
  /-- If `d ≠ 0`, the lattice is stable under the ring of integers of `ℚ(√-d)`. -/
  mul_mem_of_quadInt [NeZero d] {a : ℂ} :
      a ∈ quadInt d → ∀ ⦃x : ℂ⦄, x ∈ periodPair.lattice → a * x ∈ periodPair.lattice
  /-- `2 t` lies in the lattice. -/
  two_t_mem : t + t ∈ periodPair.lattice
  /-- `t` does not lie in the lattice. -/
  t_notMem : t ∉ periodPair.lattice
  /-- If `d ≠ 0`, neither `ω t` nor `ω̄ t` lies in the lattice, where `ω = (1 + √-d) / 2`. -/
  quadGen_mul_t_notMem [NeZero d] :
      quadGen d * t ∉ periodPair.lattice ∧ conj (quadGen d) * t ∉ periodPair.lattice
  /-- `a₁² = 12 ℘(t)`. -/
  a₁_sq : a₁ ^ 2 = 12 * ℘[periodPair] t

namespace CMLattice

variable {d : ℕ} (C : CMLattice d) (m : ℕ)

/-! ### Sections and the functions θ, x, y -/

/-- The period lattice Λ ⊂ ℂ of `C`. -/
abbrev Λ : Submodule ℤ ℂ := C.lattice

/-- The twisted translation T of degree m by the point y, for the form mH with
H = `C.hermitianForm`: (T f)(z) = exp(−mπ(zȳ + |y|²/2)/A)·f(z + y), A the area of Λ. -/
abbrev twistedTranslate (y : ℂ) (f : ℂ → ℂ) : ℂ → ℂ := (m • C.hermitianForm).thetaShift y f

/-- The multiplier χ : l ↦ ±exp(2πi E(l,t)), with sign + exactly when l/2 ∈ Λ, and E the Riemann
form of H = `C.hermitianForm`. -/
def multiplier (l : ℂ) : ℂ := sigmaSign C.periodPair l * C.hermitianForm.riemannPhase l C.t

/-- The sections of degree m: theta functions for the lattice Λ with hermitian form mH and
multiplier χ^m. -/
abbrev sections : Submodule ℂ (ℂ → ℂ) := (m • C.hermitianForm).thetaSpace (C.multiplier ^ m)

/-- The function z ↦ (T_tσ)(z)/(T_tσ)(0): the twisted translate of the sigma function by the
2-torsion point t, normalised to 1 at 0. -/
def θ (z : ℂ) : ℂ := C.twistedTranslate 1 C.t C.σ z / C.twistedTranslate 1 C.t C.σ 0

/-- The function x(z) = ℘(z + t) − ℘(t) for the lattice Λ and its 2-torsion point t. -/
def translatedX (z : ℂ) : ℂ := ℘[C.periodPair] (z + C.t) - ℘[C.periodPair] C.t

/-- The function y(z) = ½(℘′(z + t) − a₁x(z)), where x(z) = ℘(z + t) − ℘(t). -/
def translatedY (z : ℂ) : ℂ := (℘'[C.periodPair] (z + C.t) - C.a₁ * C.translatedX z) / 2

/-- The entire function G = σ·(σ′θ − σ·(θ′ + ½a₁θ)), written as a pointwise product of functions. It
equals yθ³ off t + Λ, with y = `C.translatedY`. -/
def translatedYThetaCube : ℂ → ℂ := C.σ * (deriv C.σ * C.θ - C.σ * (deriv C.θ + (C.a₁ / 2) • C.θ))

/-- The function `y = C.translatedY`, given by `y(z) = ½(℘′(z + t) − a₁(℘(z + t) − ℘(t)))`, vanishes
at `0`, since `℘'` vanishes at the point `t` of order two. -/
@[simp]
lemma translatedY_zero : C.translatedY 0 = 0 := by
  have h_two : ℘'[C.periodPair] C.t = 0 :=
    (derivWeierstrassP_eq_zero_iff C.periodPair C.t_notMem).2 C.two_t_mem
  simp [translatedY, translatedX, h_two]

end CMLattice

end New

end CMLatticeDefs

/-!
## The invariants g₂, g₃, Δ and lattices with given invariants

* `New.weierstrass_disc_ne_zero`: g₂³ − 27 g₃² ≠ 0, because Δ has no zero.
-/

section LatticeInvariants

open UpperHalfPlane ModularForm ModularFormClass EisensteinSeries PeriodPair Real Complex
open scoped MatrixGroups

namespace New

/-- The area of the period parallelogram is |ω₂|²·|Im(ω₁/ω₂)|. -/
lemma area_eq_norm_sq_mul_abs_im (L : PeriodPair) :
    L.area = ‖L.ω₂‖ ^ 2 * |(L.ω₁ * L.ω₂⁻¹).im| := by
  have hω₂ : normSq L.ω₂ ≠ 0 := normSq_eq_zero.not.2 (L.indep.ne_zero 1)
  have h_im : -((starRingEnd ℂ) L.ω₁ * L.ω₂).im = normSq L.ω₂ * (L.ω₁ * L.ω₂⁻¹).im := by
    simp only [mul_im, conj_re, conj_im, inv_re, inv_im]
    field
  rw [area, ← abs_neg, h_im, abs_mul, abs_of_nonneg (normSq_nonneg L.ω₂), normSq_eq_norm_sq]

/-- The special value ζ(6) = π⁶/945. -/
lemma riemannZeta_six_eq : riemannZeta 6 = π ^ 6 / 945 := by
  have h_bernoulli : bernoulli 6 = 42⁻¹ := by cbv
  have h_value := riemannZeta_two_mul_nat (k := 3) three_ne_zero
  norm_num [h_bernoulli, Nat.factorial] at h_value
  linear_combination h_value

/-- Every period lattice is a(ℤτ + ℤ) with a ≠ 0 and τ in the upper half plane: e enumerates it by
(m, n) ↦ a(mτ + n). The area of its period parallelogram (`PeriodPair.area`) is then |a|² Im τ. -/
lemma exists_lattice_eq_mul_tau (L : PeriodPair) :
    ∃ (a : ℂ) (τ : ℍ) (e : ℤ × ℤ ≃ L.lattice),
      (∀ p : ℤ × ℤ, (e p : ℂ) = a * (p.1 * τ + p.2)) ∧
      a ≠ 0 ∧
      L.area = ‖a‖ ^ 2 * τ.im := by
  have hω₂ : L.ω₂ ≠ 0 := L.indep.ne_zero 1
  -- Take `a = ω₂` and `τ = k ω₁ / ω₂`, the sign `k` chosen to make the imaginary part positive.
  obtain ⟨k, hk⟩ : ∃ k : ℤˣ, |(L.ω₁ * L.ω₂⁻¹).im| = ((k : ℤˣ) * L.ω₁ * L.ω₂⁻¹).im := by
    obtain h_pos | h_neg := abs_choice (L.ω₁ * L.ω₂⁻¹).im
    · exact ⟨1, by simpa using h_pos⟩
    · exact ⟨-1, by simpa [add_comm] using h_neg⟩
  let ratio : ℂ := (k : ℤˣ) * L.ω₁ * L.ω₂⁻¹
  have h_area : L.area = ‖L.ω₂‖ ^ 2 * ratio.im := by rw [area_eq_norm_sq_mul_abs_im, hk]
  have h_im : 0 < ratio.im :=
    pos_of_mul_pos_right ((area_pos L).trans_eq h_area) (sq_nonneg ‖L.ω₂‖)
  let e : ℤ × ℤ ≃ L.lattice := (k.mulLeft.prodCongr 1).trans L.latticeEquivProd.symm.toEquiv
  refine ⟨L.ω₂, ⟨ratio, h_im⟩, e, fun p ↦ ?_, hω₂, h_area⟩
  calc (e p : ℂ) = (k : ℤˣ) * p.1 * L.ω₁ + p.2 * L.ω₂ := by simp [e, latticeEquiv_symm_apply]
    _ = L.ω₂ * (p.1 * ratio + p.2) := by simp [ratio, field]

/-- If the lattice of L is a(ℤτ + ℤ), enumerated by e, then for k ≥ 3 the lattice sum `L.G k` of the
k-th inverse powers is 2ζ(k)E_k(τ)/aᵏ, where E_k is the normalised Eisenstein series of weight k. -/
lemma G_eq_riemannZeta_mul_eisenstein {L : PeriodPair} {a : ℂ} {τ : ℍ} {e : ℤ × ℤ ≃ L.lattice}
    (h_enum : ∀ p : ℤ × ℤ, (e p : ℂ) = a * (p.1 * τ + p.2)) {k : ℕ} (hk : 3 ≤ k) :
    L.G k = 2 * riemannZeta k * E hk τ / a ^ k := by
  -- The sum over all pairs is `ζ(k)` times the sum over coprime pairs, which is `2 E_k`.
  have h_scale : L.G k = (a ^ k)⁻¹ * ∑' v : Fin 2 → ℤ, eisSummand k v τ := by
    simp [G, ← ((finTwoArrowEquiv ℤ).trans e).tsum_eq, h_enum, eisSummand, mul_pow, tsum_mul_left,
      mul_comm]
  rw [h_scale, tsum_eisSummand_eq_riemannZeta_mul_eisensteinSeries hk,
    show E hk τ = 1 / 2 * eisensteinSeries (N := 1) 0 k τ from rfl]
  ring

/-- If the lattice of L is a(ℤτ + ℤ), enumerated by e, then g₂ = (2π/a)⁴ E₄(τ)/12, where E₄ is the
normalised Eisenstein series of weight 4. -/
lemma g₂_eq_eisenstein {L : PeriodPair} {a : ℂ} {τ : ℍ} {e : ℤ × ℤ ≃ L.lattice}
    (h_enum : ∀ p : ℤ × ℤ, (e p : ℂ) = a * (p.1 * τ + p.2)) :
    L.g₂ = (2 * π / a) ^ 4 * E₄ τ / 12 := by
  have h_G : L.G 4 = 2 * riemannZeta 4 * E₄ τ / a ^ 4 :=
    G_eq_riemannZeta_mul_eisenstein h_enum (show 3 ≤ 4 by norm_num)
  rw [g₂, h_G, riemannZeta_four]
  ring

/-- If the lattice of L is a(ℤτ + ℤ), enumerated by e, then g₃ = (2π/a)⁶ E₆(τ)/216, where E₆ is the
normalised Eisenstein series of weight 6. -/
lemma g₃_eq_eisenstein {L : PeriodPair} {a : ℂ} {τ : ℍ} {e : ℤ × ℤ ≃ L.lattice}
    (h_enum : ∀ p : ℤ × ℤ, (e p : ℂ) = a * (p.1 * τ + p.2)) :
    L.g₃ = (2 * π / a) ^ 6 * E₆ τ / 216 := by
  have h_G : L.G 6 = 2 * riemannZeta 6 * E₆ τ / a ^ 6 :=
    G_eq_riemannZeta_mul_eisenstein h_enum (show 3 ≤ 6 by norm_num)
  rw [g₃, h_G, riemannZeta_six_eq]
  ring

/-- If the lattice of L is a(ℤτ + ℤ), enumerated by e, then g₂³ − 27 g₃² = (2π/a)¹² Δ(τ), where Δ
is the modular discriminant. -/
lemma g₂_pow_three_sub_g₃_sq_eq_discriminant {L : PeriodPair} {a : ℂ} {τ : ℍ}
    {e : ℤ × ℤ ≃ L.lattice} (h_enum : ∀ p : ℤ × ℤ, (e p : ℂ) = a * (p.1 * τ + p.2)) :
    L.g₂ ^ 3 - 27 * L.g₃ ^ 2 = (2 * π / a) ^ 12 * discriminant τ := by
  -- The discriminant is `(E₄³ - E₆²) / 1728`.
  rw [g₂_eq_eisenstein h_enum, g₃_eq_eisenstein h_enum, discriminant_eq_E₄_cube_sub_E₆_sq]
  ring

lemma weierstrass_disc_ne_zero (L : PeriodPair) : g₂ L ^ 3 - 27 * g₃ L ^ 2 ≠ 0 := by
  obtain ⟨a, τ, e, h_enum, ha, -⟩ := exists_lattice_eq_mul_tau L
  rw [g₂_pow_three_sub_g₃_sq_eq_discriminant h_enum]
  simp [ha, discriminant_ne_zero]

/-- For τ in the upper half plane and w ≠ 0 some period lattice has the invariants
g₂ = w⁴E₄(τ)/12 and g₃ = w⁶E₆(τ)/216. The proof uses the lattice (2π/w)(ℤτ + ℤ). -/
lemma exists_g₂_g₃_eq_pow_mul_eisenstein (τ : ℍ) {w : ℂ} (hw : w ≠ 0) :
    ∃ L : PeriodPair, g₂ L = w ^ 4 * E₄ τ / 12 ∧ g₃ L = w ^ 6 * E₆ τ / 216 := by
  have h_indep : LinearIndependent ℝ ![(τ : ℂ) * (2 * π / w), 2 * π / w] := by
    -- A relation `s τ c + t c = 0` with `c ≠ 0` gives `s τ + t = 0`; take imaginary parts.
    refine LinearIndependent.pair_iff.2 fun s t h_rel ↦ ?_
    have h_comb : s * (τ : ℂ) + t = 0 := by
      apply mul_right_cancel₀ (show (2 * π / w : ℂ) ≠ 0 by simp [hw])
      simp only [real_smul] at h_rel
      linear_combination h_rel
    have hs : s = 0 := by simpa [τ.im_ne_zero] using congrArg Complex.im h_comb
    exact ⟨hs, by simpa [hs] using h_comb⟩
  let L : PeriodPair := ⟨τ * (2 * π / w), 2 * π / w, h_indep⟩
  have h_enum (p : ℤ × ℤ) :
      (L.latticeEquivProd.symm.toEquiv p : ℂ) = 2 * π / w * (p.1 * τ + p.2) := by
    simp [L, latticeEquiv_symm_apply, field]
  exact ⟨L, by simp [g₂_eq_eisenstein h_enum, field], by simp [g₃_eq_eisenstein h_enum, field]⟩

/-- If a³ − 27b² ≠ 0 and E₄(τ)³·(a³ − 27b²) = (12a)³·Δ(τ) at a point τ of the upper half plane,
then some period lattice has g₂ = a and g₃ = b. -/
lemma exists_lattice_of_E₄_cube_mul_eq {a b : ℂ} {τ : ℍ} (h_ne : a ^ 3 - 27 * b ^ 2 ≠ 0)
    (h_disc : E₄ τ ^ 3 * (a ^ 3 - 27 * b ^ 2) = (12 * a) ^ 3 * discriminant τ) :
    ∃ L : PeriodPair, g₂ L = a ∧ g₃ L = b := by
  have hΔ : discriminant τ = (E₄ τ ^ 3 - E₆ τ ^ 2) / 1728 := discriminant_eq_E₄_cube_sub_E₆_sq τ
  by_cases hE : E₄ τ = 0
  · -- Then `a = 0`; scale so that `g₃ = b`.
    have ha : a = 0 := by simpa [hE, discriminant_ne_zero] using h_disc.symm
    have hb : b ≠ 0 := by simpa [ha] using h_ne
    have hE₆ : E₆ τ ≠ 0 := fun h_six ↦ discriminant_ne_zero τ (by simp [hΔ, hE, h_six])
    obtain ⟨w, hw⟩ : ∃ w : ℂ, w ^ 6 = 216 * b / E₆ τ := IsSepClosed.exists_pow_nat_eq _ 6
    have hw_ne : w ≠ 0 := ne_zero_pow (n := 6) (by norm_num) (by simp [hw, hb, hE₆])
    obtain ⟨L, h₂, h₃⟩ := exists_g₂_g₃_eq_pow_mul_eisenstein τ hw_ne
    exact ⟨L, by simp [h₂, hE, ha], by simp [h₃, hw, field]⟩
  · -- Scale by `c` so that `g₂ = a`; then `g₃ = ± b`, and `c * I` changes the sign of `g₃` only.
    have ha : a ≠ 0 := fun ha_zero ↦
      mul_ne_zero (pow_ne_zero 3 hE) h_ne (by simpa [ha_zero] using h_disc)
    obtain ⟨c, hc⟩ : ∃ c : ℂ, c ^ 4 = 12 * a / E₄ τ := IsSepClosed.exists_pow_nat_eq _ 4
    have hc_ne : c ≠ 0 := ne_zero_pow (n := 4) (by norm_num) (by simp [hc, ha, hE])
    have h_g₂ : c ^ 4 * E₄ τ / 12 = a := by simp [hc, field]
    -- Both `(g₂, g₃)` and `(a, b)` satisfy `g₂³ : (g₂³ - 27 g₃²) = E₄³ : 12³ Δ`, so the two `g₃`
    -- have equal squares.
    have h_sq : (c ^ 6 * E₆ τ / 216) ^ 2 = b ^ 2 := by
      have h_twelve : (c ^ 4) ^ 3 * E₄ τ ^ 3 = (12 * a) ^ 3 := by simp [hc, field]
      apply mul_right_cancel₀ (pow_ne_zero 3 hE)
      linear_combination (E₆ τ ^ 2 / 216 ^ 2) * h_twelve +
        (1728 * (12 * a) ^ 3 / 216 ^ 2) * hΔ + (1728 / 216 ^ 2) * h_disc
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h_sq with h_pos | h_neg
    · obtain ⟨L, h₂, h₃⟩ := exists_g₂_g₃_eq_pow_mul_eisenstein τ hc_ne
      exact ⟨L, h₂.trans h_g₂, h₃.trans h_pos⟩
    · obtain ⟨L, h₂, h₃⟩ :=
        exists_g₂_g₃_eq_pow_mul_eisenstein τ (mul_ne_zero hc_ne Complex.I_ne_zero)
      refine ⟨L, by simpa [mul_pow, h_g₂] using h₂, ?_⟩
      rw [h₃, mul_pow, show Complex.I ^ 6 = -1 by norm_num [pow_succ]]
      linear_combination -h_neg

/-- A modular form `g` of weight 12 for the full modular group (`𝒮ℒ`, the image of SL₂(ℤ) in
GL₂(ℝ)) that tends to 1 at the cusp `i∞` has a zero in the upper half plane. -/
lemma exists_eq_zero_of_weight_twelve_of_tendsto_one (g : ModularForm 𝒮ℒ 12)
    (h_lim : Filter.Tendsto g atImInfty (nhds 1)) : ∃ τ : ℍ, g τ = 0 := by
  -- Otherwise `g⁻¹` is a modular form of weight `-12`, hence zero: absurd.
  by_contra! h_ne
  have h_slash (γ : SL(2, ℤ)) :
      (fun τ ↦ (g τ)⁻¹) ∣[(-12 : ℤ)] Matrix.SpecialLinearGroup.mapGL ℝ γ = fun τ ↦ (g τ)⁻¹ := by
    simp [slash_def, UpperHalfPlane.σ, SlashInvariantForm.slash_action_eqn'' g]
  have h_bdd : IsBoundedAtImInfty fun τ ↦ (g τ)⁻¹ := (h_lim.inv₀ one_ne_zero).isBigO_one ℝ
  let g_inv : ModularForm 𝒮ℒ (-12) :=
    { toFun := fun τ ↦ (g τ)⁻¹
      slash_action_eq' := Set.forall_mem_range.2 h_slash
      holo' := g.holo'.inv h_ne
      bdd_at_cusps' := fun hc ↦
        (OnePoint.isBoundedAt_iff_forall_SL2Z hc).2 fun γ _ ↦ by rwa [← h_slash γ] at h_bdd }
  exact inv_ne_zero (h_ne UpperHalfPlane.I)
    (congrFun (levelOne_neg_weight_eq_zero (by norm_num) g_inv) UpperHalfPlane.I)

/-- The Eisenstein series E₄ tends to 1 at the cusp i∞. -/
lemma tendsto_E₄_atImInfty : Filter.Tendsto E₄ atImInfty (nhds 1) := by
  have hE : Filter.Tendsto E₄ atImInfty (nhds (valueAtInfty E₄)) :=
    tendsto_sub_nhds_zero_iff.1 (IsZeroAtImInfty.of_exp_decay (exp_decay_sub_atImInfty' E₄))
  -- The value at the cusp is the constant term 1 of the `q`-expansion with period 1.
  have h_one : (qExpansion 1 E₄).coeff 0 = 1 :=
    E_qExpansion_coeff_zero (show 3 ≤ 4 by norm_num) (show Even 4 by decide)
  rwa [← h_one, qExpansion_coeff_zero one_pos
    (ModularFormClass.analyticAt_cuspFunction_zero E₄ one_pos one_mem_strictPeriods_SL)
    (SlashInvariantFormClass.periodic_comp_ofComplex E₄ one_mem_strictPeriods_SL)]

/-- For complex numbers a, b with a³ − 27b² ≠ 0 there is a period lattice L with Weierstrass
invariants g₂(L) = a and g₃(L) = b.
This is the existence part of the uniformisation theorem for elliptic curves over ℂ. -/
lemma exists_lattice_of_g₂_g₃ {a b : ℂ} (h_ne : a ^ 3 - 27 * b ^ 2 ≠ 0) :
    ∃ L : PeriodPair, g₂ L = a ∧ g₃ L = b := by
  -- The form `g = E₄³ - c Δ` of weight 12, with `c = (12 a)³ / (a³ - 27 b²)`, tends to 1 at the
  -- cusp, so it has a zero `τ`; a suitable multiple of `ℤ τ + ℤ` then has both invariants.
  let c : ℂ := (12 * a) ^ 3 / (a ^ 3 - 27 * b ^ 2)
  let E₄_cube : ModularForm 𝒮ℒ 12 := E₄.pow 3
  let g : ModularForm 𝒮ℒ 12 := E₄_cube - c • modularForm CuspForm.discriminant
  have g_apply (τ : ℍ) : g τ = E₄ τ ^ 3 - c * discriminant τ := by simp [g, E₄_cube, (coe_pow)]
  obtain ⟨τ, h_zero⟩ : ∃ τ : ℍ, g τ = 0 := exists_eq_zero_of_weight_twelve_of_tendsto_one g <| by
    simpa [funext g_apply] using
      (tendsto_E₄_atImInfty.pow 3).sub (discriminant_isZeroAtImInfty.const_mul c)
  have h_disc : E₄ τ ^ 3 * (a ^ 3 - 27 * b ^ 2) = (12 * a) ^ 3 * discriminant τ := by
    rw [g_apply, sub_eq_zero] at h_zero
    rw [h_zero, mul_right_comm, div_mul_cancel₀ _ h_ne]
  exact exists_lattice_of_E₄_cube_mul_eq h_ne h_disc

end New

end LatticeInvariants

end
