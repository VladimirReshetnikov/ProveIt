import Lib.CM.Integrality.TorsionValues

/-!
# Integral series rings 𝔬[[T]], congruence parts of power series, a functional equation

Let `𝔬` (`New.valRingCp p`) be the valuation ring of `ℂ_[p]`, and let `𝔬[[X]]` be the range of the
inclusion `New.seriesToCp` into `ℂ_[p]⟦X⟧`. For a series `T = X + ⋯`, the file studies the ring
`𝔬[[T]]` of integral series in `T`. For the coordinate `y` of a CM curve, it shows that `𝔬[[y]]`
contains `x` and is stable under `d/dz`. It then treats the part of a series in the degrees of one
class mod `m`, and the integrality of the solutions of a functional equation `Y(π z) = π G(Y)`.

## Main definitions and results

* `New.IsSeriesGenerator A T`: the series `T = X + ⋯` generates `A`, that is, `A = 𝔬[[T]]`. Such a
  ring is closed under integral scalars. It is closed under `f ↦ f(a X)` when it contains `T(a X)`.
  Its elements whose constant term has norm `1` are invertible. Any series `f = X + ⋯` in `A`
  generates it too (`New.IsSeriesGenerator.of_mem`).
* `New.CMLattice.integralSeriesRing C`: the ring `𝔬[[y]]`. Here `y` (`New.CMLattice.translatedY`)
  and `x` (`New.CMLattice.translatedX`) are the coordinates of the CM curve `y² + a₁ x y = x³ + x`.
  `New.taylorVia ιₚ f` is the Taylor series of `f` at `0` with the p-adic place `ιₚ : ℂ →+* ℂ_[p]`
  applied to the coefficients.
* `New.CMLattice.taylorVia_translatedX_mem_integralSeriesRing`,
  `New.CMLattice.derivative_mem_integralSeriesRing`: `𝔬[[y]]` contains `x` and is stable under
  `d/dz`.
* `New.congruencePart_eq_sum`: for `m ≠ 0`, the part of a series in the degrees of one class mod `m`
  is a mean over the `m`-th roots of unity; `New.congruencePart_subst`: taking it commutes with the
  substitution of a series `T` with `T(0) = 0` that has only degrees `≡ 1` mod `m`.
* `New.exists_seriesToCp_eq_of_rescale_eq`: for `0 < |π| < 1`, `q > 1` and `E` integral of order at
  least two, a solution `Y = z + ⋯` of `Y(π z) / π = Y - Y ^ q + π E(Y)` is integral, by induction
  on the degree (`New.mem_range_seriesToCp_of_rescale_eq_X_sub_X_pow`), and `Y - Y ^ q ≡ z` modulo
  `π` (`New.C_dvd_sub_pow_sub_X_of_rescale_eq`).
* `New.dvd_coeff_sub_of_C_dvd_sub_pow_sub_X`: let `π` be a non-unit dividing `p` and `q > 1` a power
  of `p`. If `Y(0) = 0` and `Y - Y ^ q ≡ z` modulo `π`, then `Y ≡ ∑ z ^ q ^ j` modulo `π`.

Notions from other files:
* `New.CMLattice d`: a lattice `Λ` stable under the integers of `ℚ(√-d)`, with a point `t` of order
  two modulo `Λ` such that `ω t`, `ω̄ t ∉ Λ` for `ω = (1 + √-d) / 2`, scaled so that `℘''(t) = 2`,
  and a square root `a₁` of `12 ℘(t)`.
* `New.PrimeSevenModEight d`: the number `d` is a prime congruent to `7` modulo `8`.

## Relation to the literature

Known result: elementary facts on power series; the induction is that of the functional equation of
a Lubin–Tate group. Source: Lubin–Tate, Formal complex multiplication in local fields.

The statements on the CM curve use only that `a₁` is integral; `x ∈ 𝔬[[y]]` is Hensel's lemma for
the cubic.
-/

/-! ## Rings of integral series in a generating parameter -/

section IntegralParameter

open PowerSeries WithPiTopology

namespace New

variable {p : ℕ} [Fact p.Prime]

lemma seriesToCp_eq_map (g : (valRingCp p)⟦X⟧) :
    seriesToCp g = PowerSeries.map (valRingCp p).subtype g := rfl

lemma coeff_seriesToCp (n : ℕ) (g : (valRingCp p)⟦X⟧) :
    coeff n (seriesToCp g) = (coeff n g : valRingCp p) := rfl

lemma constantCoeff_seriesToCp (g : (valRingCp p)⟦X⟧) :
    constantCoeff (seriesToCp g) = (constantCoeff g : valRingCp p) := rfl

lemma derivative_seriesToCp (g : (valRingCp p)⟦X⟧) :
    d⁄dX (seriesToCp g) = seriesToCp (d⁄dX g) :=
  (map_pderiv (valRingCp p).subtype () g).symm

/-- The series `T = X + ⋯` generates the subring `A` of `ℂ_[p]⟦X⟧`: `A = 𝔬[[T]]` consists exactly
of the `g(T)` with `g` a series over the valuation ring `𝔬` of `ℂ_[p]`. -/
structure IsSeriesGenerator (A : Subring ℂ_[p]⟦X⟧) (T : ℂ_[p]⟦X⟧) : Prop where
  /-- The constant term of `T` is `0`. -/
  constantCoeff_eq_zero : constantCoeff T = 0
  /-- The linear coefficient of `T` is `1`. -/
  coeff_one : coeff 1 T = 1
  /-- The elements of `A` are the series `g(T)` with `g` integral. -/
  mem_iff (f : ℂ_[p]⟦X⟧) : f ∈ A ↔ ∃ g : (valRingCp p)⟦X⟧, f = subst T (seriesToCp g)

@[simp]
lemma constantCoeff_rescale {a : ℂ_[p]} {f : ℂ_[p]⟦X⟧} :
    (rescale a f).constantCoeff = f.constantCoeff := by simp [rescale]

@[simp]
lemma rescale_smul {a c : ℂ_[p]} {f : ℂ_[p]⟦X⟧} : rescale a (c • f) = c • rescale a f := by
  ext n
  simp [mul_left_comm]

/-- The series `f(T)` and `f` have the same constant term, if `T(0) = 0`. -/
@[simp]
lemma constantCoeff_subst_eq {T : ℂ_[p]⟦X⟧} (hT₀ : T.constantCoeff = 0) {f : ℂ_[p]⟦X⟧} :
    constantCoeff (f.subst T) = f.constantCoeff :=
  constantCoeff_subst_of_constantCoeff_eq_zero T hT₀ f

/-- The linear coefficient of `f(T)` is the product of those of `f` and `T`, if `T(0) = 0`. -/
lemma coeff_one_subst {T : ℂ_[p]⟦X⟧} (hT₀ : T.constantCoeff = 0) {f : ℂ_[p]⟦X⟧} :
    coeff 1 (f.subst T) = f.coeff 1 * T.coeff 1 := by
  -- Only the power `T ^ 1` contributes to degree one, as `T` has no constant term.
  have h_pow (n : ℕ) (hn : n ≠ 1) : coeff 1 (T ^ n) = 0 := by
    rcases n with _ | _ | n <;> simp_all [coeff_one_pow]
  rw [coeff_subst' (.of_constantCoeff_zero' hT₀), finsum_eq_single _ 1, pow_one, smul_eq_mul]
  simp +contextual [h_pow]

/-- Substituting `a X` in `f(T)` gives `f(T(a X))`, if `T(0) = 0`. -/
lemma rescale_subst {a : ℂ_[p]} {T : ℂ_[p]⟦X⟧} (hT₀ : T.constantCoeff = 0) {f : ℂ_[p]⟦X⟧} :
    rescale a (f.subst T) = f.subst (rescale a T) := by
  rw [rescale_eq_subst, rescale_eq_subst,
    subst_comp_subst_apply (.of_constantCoeff_zero' hT₀) (.of_constantCoeff_zero' (by simp))]

/-- For integral series `F`, `G` and a series `T` with `F(0) = T(0) = 0`, the composite `G ∘ F`
formed over `𝔬` satisfies `(G ∘ F)(T) = G(F(T))`. -/
lemma subst_seriesToCp_subst {T : ℂ_[p]⟦X⟧} (hT₀ : constantCoeff T = 0) {F : (valRingCp p)⟦X⟧}
    (hF₀ : constantCoeff F = 0) (G : (valRingCp p)⟦X⟧) :
    subst T (seriesToCp (subst F G)) = subst (subst T (seriesToCp F)) (seriesToCp G) := by
  rw [map_subst (.of_constantCoeff_zero' hF₀), ← seriesToCp_eq_map, subst_comp_subst_apply
    (.of_constantCoeff_zero' (by simp [constantCoeff_seriesToCp, hF₀]))
    (.of_constantCoeff_zero' hT₀)]

/-- If `T` may be substituted into series, the substitution `f ↦ f(T)` is continuous for the
topology of coefficientwise convergence. -/
@[fun_prop]
lemma continuous_subst {T : ℂ_[p]⟦X⟧} (hT : HasSubst T) :
    Continuous (subst T : ℂ_[p]⟦X⟧ → ℂ_[p]⟦X⟧) := by
  refine continuous_pi fun α ↦ ?_
  -- Only finitely many powers `T ^ n` have a nonzero `α`-th coefficient (apply finiteness to the
  -- series `mk 1` with all coefficients `1`), so the `α`-th coefficient of `subst T f` is a sum
  -- over a finite set that does not depend on `f`.
  have h_fin : (Function.support fun n : ℕ ↦ MvPowerSeries.coeff α (T ^ n)).Finite := by
    simpa [Function.HasFiniteSupport] using coeff_subst_finite hT (mk (R := ℤ) 1) α
  have h_sum (f : ℂ_[p]⟦X⟧) : MvPowerSeries.coeff α (subst T f) =
      ∑ n ∈ h_fin.toFinset, coeff n f • MvPowerSeries.coeff α (T ^ n) := by
    rw [coeff_subst hT, finsum_eq_sum_of_support_subset_of_finite _ (by simp) h_fin]
  exact .congr (by fun_prop [coeff]) fun f ↦ (h_sum f).symm

namespace IsSeriesGenerator

variable {B : Subring ℂ_[p]⟦X⟧} {T : ℂ_[p]⟦X⟧}

/-! ### Properties of `𝔬[[T]]` -/

/-- Let `B = 𝔬[[T]]`, with `𝔬` the valuation ring of `ℂ_[p]`. The generator `T` has a
compositional inverse `Z`, and `f ∈ B` exactly when `f(Z)` has integral coefficients. -/
lemma exists_subst_inverse (hB : IsSeriesGenerator B T) :
    ∃ Z : ℂ_[p]⟦X⟧,
      constantCoeff Z = 0 ∧
      subst Z T = X ∧
      subst T Z = X ∧
      ∀ {f : ℂ_[p]⟦X⟧}, f ∈ B ↔ subst Z f ∈ seriesToCp.range := by
  -- `Z` is the compositional inverse of `T`, so `f = g(T)` if and only if `f(Z) = g`.
  have h_unit : IsUnit (coeff 1 T) := by simp [hB.coeff_one]
  let Z : ℂ_[p]⟦X⟧ := T.substInvOfIsUnit h_unit
  have hZT : subst Z T = X := subst_substInvOfIsUnit_right T hB.constantCoeff_eq_zero h_unit
  have hTZ : subst T Z = X := subst_substInvOfIsUnit_left T hB.constantCoeff_eq_zero h_unit
  have hT : HasSubst T := .of_constantCoeff_zero' hB.constantCoeff_eq_zero
  have hZ : HasSubst Z := .of_constantCoeff_zero' (by simp [Z])
  refine ⟨Z, by simp [Z], hZT, hTZ, fun {f} ↦
    (hB.mem_iff f).trans (exists_congr fun g ↦ ⟨fun hg ↦ ?_, fun hg ↦ ?_⟩)⟩
  · rw [hg, subst_comp_subst_apply hT hZ, hZT, X_subst]
  · rw [hg, subst_comp_subst_apply hZ hT, hTZ, X_subst]

lemma generator_mem (hB : IsSeriesGenerator B T) : T ∈ B := by
  exact (hB.mem_iff T).2
    ⟨X, by simp [seriesToCp_eq_map, subst_X (.of_constantCoeff_zero' hB.constantCoeff_eq_zero)]⟩

/-- Let `B = 𝔬[[T]]` be the ring of series in `T` over the valuation ring `𝔬` of `ℂ_[p]`. If
`c` has norm at most one and `f ∈ B`, then `c • f ∈ B`. -/
lemma smul_mem (hB : IsSeriesGenerator B T) {c : ℂ_[p]} {f : ℂ_[p]⟦X⟧} (hc : ‖c‖ ≤ 1)
    (hf : f ∈ B) : c • f ∈ B := by
  -- After substituting the inverse `Z` of `T`, membership is a norm bound on each coefficient.
  obtain ⟨Z, hZ₀, -, -, h_mem⟩ := hB.exists_subst_inverse
  rw [h_mem, mem_range_seriesToCp] at hf ⊢
  intro n
  rw [subst_smul (.of_constantCoeff_zero' hZ₀), coeff_smul, norm_smul]
  exact (mul_le_of_le_one_left (norm_nonneg _) hc).trans (hf n)

lemma norm_constantCoeff_le_one (hB : IsSeriesGenerator B T) {f : ℂ_[p]⟦X⟧} (hf : f ∈ B) :
    ‖f.constantCoeff‖ ≤ 1 := by
  obtain ⟨g, rfl⟩ := (hB.mem_iff f).1 hf
  simpa [hB.constantCoeff_eq_zero] using mem_range_seriesToCp.1 ⟨g, rfl⟩ 0

lemma norm_coeff_one_le_one (hB : IsSeriesGenerator B T) {f : ℂ_[p]⟦X⟧} (hf : f ∈ B) :
    ‖f.coeff 1‖ ≤ 1 := by
  -- The linear coefficient of `f = g(T)` is that of the integral series `g`, as `T = X + ⋯`.
  obtain ⟨g, rfl⟩ := (hB.mem_iff f).1 hf
  simpa [coeff_one_subst hB.constantCoeff_eq_zero, hB.coeff_one] using
    mem_range_seriesToCp.1 ⟨g, rfl⟩ 1

/-- The constant term and the linear coefficient of an element of `B = 𝔬[[T]]` have norm at most
one. -/
lemma norm_constantCoeff_le_one_and_norm_coeff_one_le_one (hB : IsSeriesGenerator B T)
    {f : ℂ_[p]⟦X⟧} (hf : f ∈ B) :
    ‖f.constantCoeff‖ ≤ 1 ∧ ‖f.coeff 1‖ ≤ 1 :=
  ⟨hB.norm_constantCoeff_le_one hf, hB.norm_coeff_one_le_one hf⟩

/-- Let `B = 𝔬[[T]]` be the ring of series in `T` over the valuation ring `𝔬` of `ℂ_[p]`. Any
`f = X + ⋯` in `B` generates the same ring: `𝔬[[f]] = B`. -/
lemma of_mem (hB : IsSeriesGenerator B T) {f : ℂ_[p]⟦X⟧} (hf : f ∈ B) (hf₀ : f.constantCoeff = 0)
    (hf₁ : f.coeff 1 = 1) : IsSeriesGenerator B f := by
  -- Write `f = F(T)` with `F` integral. As `T = X + ⋯`, also `F = X + ⋯`, so `F` has a
  -- compositional inverse over `𝔬` and substituting `F` is onto: every `G(T)` is some `G'(f)`.
  have hT₀ : constantCoeff T = 0 := hB.constantCoeff_eq_zero
  obtain ⟨F, rfl⟩ := (hB.mem_iff f).1 hf
  have hF₀ : constantCoeff F = 0 := by simpa [hT₀, constantCoeff_seriesToCp] using hf₀
  have hF₁ : coeff 1 F = 1 := by
    simpa [coeff_one_subst hT₀, hB.coeff_one, coeff_seriesToCp] using hf₁
  have h_surj : (subst F : (valRingCp p)⟦X⟧ → (valRingCp p)⟦X⟧).Surjective := fun G ↦
    ⟨subst (F.substInvOfIsUnit (by simp [hF₁])) G, by
      rw [subst_comp_subst_apply (.of_constantCoeff_zero' (by simp)) (.of_constantCoeff_zero' hF₀),
        subst_substInvOfIsUnit_left F hF₀, X_subst]⟩
  refine ⟨hf₀, hf₁, fun S ↦ ?_⟩
  rw [hB.mem_iff, h_surj.exists]
  simp only [subst_seriesToCp_subst hT₀ hF₀]

/-- An element of `B = 𝔬[[T]]`, the ring of series in `T` over the valuation ring `𝔬` of `ℂ_[p]`,
whose constant term has norm `1` is invertible in `B`. -/
lemma exists_mul_eq_one (hB : IsSeriesGenerator B T) {f : ℂ_[p]⟦X⟧} (hf : f ∈ B)
    (h_norm : ‖f.constantCoeff‖ = 1) : ∃ v ∈ B, f * v = 1 := by
  -- Write `f = g(T)`; the constant term of `g` is a unit of the valuation ring, so `g` is a unit.
  have hT₀ : constantCoeff T = 0 := hB.constantCoeff_eq_zero
  obtain ⟨g, rfl⟩ := (hB.mem_iff f).1 hf
  have hg₀ : IsUnit (constantCoeff g) := by simpa [hT₀, constantCoeff_seriesToCp] using h_norm
  obtain ⟨v, hv : g * v = 1⟩ := (isUnit_iff_constantCoeff.2 hg₀).exists_right_inv
  refine ⟨subst T (seriesToCp v), (hB.mem_iff _).2 ⟨v, rfl⟩, ?_⟩
  simp [← coe_substAlgHom (.of_constantCoeff_zero' hT₀), ← map_mul, hv]

/-- Let `B = 𝔬[[T]]` be the ring of series in `T` over the valuation ring `𝔬` of `ℂ_[p]`. If
`T(a X)` lies in `B`, then `B` is stable under `f ↦ f(a X)`. -/
lemma rescale_mem (hB : IsSeriesGenerator B T) {a : ℂ_[p]} {f : ℂ_[p]⟦X⟧} (hT : rescale a T ∈ B)
    (hf : f ∈ B) : rescale a f ∈ B := by
  -- If `T(a X) = u(T)` and `f = g(T)`, then `f(a X) = (g ∘ u)(T)`.
  have hT₀ : constantCoeff T = 0 := hB.constantCoeff_eq_zero
  obtain ⟨u, hu⟩ := (hB.mem_iff _).1 hT
  obtain ⟨g, rfl⟩ := (hB.mem_iff f).1 hf
  have hu₀ : constantCoeff u = 0 := by
    simpa [hT₀, constantCoeff_seriesToCp] using (congrArg constantCoeff hu).symm
  refine (hB.mem_iff _).2 ⟨subst u g, ?_⟩
  rw [rescale_subst hT₀, hu, subst_seriesToCp_subst hT₀ hu₀]

end IsSeriesGenerator

namespace CMLattice

variable {d : ℕ} (C : CMLattice d) [PadicPlace p]

/-! ### The ring `𝔬[[y]]` of a CM curve -/

/-- The subring `𝔬[[y]]` of `ℂ_[p]⟦X⟧` of integral power series in the Taylor series of the
coordinate `y = C.translatedY`, with the `p`-adic place `ιₚ` applied to its coefficients. -/
noncomputable def integralSeriesRing : Subring ℂ_[p]⟦X⟧ :=
  ((substAlgHom (a := taylorVia ιₚ C.translatedY)
    (.of_constantCoeff_zero' (by simp))).toRingHom.comp (seriesToCp (p := p))).range

/-- The elements of `𝔬[[y]]` are the series `g(y)` with `g` integral. -/
lemma mem_integralSeriesRing {f : ℂ_[p]⟦X⟧} : f ∈ C.integralSeriesRing ↔
    ∃ g : (valRingCp p)⟦X⟧, f = subst (taylorVia ιₚ C.translatedY) (seriesToCp g) := by
  simp [integralSeriesRing, eq_comm, coe_substAlgHom]

/-- The Taylor series of `y = C.translatedY` in `ℂ_[p]⟦X⟧` begins with `X` and generates
`𝔬[[y]]`. -/
lemma isSeriesGenerator_translatedY :
    IsSeriesGenerator C.integralSeriesRing (taylorVia ιₚ C.translatedY) where
  constantCoeff_eq_zero := by simp
  coeff_one := by simp
  mem_iff _ := C.mem_integralSeriesRing

variable [PrimeSevenModEight d]

omit [PadicPlace p] in
/-- For `a` in the valuation ring `𝔬` of `ℂ_[p]`, the cubic `Y³ + (1 - a X) Y - X²` over `𝔬[[X]]`
has a root without constant term, by Hensel's lemma. -/
lemma _root_.New.exists_isRoot_cubic_constantCoeff_eq_zero (a : valRingCp p) :
    ∃ y : (valRingCp p)⟦X⟧,
      (⟨1, 0, 1 - .C a * X, -X * X⟩ : Cubic (valRingCp p)⟦X⟧).toPoly.IsRoot y ∧
      constantCoeff y = 0 := by
  set F : Cubic (valRingCp p)⟦X⟧ := ⟨1, 0, 1 - .C a * X, -X * X⟩ with hF
  have h_approx : F.toPoly.eval 0 ∈ Ideal.span {X} := by
    simp [hF, Cubic.toPoly, Ideal.mem_span_singleton]
  have h_simple : IsUnit (Ideal.Quotient.mk (Ideal.span {X}) (F.toPoly.derivative.eval 0)) := by
    simp [hF, Cubic.toPoly]
  obtain ⟨y, hy_root, hy_mem : y - 0 ∈ Ideal.span {X}⟩ :=
    HenselianRing.is_henselian F.toPoly Cubic.monic_of_a_eq_one' 0 h_approx h_simple
  exact ⟨y, hy_root, by simpa [Ideal.mem_span_singleton, X_dvd_iff] using hy_mem⟩

/-- For a `CMLattice` `C`, consisting of a lattice `Λ`, a point `t` of order two modulo `Λ` and `a₁`
with `a₁² = 12 ℘(t)`, let `x(z) = ℘(z + t) − ℘(t)` be `C.translatedX` and `y = C.translatedY` the
companion coordinate, with Taylor series `y = X + ⋯` and `y' = 1 + 3 x² - a₁ y`, so that `(x, y)`
lies on the CM curve `y² + a₁ x y = x³ + x`. Then the Taylor series of `x` at `z = 0`, with the
`p`-adic place `ιₚ` applied to its coefficients, lies in `C.integralSeriesRing`. That is, it is a
power series in the likewise expanded `y` with coefficients in the ring of integers `𝔬` of
`ℂ_[p]`. -/
lemma taylorVia_translatedX_mem_integralSeriesRing :
    taylorVia ιₚ C.translatedX ∈ C.integralSeriesRing := by
  -- The equation of the curve says that `x` is a root of `Y³ + (1 - a₁ y) Y - y²`. The cubic
  -- `Y³ + (1 - a₁ X) Y - X²` has a root `r` in `X 𝔬[[X]]`, and `r(y)` is the same root: over a
  -- local ring two roots that are congruent and simple modulo the maximal ideal agree.
  let a₁ : valRingCp p := ⟨ιₚ C.a₁, C.norm_a₁_le_one⟩
  let F : Cubic (valRingCp p)⟦X⟧ := ⟨1, 0, 1 - .C a₁ * X, -X * X⟩
  obtain ⟨r, hr_root : F.toPoly.IsRoot r, hr₀⟩ := exists_isRoot_cubic_constantCoeff_eq_zero a₁
  set y : ℂ_[p]⟦X⟧ := taylorVia ιₚ C.translatedY with hy
  set x : ℂ_[p]⟦X⟧ := taylorVia ιₚ C.translatedX with hx
  have hy₀ : constantCoeff y = 0 := by simp [hy]
  have hy_subst : HasSubst y := .of_constantCoeff_zero' hy₀
  let Φ : (valRingCp p)⟦X⟧ →+* ℂ_[p]⟦X⟧ := (substAlgHom hy_subst).toRingHom.comp seriesToCp
  have hΦ (g : (valRingCp p)⟦X⟧) : Φ g = subst y (seriesToCp g) := by simp [Φ, coe_substAlgHom]
  have hΦr₀ : constantCoeff (Φ r) = 0 := by simp [hΦ, hy₀, constantCoeff_seriesToCp, hr₀]
  have h_map : F.toPoly.map Φ =
      Polynomial.X ^ 3 + .C (1 - .C (ιₚ C.a₁) * y) * Polynomial.X - .C (y * y) := by
    have hΦ_C : Φ (.C a₁) = .C (ιₚ C.a₁) := by
      rw [hΦ, seriesToCp_eq_map, map_C, subst_C]
      rfl
    have hΦ_X : Φ X = y := by rw [hΦ, seriesToCp_eq_map, map_X, subst_X hy_subst]
    simp [F, Cubic.toPoly, hΦ_X, hΦ_C, sub_eq_add_neg]
  have hx_root : (F.toPoly.map Φ).eval x = 0 := by
    have h_curve : x ^ 3 + (1 - .C (ιₚ C.a₁) * y) * x - y * y = 0 := by
      linear_combination -C.taylorVia_curve_eq ιₚ
    simpa [h_map] using h_curve
  have h_congr : ¬IsUnit (Φ r - x) := by simp [isUnit_iff_constantCoeff, hΦr₀, hx, translatedX]
  have h_simple : IsUnit ((F.toPoly.map Φ).derivative.eval (Φ r)) := by
    simp [h_map, isUnit_iff_constantCoeff, hΦr₀, hy₀]
  have h_eq : Φ r = x :=
    IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub hr_root.map hx_root h_congr h_simple
  exact C.mem_integralSeriesRing.2 ⟨r, by rw [← hΦ, h_eq]⟩

/-- For a `CMLattice` `C` (a lattice `Λ` with a point `t` of order two modulo `Λ`), let
`y = C.translatedY` be the `y`-coordinate of the CM curve `y² + a₁ x y = x³ + x`, where
`x(z) = ℘(z + t) − ℘(t)`. Expand `y` at `z = 0` and apply the `p`-adic place `ιₚ` to its
coefficients to get a series in `ℂ_[p]⟦X⟧`. The ring `C.integralSeriesRing` is the ring `𝔬[[y]]` of
power series in this `y` with coefficients in the ring of integers `𝔬` of `ℂ_[p]`. This ring is
stable under the derivative `d/dz`. -/
lemma derivative_mem_integralSeriesRing {f : ℂ_[p]⟦X⟧} (hf : f ∈ C.integralSeriesRing) :
    d⁄dX f ∈ C.integralSeriesRing := by
  obtain ⟨g, rfl⟩ := C.mem_integralSeriesRing.1 hf
  have hy := C.isSeriesGenerator_translatedY (p := p)
  -- Chain rule: `(g ∘ y)' = (g' ∘ y) y'` with `g'` integral and `y' = 1 + 3 x² - a₁ y`.
  rw [derivative_subst (.of_constantCoeff_zero' hy.constantCoeff_eq_zero), derivative_seriesToCp,
    derivative_taylorVia_translatedY, ← smul_eq_C_mul]
  refine mul_mem (C.mem_integralSeriesRing.2 ⟨d⁄dX g, rfl⟩) (sub_mem ?_ ?_)
  · exact add_mem (one_mem _)
      (mul_mem (ofNat_mem _ 3) (pow_mem C.taylorVia_translatedX_mem_integralSeriesRing 2))
  · exact hy.smul_mem C.norm_a₁_le_one hy.generator_mem

end CMLattice

end New

end IntegralParameter

/-! ## Congruence parts and integral solutions of a functional equation -/

section SeriesParts

open PowerSeries Finset

namespace New

variable {p : ℕ} [Fact p.Prime] {m r n : ℕ} {f T : ℂ_[p]⟦X⟧}

lemma seriesToCp_injective : Function.Injective (seriesToCp : (valRingCp p)⟦X⟧ → ℂ_[p]⟦X⟧) :=
  map_injective (valRingCp p).subtype Subtype.coe_injective

/-- The part of `f` in degrees `≡ r` mod `m`. -/
noncomputable def congruencePart (m r : ℕ) (f : ℂ_[p]⟦X⟧) : ℂ_[p]⟦X⟧ :=
  mk fun n ↦ if n ≡ r [MOD m] then f.coeff n else 0

lemma coeff_congruencePart (f : ℂ_[p]⟦X⟧) :
    coeff n (congruencePart m r f) = if n ≡ r [MOD m] then coeff n f else 0 := coeff_mk n _

lemma congruencePart_congruencePart (f : ℂ_[p]⟦X⟧) :
    congruencePart m r (congruencePart m r f) = congruencePart m r f := by
  ext n
  simp +contextual [coeff_congruencePart]

/-- The substitution `f ↦ f(a X)` commutes with taking the part in degrees `≡ r` mod `m`. -/
lemma congruencePart_rescale (a : ℂ_[p]) (f : ℂ_[p]⟦X⟧) :
    congruencePart m r (rescale a f) = rescale a (congruencePart m r f) := by
  ext n
  simp [coeff_congruencePart, coeff_rescale]

/-- If `ζ ^ m = 1`, then replacing `X` by `ζ X` multiplies the part of a series in degrees `≡ r`
mod `m` by `ζ ^ r`. -/
lemma rescale_congruencePart_of_pow_eq_one {ζ : ℂ_[p]} (hζ : ζ ^ m = 1) (r : ℕ) (f : ℂ_[p]⟦X⟧) :
    rescale ζ (congruencePart m r f) = ζ ^ r • congruencePart m r f := by
  ext n
  simp +contextual [coeff_congruencePart, coeff_rescale, pow_eq_pow_of_modEq (b := r) _ hζ]

/-- For `m ≠ 0` and a primitive `m`-th root of unity `ζ`, the part of `f` in degrees `≡ r` mod `m`
is the mean over `i < m` of the series `η ^ (-r) f(η z)` with `η = ζ ^ i`. -/
lemma congruencePart_eq_sum {m : ℕ} [NeZero m] {ζ : ℂ_[p]} (hζ : IsPrimitiveRoot ζ m) (r : ℕ)
    (f : ℂ_[p]⟦X⟧) :
    congruencePart m r f = (m : ℂ_[p])⁻¹ • ∑ i ∈ range m, (ζ ^ i)⁻¹ ^ r • rescale (ζ ^ i) f := by
  -- Compare the coefficients of `X ^ n`: the factor of `coeff n f` on the right is the average of
  -- the powers of the `m`-th root of unity `ξ = ζ⁻¹ ^ r * ζ ^ n`, which is `1` iff `n ≡ r [MOD m]`.
  ext n
  have hm : m ≠ 0 := NeZero.ne m
  set ξ : ℂ_[p] := ζ⁻¹ ^ r * ζ ^ n with hξ
  have h_one : ξ = 1 ↔ n ≡ r [MOD m] := by
    rw [hξ, inv_pow, inv_mul_eq_one₀ (pow_ne_zero r (hζ.ne_zero hm)), eq_comm,
      (hζ.isOfFinOrder hm).pow_eq_pow_iff_modEq, ← hζ.eq_orderOf]
  have h_root : ξ ^ m = 1 := by simp [hξ, mul_pow, pow_right_comm _ _ m, hζ.pow_eq_one]
  have h_avg : (m : ℂ_[p])⁻¹ * ∑ i ∈ range m, ξ ^ i = if n ≡ r [MOD m] then 1 else 0 := by
    split_ifs with h_modEq
    · simp [h_one.2 h_modEq, hm]
    · simp [geom_sum_eq (mt h_one.1 h_modEq), h_root]
  calc coeff n (congruencePart m r f) = ((m : ℂ_[p])⁻¹ * ∑ i ∈ range m, ξ ^ i) * coeff n f := by
        simp [h_avg, coeff_congruencePart]
    _ = coeff n ((m : ℂ_[p])⁻¹ • ∑ i ∈ range m, (ζ ^ i)⁻¹ ^ r • rescale (ζ ^ i) f) := by
        simp [hξ, mul_assoc, sum_mul, ← inv_pow, pow_right_comm, mul_pow]

/-- Let `m ≠ 0`. If `T` has constant term `0` and only degrees `≡ 1` mod `m`, then substituting `T`
commutes with taking the part of a series in the degrees `≡ r` mod `m`. -/
lemma congruencePart_subst {m : ℕ} {T : ℂ_[p]⟦X⟧} [NeZero m] (hT₀ : constantCoeff T = 0)
    (hT : congruencePart m 1 T = T) (r : ℕ) (g : ℂ_[p]⟦X⟧) :
    congruencePart m r (subst T g) = subst T (congruencePart m r g) := by
  obtain ⟨ζ : ℂ_[p], hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot ℂ_[p] m
  have hT_subst : HasSubst T := .of_constantCoeff_zero' hT₀
  have h_rescale (i : ℕ) : rescale (ζ ^ i) T = ζ ^ i • T := by
    have h_root : (ζ ^ i) ^ m = 1 := by rw [pow_right_comm, hζ.pow_eq_one, one_pow]
    simpa only [hT, pow_one] using rescale_congruencePart_of_pow_eq_one h_root 1 T
  have h_comm (i : ℕ) : rescale (ζ ^ i) (subst T g) = subst T (rescale (ζ ^ i) g) := by
    rw [rescale_subst hT₀, h_rescale, subst_rescale_eq_subst_smul T hT_subst]
  calc congruencePart m r (subst T g)
      = (m : ℂ_[p])⁻¹ • ∑ i ∈ range m, (ζ ^ i)⁻¹ ^ r • subst T (rescale (ζ ^ i) g) := by
        simp only [congruencePart_eq_sum hζ, h_comm]
    _ = subst T (congruencePart m r g) := by
        simp only [congruencePart_eq_sum hζ, ← coe_substAlgHom hT_subst, map_smul, map_sum]

/-- If `T` generates `B`, that is `B = 𝔬[[T]]` with `T = X + ⋯`, then `f ↦ f(T)` is injective. -/
lemma IsSeriesGenerator.subst_injective {T : ℂ_[p]⟦X⟧} {B : Subring ℂ_[p]⟦X⟧}
    (hT : IsSeriesGenerator B T) : (subst T : ℂ_[p]⟦X⟧ → ℂ_[p]⟦X⟧).Injective := by
  obtain ⟨Z, hZ₀, hZ : subst Z T = X, -, -⟩ := hT.exists_subst_inverse
  refine Function.LeftInverse.injective (g := subst Z) fun f ↦ ?_
  rw [subst_comp_subst_apply (.of_constantCoeff_zero' hT.constantCoeff_eq_zero)
    (.of_constantCoeff_zero' hZ₀), hZ, X_subst]

variable (p) in
/-- The ring of the power series whose coefficients in degrees below `n` are integral. -/
def integralBelow (n : ℕ) : Subring ℂ_[p]⟦X⟧ where
  carrier := {f : ℂ_[p]⟦X⟧ | ∀ k < n, coeff k f ∈ valRingCp p}
  zero_mem' k _ := by simp
  one_mem' k _ := by simp [coeff_one, apply_ite (· ∈ valRingCp p)]
  add_mem' hf hg k hk := by simpa using add_mem (hf k hk) (hg k hk)
  neg_mem' hf k hk := by simpa using hf k hk
  mul_mem' hf hg k hk := by
    rw [coeff_mul]
    refine sum_mem fun ⟨i, j⟩ hij ↦ ?_
    rw [HasAntidiagonal.mem_antidiagonal] at hij
    exact mul_mem (hf i (by omega)) (hg j (by omega))

lemma mem_integralBelow : f ∈ integralBelow p n ↔ ∀ k < n, ‖coeff k f‖ ≤ 1 := Iff.rfl

lemma X_mul_mem_integralBelow : X * f ∈ integralBelow p (n + 1) ↔ f ∈ integralBelow p n := by
  rw [mem_integralBelow, Nat.forall_lt_succ_left]
  simp [mem_integralBelow, coeff_succ_X_mul]

/-- For `T : ℂ_[p]⟦X⟧` and `n : ℕ`: if `T(0) = 0`, the coefficients of `T` in degrees below `n` have
norm at most one and `g` is a series over the valuation ring of `ℂ_[p]`, then the coefficients of
`g(T)` in degrees below `n` have norm at most one. -/
lemma subst_seriesToCp_mem_integralBelow (hT₀ : constantCoeff T = 0) (hT : T ∈ integralBelow p n)
    (g : (valRingCp p)⟦X⟧) : subst T (seriesToCp g) ∈ integralBelow p n := by
  intro k hk
  rw [coeff_subst' (.of_constantCoeff_zero' hT₀)]
  exact finsum_induction (· ∈ valRingCp p) (zero_mem _) (fun _ _ ↦ add_mem)
    fun i ↦ mul_mem (SetLike.coe_mem (coeff i g)) (pow_mem hT i k hk)

lemma integralBelow_anti {k n : ℕ} (hkn : k ≤ n) : integralBelow p n ≤ integralBelow p k :=
  fun _ hf j hj ↦ hf j (hj.trans_le hkn)

lemma norm_pow_sub_one_eq_one {π : ℂ_[p]} (hπ : ‖π‖ < 1) {n : ℕ} (hn : n ≠ 0) :
    ‖π ^ n - 1‖ = 1 := by
  have h_lt : ‖π ^ n‖ < ‖(-1 : ℂ_[p])‖ := by simpa using pow_lt_one₀ (norm_nonneg π) hπ hn
  rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h_lt.ne,
    max_eq_right h_lt.le, norm_neg, norm_one]

/-- Let `0 < |π| < 1` and let `G = z + ⋯` be a series over the valuation ring of `ℂ_[p]`, which
`seriesToCp` maps to `ℂ_[p]⟦X⟧`. A series `Y = z + ⋯` with `Y(π z) = π G(Y)` has coefficients in
the valuation ring, that is, lies in the range of `seriesToCp`. -/
lemma mem_range_seriesToCp_of_rescale_eq {π : ℂ_[p]} (hπ₀ : π ≠ 0) (hπ : ‖π‖ < 1) {Y : ℂ_[p]⟦X⟧}
    (hY₀ : constantCoeff Y = 0) (hY₁ : coeff 1 Y = 1) {G : (valRingCp p)⟦X⟧} (hG : X ^ 2 ∣ G - X)
    (h_rescale : rescale π Y = π • subst Y (seriesToCp G)) : Y ∈ seriesToCp.range := by
  -- Induction on the degree: with `G = X + X ^ 2 H`, the equation in degree `n` expresses
  -- `(π ^ (n - 1) - 1) coeff n Y` by coefficients of lower degree, and `π ^ (n - 1) - 1` is a
  -- unit for `n ≥ 2`.
  obtain ⟨H : (valRingCp p)⟦X⟧, hH : G - X = X ^ 2 * H⟩ := hG
  obtain ⟨Y₁ : ℂ_[p]⟦X⟧, hY : Y = X * Y₁⟩ := X_dvd_iff.2 hY₀
  have hY_subst : HasSubst Y := .of_constantCoeff_zero' hY₀
  set R : ℂ_[p]⟦X⟧ := X * (X * (Y₁ ^ 2 * subst Y (seriesToCp H))) with hR
  have h_higher : subst Y (seriesToCp G) = Y + R := by
    have h_map : seriesToCp G = X + X ^ 2 * seriesToCp H := by
      simp [seriesToCp_eq_map, eq_add_of_sub_eq' hH]
    rw [h_map, subst_add hY_subst, subst_mul hY_subst, subst_pow hY_subst, subst_X hY_subst, hR]
    linear_combination (Y + X * Y₁) * subst Y (seriesToCp H) * hY
  suffices h_below : ∀ n : ℕ, Y ∈ integralBelow p (n + 2) from
    mem_range_seriesToCp.2 fun n ↦ mem_integralBelow.1 (h_below n) n (by omega)
  intro n
  induction n with
  | zero =>
    rw [mem_integralBelow, Nat.forall_lt_succ_left, Nat.forall_lt_succ_left]
    simp [hY₀, hY₁]
  | succ n ih =>
    -- The higher terms involve in degree `n + 2` only coefficients of `Y` of lower degree.
    have h_rest : R ∈ integralBelow p (n + 3) := by
      have hY₁_below : Y₁ ∈ integralBelow p (n + 1) := by rwa [← X_mul_mem_integralBelow, ← hY]
      rw [hR, X_mul_mem_integralBelow, X_mul_mem_integralBelow]
      exact mul_mem (pow_mem hY₁_below 2)
        (integralBelow_anti (by omega) (subst_seriesToCp_mem_integralBelow hY₀ ih H))
    have h_coeff : (π ^ (n + 1) - 1) * coeff (n + 2) Y = coeff (n + 2) R := by
      have h_eq : π ^ (n + 2) * coeff (n + 2) Y = π * (coeff (n + 2) Y + coeff (n + 2) R) := by
        rw [← map_add, ← h_higher, ← coeff_rescale, h_rescale, coeff_smul, smul_eq_mul]
      exact mul_left_cancel₀ hπ₀ (by linear_combination h_eq)
    have h_norm : ‖coeff (n + 2) Y‖ = ‖coeff (n + 2) R‖ := by
      rw [← h_coeff, norm_mul, norm_pow_sub_one_eq_one hπ n.succ_ne_zero, one_mul]
    rw [mem_integralBelow, Nat.forall_lt_succ_right, h_norm]
    exact ⟨mem_integralBelow.1 ih, mem_integralBelow.1 h_rest (n + 2) (by omega)⟩

/-- Let `m ≠ 0` and let `π ≠ 0` lie in the valuation ring `𝔬` of `ℂ_[p]`. Let
`g = π z + b₁ z ^ (1 + m) + ∑_{i ≥ 2} bᵢ z ^ (1 + i m)` have coefficients in `𝔬`, with `b₁` a unit,
and let `ϖ ^ m = -π / b₁`. Then `g(ϖ z) = ϖ π (z - z ^ (1 + m) + π E)` for an integral series `E`
of order at least two. -/
lemma exists_rescale_eq_smul_X_sub_X_pow {m : ℕ} (hm : m ≠ 0) {π : valRingCp p} (hπ₀ : π ≠ 0)
    {g : (valRingCp p)⟦X⟧} (h_degree : ∀ n : ℕ, coeff n g ≠ 0 → ∃ i : ℕ, n = 1 + i * m)
    (hg₁ : coeff 1 g = π) {b₁ : (valRingCp p)ˣ} (hb₁ : coeff (1 + m) g = b₁) {ϖ : ℂ_[p]}
    (hϖ : ϖ ^ m = (π * -b₁⁻¹ : valRingCp p)) :
    ∃ E : (valRingCp p)⟦X⟧,
      X ^ 2 ∣ E ∧
      rescale ϖ (seriesToCp g) = (ϖ * π) • seriesToCp (X - X ^ (1 + m) + C π * E) := by
  -- The coefficient of `E` in degree `1 + i m`, `i ≥ 2`, is `bᵢ (-b₁) ^ (-i) π ^ (i - 2)`.
  let E : (valRingCp p)⟦X⟧ := mk fun n : ℕ ↦ if 1 + m < n then
    coeff n g * (-b₁⁻¹) ^ ((n - 1) / m) * π ^ ((n - 1) / m - 2) else 0
  refine ⟨E, X_pow_dvd_iff.2 fun n hn ↦ by rw [coeff_mk, ite_eq_right (by omega)], ext fun n ↦ ?_⟩
  -- In degree `n` the identity is an equation in `ℂ_[p]` between elements of `𝔬`.
  suffices h_coeff : ϖ ^ n * coeff n g = ϖ * π * ((if n = 1 then 1 else 0) -
      (if n = 1 + m then 1 else 0) + (π * coeff n E : valRingCp p)) by
    simp only [coeff_rescale, coeff_smul, coeff_seriesToCp, map_add, map_sub, coeff_X, coeff_X_pow,
      coeff_C_mul, smul_eq_mul]
    simpa [apply_ite (Subtype.val : valRingCp p → ℂ_[p])] using h_coeff
  rw [coeff_mk]
  by_cases hn : coeff n g = 0
  · have hn₁ : n ≠ 1 := fun h ↦ hπ₀ (by rw [← hg₁, ← h, hn])
    have hn₂ : n ≠ 1 + m := fun h ↦ b₁.ne_zero (by rw [← hb₁, ← h, hn])
    simp [hn, hn₁, hn₂]
  obtain ⟨i, rfl⟩ := h_degree n hn
  rw [pow_add, pow_mul', hϖ, Nat.add_sub_cancel_left, Nat.mul_div_cancel i hm.bot_lt]
  rcases i with _ | _ | i
  · -- Degree one.
    simp [hg₁, hm]
  · -- Degree `1 + m`.
    have h_inv : ((b₁⁻¹ : (valRingCp p)ˣ) : ℂ_[p]) * b₁ = 1 := mod_cast b₁.inv_mul
    simp [hb₁, hm, mul_assoc, h_inv]
  · -- Degree `1 + (i + 2) m`, the only degrees in which `E` can be nonzero.
    have h_lt : 1 + m < 1 + (i + 1 + 1) * m := by nlinarith [hm.bot_lt]
    simp [h_lt, hm]
    ring

/-- Let `π ≠ 0` be an element of a domain. If `Y = z + ⋯` and `Y(π z) = π W`, then `W ≡ z`
modulo `π`. -/
lemma C_dvd_sub_X_of_rescale_eq {R : Type*} [CommRing R] [IsDomain R] {π : R} (hπ₀ : π ≠ 0)
    {Y W : R⟦X⟧} (hY₀ : constantCoeff Y = 0) (hY₁ : coeff 1 Y = 1)
    (h_rescale : rescale π Y = π • W) : C π ∣ W - X := by
  refine ⟨mk fun n : ℕ ↦ if 2 ≤ n then π ^ (n - 2) * coeff n Y else 0, ext fun n ↦ ?_⟩
  have h_coeff : π ^ n * coeff n Y = π * coeff n W := by
    rw [← coeff_rescale, h_rescale, coeff_smul, smul_eq_mul]
  apply mul_left_cancel₀ hπ₀
  rw [map_sub, mul_sub, ← h_coeff, coeff_C_mul, coeff_mk, coeff_X]
  rcases n with _ | _ | n <;> simp [hY₀, hY₁, pow_succ', mul_assoc]

/-- Let `π ≠ 0` be an element of a domain. If `S = z + ⋯` and
`S(π z) = π (S - S ^ q + π E(S))`, then `S - S ^ q ≡ z` modulo `π`. -/
lemma C_dvd_sub_pow_sub_X_of_rescale_eq {R : Type*} [CommRing R] [IsDomain R] {π : R}
    (hπ₀ : π ≠ 0) {q : ℕ} {E S : R⟦X⟧} (hS₀ : constantCoeff S = 0) (hS₁ : coeff 1 S = 1)
    (h_rescale : rescale π S = π • subst S (X - X ^ q + C π * E)) : C π ∣ S - S ^ q - X := by
  have hS : HasSubst S := .of_constantCoeff_zero' hS₀
  have h_dvd : C π ∣ S - S ^ q - X + C π * subst S E := by
    simpa only [subst_add hS, subst_sub hS, subst_pow hS, subst_mul hS, subst_X hS, subst_C,
      ← C.eq_def, add_sub_right_comm] using C_dvd_sub_X_of_rescale_eq hπ₀ hS₀ hS₁ h_rescale
  exact (dvd_add_left (dvd_mul_right (C π) (subst S E))).1 h_dvd

/-- Let `0 < |π| < 1`, `q > 1` and let `E` be integral of order at least two. A series `Y = z + ⋯`
with `Y(π z) / π = Y - Y ^ q + π E(Y)` is integral. -/
lemma mem_range_seriesToCp_of_rescale_eq_X_sub_X_pow {π : valRingCp p} (hπ₀ : π ≠ 0)
    (hπ : ‖(π : ℂ_[p])‖ < 1) {q : ℕ} (hq : 1 < q) {E : (valRingCp p)⟦X⟧} (hE : X ^ 2 ∣ E)
    {Y : ℂ_[p]⟦X⟧} (hY₀ : constantCoeff Y = 0) (hY₁ : coeff 1 Y = 1)
    (h_rescale : rescale (π : ℂ_[p]) Y = (π : ℂ_[p]) • subst Y (seriesToCp (X - X ^ q + C π * E))) :
    Y ∈ seriesToCp.range := by
  have h_order : X ^ 2 ∣ X - X ^ q + C π * E - X := by
    rw [show X - X ^ q + C π * E - X = C π * E - X ^ q by ring]
    exact (hE.mul_left _).sub (pow_dvd_pow X hq)
  exact mem_range_seriesToCp_of_rescale_eq (mod_cast hπ₀) hπ hY₀ hY₁ h_order h_rescale

/-- Let `0 < |π| < 1`, `q > 1` and let `E` be integral of order at least two. A series `Y = z + ⋯`
with `Y(π z) / π = Y - Y ^ q + π E(Y)` comes from an integral series `S`, and `S - S ^ q ≡ z`
modulo `π`. -/
lemma exists_seriesToCp_eq_of_rescale_eq {π : valRingCp p} (hπ₀ : π ≠ 0) (hπ : ‖(π : ℂ_[p])‖ < 1)
    {q : ℕ} (hq : 1 < q) {E : (valRingCp p)⟦X⟧} (hE : X ^ 2 ∣ E) {Y : ℂ_[p]⟦X⟧}
    (hY₀ : constantCoeff Y = 0) (hY₁ : coeff 1 Y = 1)
    (h_rescale : rescale (π : ℂ_[p]) Y = (π : ℂ_[p]) • subst Y (seriesToCp (X - X ^ q + C π * E))) :
    ∃ S : (valRingCp p)⟦X⟧, seriesToCp S = Y ∧ C π ∣ S - S ^ q - X := by
  obtain ⟨S, rfl⟩ : Y ∈ seriesToCp.range :=
    mem_range_seriesToCp_of_rescale_eq_X_sub_X_pow hπ₀ hπ hq hE hY₀ hY₁ h_rescale
  have hS₀ : constantCoeff S = 0 := by simpa [constantCoeff_seriesToCp] using hY₀
  have hS₁ : coeff 1 S = 1 := by simpa [coeff_seriesToCp] using hY₁
  -- The functional equation descends to `𝔬[[X]]`.
  have h_int : rescale π S = π • subst S (X - X ^ q + C π * E) := seriesToCp_injective <| by
    rwa [seriesToCp_smul, map_subst (.of_constantCoeff_zero' hS₀), seriesToCp_eq_map, ← rescale_map]
  exact ⟨S, rfl, C_dvd_sub_pow_sub_X_of_rescale_eq hπ₀ hS₀ hS₁ h_int⟩

/-- In characteristic `p`, if `s - s ^ q = x` with `q = p ^ e`, then
`s = ∑_{l < B} x ^ q ^ l + s ^ q ^ B` for every `B`. -/
lemma eq_sum_pow_of_sub_pow_eq {R : Type*} [CommRing R] [CharP R p] {x s : R} {e : ℕ}
    (hs : s - s ^ p ^ e = x) (B : ℕ) : s = ∑ l ∈ range B, x ^ p ^ (e * l) + s ^ p ^ (e * B) := by
  -- The sum telescopes.
  have h_term (l : ℕ) : x ^ p ^ (e * l) = s ^ p ^ (e * l) - s ^ p ^ (e * (l + 1)) := by
    simp [← hs, sub_pow_char_pow, ← pow_mul, ← pow_add, mul_add, add_comm]
  simp [h_term, sum_range_sub' fun l ↦ s ^ p ^ (e * l)]

open scoped Classical in
/-- In prime characteristic `p`, let `q = p ^ e` with `e ≠ 0`. If `S(0) = 0` and `S - S ^ q = z`,
then `S = ∑ z ^ q ^ j`: the coefficient of degree `n` is `1` if `n` is a power of `q`, else `0`. -/
lemma coeff_eq_of_sub_pow_eq_X {R : Type*} [CommRing R] [CharP R p] {S : R⟦X⟧} {e : ℕ}
    (he : e ≠ 0) (hS₀ : constantCoeff S = 0) (hS : S - S ^ p ^ e = X) (n : ℕ) :
    coeff n S = if ∃ j : ℕ, n = (p ^ e) ^ j then 1 else 0 := by
  have : CharP R⟦X⟧ p := charP_of_injective_ringHom C_injective p
  have hq : 1 < p ^ e := Nat.one_lt_pow he (Fact.out : p.Prime).one_lt
  have h_tail : coeff n (S ^ (p ^ e) ^ n) = 0 := coeff_of_lt_order n
    (lt_of_lt_of_le (mod_cast Nat.lt_pow_self hq) (le_order_pow_of_constantCoeff_eq_zero _ hS₀))
  have h_sum : coeff n S = ∑ l ∈ range n, if n = (p ^ e) ^ l then 1 else 0 := by
    conv_lhs => rw [eq_sum_pow_of_sub_pow_eq hS n]
    simp [pow_mul p e, coeff_X_pow, h_tail]
  rw [h_sum]
  split_ifs with hn
  · obtain ⟨j, rfl⟩ := hn
    simp [Nat.pow_right_inj hq, Nat.lt_pow_self hq]
  · exact sum_eq_zero fun l _ ↦ ite_eq_right fun hl ↦ hn ⟨l, hl⟩

open scoped Classical in
/-- If `π` is a non-unit that divides `p`, `q = p ^ e` with `e ≠ 0`, `S(0) = 0` and
`S - S ^ q ≡ z` modulo `π`, then `S ≡ ∑ z ^ q ^ j` modulo `π`. -/
lemma dvd_coeff_sub_of_C_dvd_sub_pow_sub_X {R : Type*} [CommRing R] {π : R} (hπ : ¬IsUnit π)
    (hπp : π ∣ p) {S : R⟦X⟧} {e : ℕ} (he : e ≠ 0) (hS₀ : constantCoeff S = 0)
    (hS : C π ∣ S - S ^ p ^ e - X) (n : ℕ) :
    π ∣ coeff n S - if ∃ j : ℕ, n = (p ^ e) ^ j then 1 else 0 := by
  -- Reduce modulo `π`: the quotient has characteristic `p`, where the equation determines `S`.
  let φ : R →+* R ⧸ Ideal.span {π} := Ideal.Quotient.mk (Ideal.span {π})
  have hφ {x : R} : φ x = 0 ↔ π ∣ x := Ideal.Quotient.eq_zero_iff_dvd π x
  have : Nontrivial (R ⧸ Ideal.span {π}) :=
    Ideal.Quotient.nontrivial_iff.2 (mt Ideal.span_singleton_eq_top.1 hπ)
  have : CharP (R ⧸ Ideal.span {π}) p :=
    (CharP.charP_iff_prime_eq_zero Fact.out).2 (by simpa using hφ.2 hπp)
  have h_map : S.map φ - S.map φ ^ p ^ e = X := by
    simpa [hφ.2 dvd_rfl, sub_eq_zero] using map_dvd (PowerSeries.map φ) hS
  have h_coeff : coeff n (S.map φ) = if ∃ j : ℕ, n = (p ^ e) ^ j then 1 else 0 :=
    coeff_eq_of_sub_pow_eq_X he (by simp [← coeff_zero_eq_constantCoeff_apply, hS₀]) h_map n
  rw [← hφ, map_sub, ← coeff_map, h_coeff, apply_ite φ, map_one, map_zero, sub_self]

end New

end SeriesParts
