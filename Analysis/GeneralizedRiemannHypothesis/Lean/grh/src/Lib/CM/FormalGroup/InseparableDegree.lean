import Lib.CM.FormalGroup.PrimeNotation
import Lib.CM.Integrality.IsogenyIntegrality

/-!
# The inseparable degree

For `α ∈ 𝒪_K` let `o(α)` be the order in `y` of `y(α z) ∈ 𝒪[[y]]` modulo the maximal ideal of `𝒪`.

* `New.CMLattice.insepDegree_le`: `o(α) ≤ α ᾱ` for `α ≠ 0`, since `x(α z)` is, up to a unit, an
  integral polynomial in `x` with a unit coefficient in a degree at most `α ᾱ`.
* `New.CMLattice.insepDegree_piPrime_le`: `o(π_p) ≤ q_p` for every prime `p`.

## Notation

* `C : CMLattice d` is a lattice `Λ` stable under `𝒪_K = quadInt d`, the ring of integers of
  `K = ℚ(√-d)` in `ℂ`, with a point `t = C.t` of order two modulo `Λ`.
* `ιₚ : ℂ →+* ℂ_[p]` is the chosen place, `𝒪 = valRingCp p` is the valuation ring of `ℂ_[p]`, and
  `seriesToCp` is the inclusion `𝒪[[X]] → ℂ_[p][[X]]`.
* `taylorVia ιₚ f` is the Taylor series of `f` at `0` with `ιₚ` applied to its coefficients.
* `x` and `y` are the series of `C.translatedX` and `C.translatedY`, the coordinates of the curve
  `y ^ 2 + a₁ x y = x ^ 3 + x` at `z + t`, and `C.integralSeriesRing` is the ring `𝒪[[y]]`; `σ` is
  the sigma function of `Λ` and `θ = C.θ` its normalised twisted translate by `t`, with `θ(0) = 1`
  and `σ ^ 2 = x θ ^ 2`.

## Relation to the literature

Known result: the inseparable degree of the reduction of an isogeny is at most its degree. This
gives the bound on the height of the formal group in Deuring's criterion. Sources: Deuring, Die
Typen der Multiplikatorenringe elliptischer Funktionenkörper; Blake, A Deuring criterion for abelian
varieties, arXiv 1311.5454, Theorem 1.1; Bluher, Formal groups, elliptic curves, and some theorems
of Couveignes, ANTS-III, LNCS 1423 (1998), 3.2 and 6.1 (numbering of arXiv math/9708215).
-/

open PowerSeries IsLocalRing ComplexConjugate

namespace New

/-- Over a field, the order of `f(g)` is the product of the orders of `f` and `g`, for a power
series `g` without constant term. -/
lemma order_subst {k : Type*} [Field k] {g : k⟦X⟧} (hg : constantCoeff g = 0) (f : k⟦X⟧) :
    order (subst g f : k⟦X⟧) = f.order * g.order := by
  have hg_subst : HasSubst g := .of_constantCoeff_zero' hg
  obtain rfl | hf := eq_or_ne f 0
  · rw [← coe_substAlgHom hg_subst, map_zero, order_zero,
      ENat.top_mul (order_ne_zero_iff_constCoeff_eq_zero.2 hg)]
  -- Write `f = X ^ n * u` with `u(0) ≠ 0`; then `f(g) = g ^ n * u(g)`, and `u(g)` is a unit.
  have hu : IsUnit (divXPowOrder f) :=
    isUnit_iff_constantCoeff.2 (Ne.isUnit (mt constantCoeff_divXPowOrder_eq_zero_iff.1 hf))
  have hu_subst : order (subst g (divXPowOrder f) : k⟦X⟧) = 0 := by
    simpa only [← coe_substAlgHom hg_subst] using order_zero_of_isUnit (hu.map _)
  have h_eq : (subst g f : k⟦X⟧) = g ^ f.order.toNat * subst g (divXPowOrder f) := by
    conv_lhs => rw [← X_pow_order_mul_divXPowOrder (f := f)]
    rw [subst_mul hg_subst, subst_pow hg_subst, subst_X hg_subst]
  rw [h_eq, order_mul, order_pow, hu_subst, add_zero, nsmul_eq_mul, coe_toNat_order hf]

variable {p : ℕ} [Fact p.Prime]

namespace CMLattice
variable {d : ℕ} (C : CMLattice d) [PadicPlace p]

/-- The order in `y` of a series `f ∈ 𝒪[[y]]` modulo the maximal ideal of `𝒪`: write `f = g(y)` with
`g ∈ 𝒪[[X]]` and take the order of the reduction of `g`. Here `y` is the Taylor series of
`C.translatedY`. The value for `f` outside `𝒪[[y]]` has no meaning. -/
noncomputable def reducedOrder (f : ℂ_[p]⟦X⟧) : ℕ∞ :=
  let expansion : (valRingCp p)⟦X⟧ :=
    Function.invFun (fun g ↦ subst (taylorVia ιₚ C.translatedY) (seriesToCp g)) f
  (expansion.map (residue (valRingCp p))).order

lemma constantCoeff_taylorVia_translatedY : constantCoeff (taylorVia ιₚ C.translatedY) = 0 :=
  C.isSeriesGenerator_translatedY.constantCoeff_eq_zero

lemma coeff_one_taylorVia_translatedY : coeff 1 (taylorVia ιₚ C.translatedY) = 1 :=
  C.isSeriesGenerator_translatedY.coeff_one

/-- Every element of `C.integralSeriesRing = 𝒪[[y]]` is `g(y)` for an integral series `g`. -/
lemma exists_eq_subst_of_mem_integralSeriesRing {f : ℂ_[p]⟦X⟧} (hf : f ∈ C.integralSeriesRing) :
    ∃ g : (valRingCp p)⟦X⟧, f = subst (taylorVia ιₚ C.translatedY) (seriesToCp g) :=
  (C.isSeriesGenerator_translatedY.mem_iff f).1 hf

/-- For an integral series `g ∈ 𝒪[[X]]`, viewed in `ℂ_[p][[X]]` by `seriesToCp`, the reduced order
of `g(y)` is the order of the reduction of `g` modulo the maximal ideal of `𝒪`, where `y` is the
Taylor series of `C.translatedY`. -/
lemma reducedOrder_subst_translatedY (g : (valRingCp p)⟦X⟧) :
    C.reducedOrder (subst (taylorVia ιₚ C.translatedY) (seriesToCp g)) =
      (g.map (residue (valRingCp p))).order := by
  have h_inj : Function.Injective fun u : (valRingCp p)⟦X⟧ ↦
      (subst (taylorVia ιₚ C.translatedY) (seriesToCp u) : ℂ_[p]⟦X⟧) :=
    C.isSeriesGenerator_translatedY.subst_injective.comp seriesToCp_injective
  rw [reducedOrder, Function.leftInverse_invFun h_inj g]

/-- The reduced order (the order in `y` modulo the maximal ideal) is additive on products in
`C.integralSeriesRing = 𝒪[[y]]`. -/
lemma reducedOrder_mul {f g : ℂ_[p]⟦X⟧} (hf : f ∈ C.integralSeriesRing)
    (hg : g ∈ C.integralSeriesRing) :
    C.reducedOrder (f * g) = C.reducedOrder f + C.reducedOrder g := by
  obtain ⟨u, rfl⟩ := C.exists_eq_subst_of_mem_integralSeriesRing hf
  obtain ⟨v, rfl⟩ := C.exists_eq_subst_of_mem_integralSeriesRing hg
  rw [← subst_mul (.of_constantCoeff_zero' C.constantCoeff_taylorVia_translatedY), ← map_mul,
    reducedOrder_subst_translatedY, map_mul, order_mul, reducedOrder_subst_translatedY,
    reducedOrder_subst_translatedY]

/-- Let `T ∈ C.integralSeriesRing = 𝒪[[y]]` have no constant term and let `g` be an integral series.
The reduced order of `g(T)` (its order in `y` modulo the maximal ideal) is the order of the
reduction of `g` times the reduced order of `T`. -/
lemma reducedOrder_subst {T : ℂ_[p]⟦X⟧} (hT : T ∈ C.integralSeriesRing) (hT₀ : constantCoeff T = 0)
    (g : (valRingCp p)⟦X⟧) :
    C.reducedOrder (subst T (seriesToCp g)) =
      (g.map (residue (valRingCp p))).order * C.reducedOrder T := by
  -- With `T = u(y)` we have `g(T) = g(u)(y)`, and reduction commutes with substitution.
  obtain ⟨u, rfl⟩ := C.exists_eq_subst_of_mem_integralSeriesRing hT
  set y : ℂ_[p]⟦X⟧ := taylorVia ιₚ C.translatedY
  have hy₀ : constantCoeff y = 0 := C.constantCoeff_taylorVia_translatedY
  have hu₀ : constantCoeff u = 0 := Subtype.ext (by rwa [constantCoeff_subst_eq hy₀] at hT₀)
  have hu : HasSubst u := .of_constantCoeff_zero' hu₀
  have h_comp : (subst (subst y (seriesToCp u) : ℂ_[p]⟦X⟧) (seriesToCp g) : ℂ_[p]⟦X⟧) =
      subst y (seriesToCp (subst u g)) := by
    rw [show seriesToCp (subst u g) = subst (seriesToCp u) (seriesToCp g) from map_subst hu g,
      subst_comp_subst_apply (.of_constantCoeff_zero (by rwa [constantCoeff_subst_eq hy₀] at hT₀))
        (.of_constantCoeff_zero' hy₀)]
  rw [h_comp, reducedOrder_subst_translatedY, reducedOrder_subst_translatedY,
    show map (residue (valRingCp p)) (subst u g) = subst (u.map _) (g.map _) from map_subst hu g,
    order_subst (by simp [← coeff_zero_eq_constantCoeff_apply, hu₀])]

/-- A series in `C.integralSeriesRing = 𝒪[[y]]` whose constant coefficient has norm one has the
reduced order (the order in `y` modulo the maximal ideal) zero. -/
lemma reducedOrder_eq_zero {f : ℂ_[p]⟦X⟧} (hf : f ∈ C.integralSeriesRing)
    (hf₀ : ‖constantCoeff f‖ = 1) : C.reducedOrder f = 0 := by
  obtain ⟨u, rfl⟩ := C.exists_eq_subst_of_mem_integralSeriesRing hf
  rw [constantCoeff_subst_eq C.constantCoeff_taylorVia_translatedY] at hf₀
  have hu : IsUnit u := isUnit_iff_constantCoeff.2 (isUnit_integer_iff_norm_eq_one.2 hf₀)
  rw [reducedOrder_subst_translatedY, order_zero_of_isUnit (hu.map _)]

/-- A series in `C.integralSeriesRing = 𝒪[[y]]` without constant term whose linear coefficient has
norm one has the reduced order (the order in `y` modulo the maximal ideal) one. -/
lemma reducedOrder_eq_one {T : ℂ_[p]⟦X⟧} (hT : T ∈ C.integralSeriesRing) (hT₀ : constantCoeff T = 0)
    (hT₁ : ‖coeff 1 T‖ = 1) : C.reducedOrder T = 1 := by
  obtain ⟨u, rfl⟩ := C.exists_eq_subst_of_mem_integralSeriesRing hT
  rw [constantCoeff_subst_eq C.constantCoeff_taylorVia_translatedY] at hT₀
  rw [coeff_one_subst C.constantCoeff_taylorVia_translatedY, coeff_one_taylorVia_translatedY,
    mul_one] at hT₁
  rw [reducedOrder_subst_translatedY, ← Nat.cast_one, order_eq_nat]
  have hu₁ : IsUnit (coeff 1 u) := isUnit_integer_iff_norm_eq_one.2 hT₁
  simp [show constantCoeff u = 0 from Subtype.ext hT₀, hu₁]

variable [PrimeSevenModEight d]

/-- The Taylor series `x = y ^ 2 + ⋯` of `C.translatedX` has the reduced order (the order in `y`
modulo the maximal ideal) two. -/
lemma reducedOrder_translatedX : C.reducedOrder (taylorVia ιₚ C.translatedX) = 2 := by
  set x : ℂ_[p]⟦X⟧ := taylorVia ιₚ C.translatedX
  set y : ℂ_[p]⟦X⟧ := taylorVia ιₚ C.translatedY
  have hx : x ∈ C.integralSeriesRing := C.taylorVia_translatedX_mem_integralSeriesRing
  have hy : y ∈ C.integralSeriesRing := C.isSeriesGenerator_translatedY.generator_mem
  -- The cubic reads `x u = y ^ 2` with the unit `u = 1 + x ^ 2 - a₁ y`.
  let u : ℂ_[p]⟦X⟧ := 1 + x ^ 2 - ιₚ C.a₁ • y
  have hu : u ∈ C.integralSeriesRing := sub_mem (add_mem (one_mem _) (pow_mem hx 2))
    (C.isSeriesGenerator_translatedY.smul_mem C.norm_a₁_le_one hy)
  have h_cubic : x * u = y * y := by
    simp only [u, smul_eq_C_mul]
    linear_combination -C.taylorVia_curve_eq ιₚ
  have hu₀ : C.reducedOrder u = 0 := C.reducedOrder_eq_zero hu
    (by simp [u, x, y, translatedX, constantCoeff_taylorVia, translatedY_zero])
  have hy₁ : C.reducedOrder y = 1 := C.reducedOrder_eq_one hy
    C.constantCoeff_taylorVia_translatedY (by simp [y])
  calc
    C.reducedOrder x = C.reducedOrder (x * u) := by rw [C.reducedOrder_mul hx hu, hu₀, add_zero]
    _ = 2 := by rw [h_cubic, C.reducedOrder_mul hy hy, hy₁, one_add_one_eq_two]

/-- The number `o(α)`: the order in `y` of `y(α z)` modulo the maximal ideal of `𝒪`, where `y` is
the Taylor series of `C.translatedY`. -/
noncomputable def insepDegree (α : ℂ) : ℕ∞ :=
  C.reducedOrder (rescale (ιₚ α) (taylorVia ιₚ C.translatedY))

/-- For `α` in the ring of integers `quadInt d` of `ℚ(√-d)`, the series `y(α z)` lies in
`C.integralSeriesRing = 𝒪[[y]]`, where `y` is the Taylor series of `C.translatedY`. -/
lemma rescale_translatedY_mem_of_mem_quadInt {α : ℂ} (hα : α ∈ quadInt d) :
    rescale (ιₚ α) (taylorVia ιₚ C.translatedY) ∈ C.integralSeriesRing := by
  obtain ⟨ν, hν⟩ := exists_isIsogeny_of_mul_mem_lattice (C.mul_mem_of_quadInt hα)
  exact C.rescale_translatedY_mem_integralSeriesRing hν

/-- For `α` in the ring of integers `quadInt d` and `f ∈ C.integralSeriesRing = 𝒪[[y]]`, the reduced
order of `f(α z)` is the reduced order of `f` times `o(α) = C.insepDegree α`. -/
lemma reducedOrder_rescale {α : ℂ} (hα : α ∈ quadInt d) {f : ℂ_[p]⟦X⟧}
    (hf : f ∈ C.integralSeriesRing) :
    C.reducedOrder (rescale (ιₚ α) f) = C.reducedOrder f * C.insepDegree α := by
  obtain ⟨g, rfl⟩ := C.exists_eq_subst_of_mem_integralSeriesRing hf
  have hy₀ := C.constantCoeff_taylorVia_translatedY (p := p)
  rw [rescale_subst hy₀, reducedOrder_subst_translatedY, insepDegree,
    C.reducedOrder_subst (C.rescale_translatedY_mem_of_mem_quadInt hα)
      (constantCoeff_rescale.trans hy₀)]

/-- The inseparable degree is multiplicative on the ring of integers `quadInt d`. -/
lemma insepDegree_mul {α β : ℂ} (hα : α ∈ quadInt d) (hβ : β ∈ quadInt d) :
    C.insepDegree (α * β) = C.insepDegree α * C.insepDegree β := by
  rw [insepDegree, map_mul, ← rescale_rescale,
    C.reducedOrder_rescale hβ (C.rescale_translatedY_mem_of_mem_quadInt hα), ← insepDegree]

/-- An element `α` of the ring of integers `quadInt d` that is a unit at the place `ιₚ` has the
inseparable degree one. -/
lemma insepDegree_eq_one {α : ℂ} (hα : α ∈ quadInt d) (hα_unit : ‖ιₚ α‖ = 1) :
    C.insepDegree α = 1 := by
  refine C.reducedOrder_eq_one (C.rescale_translatedY_mem_of_mem_quadInt hα) ?_ ?_
  · simp [constantCoeff_rescale]
  · simp [coeff_rescale, hα_unit]

lemma insepDegree_pow {α : ℂ} (hα : α ∈ quadInt d) (n : ℕ) :
    C.insepDegree (α ^ n) = C.insepDegree α ^ n := by
  induction n with
  | zero => simpa using C.insepDegree_eq_one (one_mem _) (by simp)
  | succ n ih => rw [pow_succ, C.insepDegree_mul (pow_mem hα n) hα, ih, pow_succ]

/-- The torsion value (the value at `0` of the twisted translate) of the square of the sigma
function `σ`, in degree two (the degree of `σ ^ 2` as a section: `σ ^ 2 ∈ C.sections 2`), at the
point `t` of order two is a unit at the place `ιₚ`. Indeed the torsion value at `t` of `θ`, the
normalised twisted translate of `σ` by `t`, vanishes. -/
lemma norm_torsionValue_sigma_sq_t : ‖ιₚ (C.torsionValue 2 (C.σ ^ 2) C.t)‖ = 1 := by
  have hθ : C.torsionValue 1 C.θ C.t = 0 := by
    simp [torsionValue_eq, C.theta_eq_zero_iff.2 C.two_t_mem]
  have hσ : ‖ιₚ (C.torsionValue 1 C.σ C.t)‖ = 1 := by
    simpa [hθ] using C.max_norm_torsionValue (p := p)
      (⟨2, two_ne_zero, by simpa [two_mul] using C.two_t_mem⟩ : C.IsTorsion C.t)
  rw [C.torsionValue_pow 2 1, map_pow, norm_pow, hσ, one_pow]

/-- If `α ≠ 0` lies in the ring of integers `quadInt d` and has the norm `ν`, then `t / α` is a
torsion point: `2 ν · (t / α) = ᾱ · 2 t` lies in the lattice. -/
lemma isTorsion_t_div {α : ℂ} (hα : α ∈ quadInt d) (hα₀ : α ≠ 0) {ν : ℕ} (hν : α * conj α = ν) :
    C.IsTorsion (C.t / α) := by
  have h_eq : ((2 * ν : ℕ) : ℂ) * (C.t / α) = conj α * (C.t + C.t) := by
    rw [Nat.cast_mul, Nat.cast_ofNat, ← hν]
    field
  exact ⟨2 * ν, mul_ne_zero two_ne_zero fun hν_zero ↦ by simp [hν_zero, hα₀] at hν,
    by simpa only [h_eq] using C.mul_mem_of_quadInt (conj_mem_quadInt hα) C.two_t_mem⟩

/-- Let `α ≠ 0` lie in the ring of integers `quadInt d` and have the norm `ν`. As Taylor series over
`ℂ_[p]`, `σ(α z) ^ 2 = θ ^ (2 ν) R(x)` with `x` the series of `C.translatedX`, for a polynomial `R`
whose coefficients are integral at the place `ιₚ` and which has a unit coefficient in a degree at
most `ν`. Here `σ` is the sigma function of the lattice and `θ` is its normalised twisted translate
by the point `t` of order two. -/
lemma exists_rescale_sigma_sq_eq {α : ℂ} (hα : α ∈ quadInt d) (hα₀ : α ≠ 0) {ν : ℕ}
    (hν : α * conj α = ν) :
    ∃ R : Polynomial ℂ,
      (∀ i : ℕ, ‖ιₚ (R.coeff i)‖ ≤ 1) ∧
      (∃ i ≤ ν, ‖ιₚ (R.coeff i)‖ = 1) ∧
      rescale (ιₚ α) (taylorVia ιₚ (C.σ ^ 2)) =
        taylorVia ιₚ C.θ ^ (2 * ν) * (R.map ιₚ).aeval (taylorVia ιₚ C.translatedX) := by
  -- `σ(α z) ^ 2` is an even section of degree `2 ν` with integral torsion values; the monomial
  -- section of `(a, b, 0)` is `θ ^ a (σ ^ 2) ^ b`.
  have h_isog : C.IsIsogeny C.periodPair α ν := ⟨C.mul_mem_of_quadInt hα, by rw [hν]⟩
  have h_sec : C.σ ^ 2 ∈ C.sections 2 := by
    simpa [monomialSection] using C.monomialSection_mem (0, 1, 0)
  have h_int : C.HasIntegralValues 2 (C.σ ^ 2) := by
    simpa [monomialSection] using C.hasIntegralValues_monomialSection (0, 1, 0)
  have h_even : Function.Even fun z : ℂ ↦ (C.σ ^ 2) (α * z) := fun z ↦ by simp [sigma_neg]
  obtain ⟨R, hR⟩ : ∃ R : Polynomial ℂ,
      C.IsIntegralEvenExpansion (2 * ν) (fun z : ℂ ↦ (C.σ ^ 2) (α * z)) R :=
    C.exists_polynomial_of_even (C.comp_mul_mem_sections h_isog h_sec) (h_int.comp_isogeny h_isog)
      h_even
  refine ⟨R, hR.norm_coeff_le_one, ?_,
    by rw [← hR.taylorVia_eq, taylorVia, taylorVia, taylorAtZero_comp_mul, rescale_map]⟩
  -- At `t / α` the torsion value of `σ(α z) ^ 2` is that of `σ ^ 2` at `t`, which is a unit.
  let m (i : ℕ) : ℂ := C.torsionValue (2 * ν) (C.monomialSection (2 * ν - 2 * i, i, 0)) (C.t / α)
  have h_value : C.torsionValue 2 (C.σ ^ 2) C.t =
      ∑ i ∈ Finset.range (ν + 1), R.coeff i * m i := calc
    _ = C.torsionValue (2 * ν) (fun z : ℂ ↦ (C.σ ^ 2) (α * z)) (C.t / α) := by
      rw [C.torsionValue_comp_isogeny h_isog, mul_div_cancel₀ C.t hα₀]
    _ = ∑ i ∈ Finset.range (ν + 1), R.coeff i * m i := by
      simp only [m, torsionValue_eq, hR.eq_sum, Nat.mul_div_cancel_left ν two_pos,
        Finset.sum_mul, mul_assoc]
  -- The monomials have integral torsion values, so the largest term has a unit coefficient.
  have hm (i : ℕ) (hi : i ≤ ν) : ‖ιₚ (m i)‖ ≤ 1 := by
    have h_deg : monomialDeg (2 * ν - 2 * i, i, 0) = 2 * ν := by grind
    simpa only [h_deg] using C.hasIntegralValues_monomialSection (2 * ν - 2 * i, i, 0) _
      (C.isTorsion_t_div hα hα₀ hν)
  obtain ⟨i, hi, h_le⟩ : ∃ i ∈ Finset.range (ν + 1),
      ‖∑ j ∈ Finset.range (ν + 1), ιₚ (R.coeff j * m j)‖ ≤ ‖ιₚ (R.coeff i * m i)‖ :=
    IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty Finset.nonempty_range_add_one _
  have hi_le : i ≤ ν := Finset.mem_range_succ_iff.1 hi
  refine ⟨i, hi_le, (hR.norm_coeff_le_one i).antisymm ?_⟩
  calc
    1 = ‖∑ j ∈ Finset.range (ν + 1), ιₚ (R.coeff j * m j)‖ := by
      rw [← map_sum, ← h_value, C.norm_torsionValue_sigma_sq_t]
    _ ≤ ‖ιₚ (R.coeff i)‖ * ‖ιₚ (m i)‖ := by rwa [← norm_mul, ← map_mul]
    _ ≤ ‖ιₚ (R.coeff i)‖ := mul_le_of_le_one_right (norm_nonneg _) (hm i hi_le)

omit [PrimeSevenModEight d] in
/-- The Taylor series of `σ ^ 2` is `x θ ^ 2`. Here `σ` is the sigma function of the lattice, `θ`
is its normalised twisted translate by `t`, and `x` is the series of `C.translatedX`. -/
lemma taylorVia_sigma_sq :
    taylorVia ιₚ (C.σ ^ 2) = taylorVia ιₚ C.translatedX * taylorVia ιₚ C.θ ^ 2 := by
  rw [taylorVia, C.taylorAtZero_congr (f := C.σ ^ 2) (g := fun z ↦ C.translatedX z * C.θ z ^ 2)
      fun z hz ↦ C.sigma_sq_eq_translatedX_mul_theta_sq hz,
    taylorAtZero_mul (by fun_prop) (by fun_prop), taylorAtZero_pow (by fun_prop), map_mul, map_pow]

/-- Let `α` in the ring of integers `quadInt d` have the norm `ν`. As Taylor series over `ℂ_[p]`,
`θ(α z) = θ ^ ν v` for a series `v ∈ C.integralSeriesRing = 𝒪[[y]]` with the constant coefficient
`1`. Here `θ` is the normalised twisted translate of `σ` by `t`. -/
lemma exists_rescale_theta_eq_pow_mul_of_mem_quadInt {α : ℂ} (hα : α ∈ quadInt d) {ν : ℕ}
    (hν : α * conj α = ν) :
    ∃ v ∈ C.integralSeriesRing, constantCoeff v = 1 ∧
      rescale (ιₚ α) (taylorVia ιₚ C.θ) = taylorVia ιₚ C.θ ^ ν * v := by
  have h_isog : C.IsIsogeny C.periodPair α ν := ⟨C.mul_mem_of_quadInt hα, by rw [hν]⟩
  obtain ⟨v, hv, hθ⟩ := C.exists_rescale_theta_eq_theta_pow_mul (p := p) h_isog
  refine ⟨v, hv, ?_, hθ⟩
  simpa [constantCoeff_rescale, constantCoeff_taylorVia, theta_zero] using
    (congrArg constantCoeff hθ).symm

/-- Let `R` be a complex polynomial whose coefficients are integral at the place `ιₚ` and whose
coefficient of degree `i` is a unit there. Then `R(x)` has the reduced order (the order in `y`
modulo the maximal ideal) at most `2 i`, where `x` is the series of `C.translatedX`. -/
lemma reducedOrder_aeval_translatedX_le {R : Polynomial ℂ} (hR : ∀ j : ℕ, ‖ιₚ (R.coeff j)‖ ≤ 1)
    {i : ℕ} (hi : ‖ιₚ (R.coeff i)‖ = 1) :
    C.reducedOrder ((R.map ιₚ).aeval (taylorVia ιₚ C.translatedX)) ≤ 2 * i := by
  obtain ⟨S, hS⟩ : ∃ S : (valRingCp p)⟦X⟧, seriesToCp S = (R.map ιₚ : Polynomial ℂ_[p]) :=
    mem_range_seriesToCp.2 (by simpa using hR)
  have h_coeff : ((coeff i S : valRingCp p) : ℂ_[p]) = ιₚ (R.coeff i) :=
    (congrArg (coeff i) hS).trans (by simp)
  have h_unit : IsUnit (coeff i S) := isUnit_integer_iff_norm_eq_one.2 (by rw [h_coeff, hi])
  have h_order : (S.map (residue (valRingCp p))).order ≤ i :=
    order_le i (h_unit.map (residue (valRingCp p))).ne_zero
  have hx₀ : constantCoeff (taylorVia ιₚ C.translatedX) = 0 := by
    simp [translatedX, constantCoeff_taylorVia]
  rw [← subst_coe (.of_constantCoeff_zero' hx₀), ← hS,
    C.reducedOrder_subst C.taylorVia_translatedX_mem_integralSeriesRing hx₀,
    C.reducedOrder_translatedX, mul_comm]
  gcongr

/-- **Inseparable degree.** Let `d` be a prime ≡ 7 mod 8 and fix a `p`-adic place of ℂ. Let
`C : CMLattice d` be a CM lattice: a lattice stable under the integers of ℚ(√-d), with a point `t`
of order two scaled so that `℘''(t) = 2` and a square root of `12 ℘(t)`, and with neither `ω t` nor
`ω̄ t` in the lattice, where `ω = (1 + √-d) / 2`. If `α ≠ 0` lies in the ring of integers
`quadInt d` of `ℚ(√-d)` and `α ᾱ = ν`, then `C.insepDegree α` is at most `ν`; this is the order in
`y` of `y(α z)` modulo the maximal ideal of `𝒪` at the chosen place, where `y` is the Taylor series
of `C.translatedY`. -/
lemma insepDegree_le {α : ℂ} (hα : α ∈ quadInt d) (hα₀ : α ≠ 0) {ν : ℕ} (hν : α * conj α = ν) :
    C.insepDegree (p := p) α ≤ ν := by
  -- We have `x(α z) v ^ 2 = R(x)` with the unit `v = θ(α z) / θ ^ ν`; compare the orders.
  obtain ⟨R, hR_int, ⟨i, hi_le, hi_unit⟩, hR⟩ :=
    C.exists_rescale_sigma_sq_eq (p := p) hα hα₀ hν
  obtain ⟨v, hv, hv₀, hθ⟩ := C.exists_rescale_theta_eq_pow_mul_of_mem_quadInt (p := p) hα hν
  set x : ℂ_[p]⟦X⟧ := taylorVia ιₚ C.translatedX
  have hx : x ∈ C.integralSeriesRing := C.taylorVia_translatedX_mem_integralSeriesRing
  have h_key : rescale (ιₚ α) x * (v * v) = (R.map ιₚ).aeval x := by
    have hθ_unit : IsUnit (taylorVia ιₚ C.θ) :=
      isUnit_iff_constantCoeff.2 (by simp [constantCoeff_taylorVia, theta_zero])
    refine (hθ_unit.pow (2 * ν)).mul_left_cancel ?_
    rw [← hR, taylorVia_sigma_sq, map_mul, map_pow, hθ]
    ring
  have hv_order : C.reducedOrder (v * v) = 0 :=
    C.reducedOrder_eq_zero (mul_mem hv hv) (by simp [hv₀])
  have hx_rescale : rescale (ιₚ α) x ∈ C.integralSeriesRing :=
    C.isSeriesGenerator_translatedY.rescale_mem
      (C.rescale_translatedY_mem_of_mem_quadInt hα) hx
  have h_two : 2 * C.insepDegree α ≤ 2 * ν := calc
    2 * C.insepDegree α = C.reducedOrder (rescale (ιₚ α) x * (v * v)) := by
      rw [C.reducedOrder_mul hx_rescale (mul_mem hv hv), hv_order, add_zero,
        C.reducedOrder_rescale hα hx, C.reducedOrder_translatedX]
    _ ≤ 2 * i := by
      rw [h_key]
      exact C.reducedOrder_aeval_translatedX_le hR_int hi_unit
    _ ≤ 2 * ν := by gcongr
  exact (ENat.mul_le_mul_left_iff two_ne_zero (ENat.ofNat_ne_top 2)).1 h_two

/-- **Inseparable degree of `π_p`.** For every prime `p` the inseparable degree of `π_p` (the order
in `y` of `y(π_p z)` modulo the maximal ideal) is at most `q_p`. Here `π_p = piPrime d p` is `√-d`
for `p = d` and `p` otherwise, and `q_p = primeNorm d p` is the norm of a prime of `ℚ(√-d)` above
`p`. A case of Deuring's criterion: the formal group of the reduction has height at most one at
split primes and at most two at the others. -/
lemma insepDegree_piPrime_le : C.insepDegree (p := p) (piPrime d p) ≤ primeNorm d p := by
  obtain hp | hp := ne_or_eq (chiK d p) 1
  · exact C.insepDegree_le (piPrime_mem_quadInt d) (piPrime_ne_zero d) (piPrime_mul_conj d hp)
  -- For split `p` (`chiK d p = 1`) we have `π_p = q_p = p`, and `p ^ h = α ᾱ` with `‖ιₚ ᾱ‖ = 1`.
  obtain ⟨h, α, h_ne, hα, h_norm, h_unit⟩ : ∃ (h : ℕ) (α : ℂ),
      h ≠ 0 ∧ α ∈ quadInt d ∧ α * conj α = p ^ h ∧ ‖ιₚ (conj α)‖ = 1 :=
    exists_mul_conj_eq_pow hp
  have hα₀ : α ≠ 0 := fun hα_zero ↦ by simp [hα_zero] at h_unit
  have h_pow : C.insepDegree p ^ h ≤ (p : ℕ∞) ^ h := calc
    C.insepDegree p ^ h = C.insepDegree α * C.insepDegree (conj α) := by
      rw [← C.insepDegree_pow (natCast_mem _ p), ← h_norm,
        C.insepDegree_mul hα (conj_mem_quadInt hα)]
    _ = C.insepDegree α := by rw [C.insepDegree_eq_one (conj_mem_quadInt hα) h_unit, mul_one]
    _ ≤ (p : ℕ∞) ^ h := by exact_mod_cast C.insepDegree_le hα hα₀ (by rw [h_norm, Nat.cast_pow])
  have hpd : p ≠ d := by grind [chiK_cases d p]
  rw [show primeNorm d p = p by simp [primeNorm, hp], piPrime, ite_eq_right hpd]
  by_contra! h_lt
  exact (WithTop.pow_lt_pow_left h_lt h_ne).not_ge h_pow

end CMLattice

end New
