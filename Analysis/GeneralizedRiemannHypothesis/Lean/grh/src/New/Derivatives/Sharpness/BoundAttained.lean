import New.Derivatives.Sharpness.Cases

/-!
# Sharpness of the valuation bound

* `New.Data.exists_le_norm_coeff_indicatorDatum`: the reduction to the curve. Some Taylor
  coefficient of degree `l` of an indicator datum, times the factor `vacuumScale ^ 12` of the
  integral vacuum, has valuation at most `val₁₂(l) + v(M ^ (12 f) c₀)`, where `c₀` is a value of the
  integral vacuum.
* `New.Data.exists_rpow_neg_localPrimeSumTotal_le_norm_coeff`: for degrees `l` between the weights
  `κ` and `κ + x ^ 42`, with `x = D.x`, there is one number `t ≠ 0` with small conjugates such that
  at every prime some Taylor coefficient of degree `l` of an indicator datum, times `∏ l!` and the
  factor `vacuumScale ^ 12` of the integral vacuum, has valuation at most `S_p + v(t)`.

The theta product times monomials in the function `y` along the forms of a tight frame is the Taylor
series of a vector with integral values, and Fourier inversion expands that vector in translates of
the vacuum. Each translate is a sum of indicator data times roots of unity.

Notions from other files:
* A tight frame of length `M` with multiplicities `c` is a family `w` of lattice vectors with
  `∑ c i Φ_σ(w i) conj(Φ_τ(w i)) = M δ_{σ τ}` (`New.IsTightFrame`). Here `M = D.M`.
* `val_n(l) ≤ r` (`CMLattice.LeastValLE`) says that some coefficient of degree `l` in some product
  over `n` copies of `H Θ` has valuation at most `r`. Here `Θ` is the theta product of the frame and
  `H` is an integral series in the functions `y` along the forms of the frame.
* `intVacuum V` is the vacuum `V.vacElem` times `vacuumScale ^ n`, where `n` is the rank of `V`.
* `π_M = D.piM` is the conjugate of the integer `π̄_M = D.piMBar` of `K`, of norm `M`.
* `D.localPrimeSumTotal p` is the forced divisibility `S_p` at the weights of `D`, the sum of
  `D.localPrimeSum p (D.weight τ) τ` over the infinite places `τ`.
* `α` is the finite idele of the Weil data of `D.E`, `𝔞₀ = E ∩ α Ô` its lattice, `finVec x` the
  adelic vector `(0, α x)` with zero part at infinity, and `D.f` the number of infinite places
  of `D.E`.

## Relation to the literature

Sharpness for one curve (slope `p / (p² - 1)`, attained in infinitely many degrees) is known in the
literature.

Related work: Bannai–Kobayashi, Algebraic theta functions and the p-adic interpolation of
Eisenstein–Kronecker numbers (arXiv v1), 2006; Bannai–Kobayashi–Yasuda, Radius of convergence of the
p-adic sigma function, 2017; Schneider–Teitelbaum, p-adic Fourier theory, 2001; Bannai–Kobayashi,
Integral structures on p-adic Fourier theory, 2016.
-/

open Finset MvPowerSeries ComplexConjugate Real IsUltrametricDist Fintype Nat Finsupp

namespace New

section copies

/-- The embedding of the variables of one copy as the `b`-th of `k` copies. -/
def copyEmbedding {X : Type} {k : ℕ} (b : Fin k) : X × Unit ↪ X × Fin k × Unit :=
  ⟨fun x ↦ (x.1, b, ()), fun _ _ h ↦ Prod.ext (Prod.mk.inj h).1 rfl⟩

lemma copyEmbedding_apply {X : Type} {k : ℕ} (b : Fin k) (x : X × Unit) :
    copyEmbedding b x = (x.1, b, ()) := rfl

/-- The exponent in `k` copies of the variables whose part in the `b`-th copy is `α b`. -/
noncomputable def copyExponent {X : Type} {k : ℕ} (α : Fin k → X × Unit →₀ ℕ) :
    X × Fin k × Unit →₀ ℕ :=
  ∑ b : Fin k, (α b).embDomain (copyEmbedding b)

/-- The part of `copyExponent α` in the `b`-th copy is `α b`. -/
lemma copyExponent_apply {X : Type} {k : ℕ} (α : Fin k → X × Unit →₀ ℕ) (x : X) (b : Fin k) :
    copyExponent α (x, b, ()) = α b (x, ()) := by
  rw [copyExponent, finsetSum_apply, sum_eq_single_of_mem b (mem_univ b)]
  · exact embDomain_apply_self (copyEmbedding b) (α b) (x, ())
  · exact fun b' _ hb' ↦ embDomain_of_notMem_range _ _ _ (by simp [copyEmbedding_apply, hb'])

/-- The coefficient at `copyExponent α` of a product of series, each in the variables of its own
copy, is the product of the coefficients at the exponents `α b` of the copies. -/
lemma coeff_prod_rename_copyEmbedding {X R : Type} [Fintype X] [CommRing R] {k : ℕ}
    (α : Fin k → X × Unit →₀ ℕ) (Ψ : Fin k → MvPowerSeries (X × Unit) R) :
    coeff (copyExponent α) (∏ b : Fin k, rename (copyEmbedding b) (Ψ b)) =
      ∏ b : Fin k, coeff (α b) (Ψ b) := by
  classical
  let β₀ : Fin k →₀ X × Fin k × Unit →₀ ℕ :=
    equivFunOnFinite.symm fun b ↦ (α b).embDomain (copyEmbedding b)
  have hβ₀ : β₀ ∈ finsuppAntidiag univ (copyExponent α) := by simp [β₀, copyExponent]
  rw [coeff_prod, sum_eq_single_of_mem β₀ hβ₀]
  · simp only [β₀, equivFunOnFinite_symm_apply_apply, coeff_embDomain_rename]
  -- In a nonzero term each exponent `β b` lies in copy `b`, so it is the part `α b`.
  intro β hβ h_ne
  by_contra h_prod
  have h_range (b : Fin k) : β b ∈ Set.range (mapDomain (copyEmbedding b)) :=
    by_contra fun hb ↦ h_prod (prod_eq_zero (mem_univ b) (coeff_rename_eq_zero _ _ hb))
  choose (α' : Fin k → X × Unit →₀ ℕ) hα' using h_range
  have h_exponent : copyExponent α' = copyExponent α := by
    simpa [copyExponent, embDomain_eq_mapDomain, hα'] using (mem_finsuppAntidiag.1 hβ).1
  have h_copy (b : Fin k) : α' b = α b := by
    ext ⟨x, ⟨⟩⟩
    rw [← copyExponent_apply, h_exponent, copyExponent_apply]
  exact h_ne (Finsupp.ext fun b ↦ by simp [β₀, ← hα', h_copy, embDomain_eq_mapDomain])

end copies

namespace Data

open CMLattice Parameters QuadField Pointwise

/-- Substitute the linear form `∑ x, μ x • X_(x, b)` (`linearSeries`) in the variables of copy
`b` into the Taylor series of `f`, and apply `ιₚ : ℂ → ℂ_[p]` to the coefficients. The result is
the series `taylorVia ιₚ f` along the form `ιₚ ∘ μ` of one copy, renamed into copy `b`. -/
lemma map_subst_linearSeries_copy {p : ℕ} [Fact p.Prime] [PadicPlace p] {X : Type} [Fintype X]
    {k : ℕ} (f : ℂ → ℂ) (μ : X → ℂ) (b : Fin k) :
    ((taylorAtZero f).subst
      (linearSeries fun y : X × Fin k × Unit ↦ if y.2 = (b, ()) then μ y.1 else 0)).map ιₚ =
      rename (copyEmbedding b) ((taylorVia ιₚ f).subst
        (linearSeries fun x : X × Unit ↦ (ιₚ (μ x.1) : ℂ_[p]))) := by
  have h_form : (linearSeries fun y : X × Fin k × Unit ↦ if y.2 = (b, ()) then μ y.1 else 0).map
      ιₚ = rename (copyEmbedding b) (linearSeries fun x : X × Unit ↦ (ιₚ (μ x.1) : ℂ_[p])) := by
    simp [linearSeries, copyEmbedding_apply, sum_prod_type, smul_eq_C_mul]
  -- Both sides are the series of `f` substituted into the linear form in the copy `b`.
  rw [PowerSeries.map_subst (.of_constantCoeff_zero (constantCoeff_linearSeries _)), h_form]
  simp only [rename_eq_subst, PowerSeries.subst]
  rw [subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero
    (constantCoeff_linearSeries _)).const (.X_comp _)]

/-- The `p`-adic norm of a product of nonzero natural numbers is `p` to minus the sum of their
valuations. -/
lemma norm_natCast_prod_eq_rpow_neg_sum {p : ℕ} [hp : Fact p.Prime] [PadicPlace p] {X : Type}
    [Fintype X] {n : X → ℕ} (hn : ∀ x : X, n x ≠ 0) :
    ‖(ιₚ (∏ x : X, n x : ℕ) : ℂ_[p])‖ = p ^ (-∑ x : X, (padicValNat p (n x) : ℝ)) := by
  simp [norm_natCast_eq_inv_pow_padicValNat, hn, rpow_neg p.cast_nonneg, ← cast_sum,
    prod_pow_eq_pow_sum]

/-- The hermitian space `Hom(E, E¹²)` of `12 × 1` matrices over `E = D.E`, where `E` and `E¹²` carry
the sum of the norms of the coordinates (`stdSpace`). The sign of a coordinate is the product of
the signs of its row and column, here always `+1` (`homSigns 1 1`). The vectors of this file lie
in `𝒮 D.twelveSpace`, the space of functions on adelic vectors that models the adelic Heisenberg
representation. -/
noncomputable abbrev twelveSpace {P : Parameters} (D : Data P) :
    Space D.E (Fin 12 × Unit) (homSigns 1 1) :=
  (stdSpace D.E Unit).hom (stdSpace D.E (Fin 12))

/-- The series `Space.jetSeries` of a vector `F` on `Hom(E, E¹²)` at the scale `a = π_M * jetScale`:
for `F` in the finite part it is the Taylor series at `0` of `z ↦ Θ_F(a z)`, where `Θ_F` is the
theta function `Space.entireTheta F`. Here `π_M` is the conjugate of `D.piMBar` and
`jetScale = periodFactor * areaScale / cmPeriod`, where `cmPeriod 𝓞_K` is the lattice of the curve
`P.cmCurve`, `areaScale = √(2π / √d)` for `d = P.d`, and
`periodFactor = vacuumRoot / chowlaSelbergUnit` is a constant of the field `D.E = P.E D.towerExp`,
the cyclotomic extension of `K` at the level `D.towerExp` of the tower. -/
noncomputable abbrev twelveTaylor {P : Parameters} (D : Data P) :
    𝒮 D.twelveSpace →ₗ[ℂ] MvPowerSeries (D.Φ × Fin 12 × Unit) ℂ :=
  D.twelveSpace.jetSeries (conj ↑D.piMBar * P.jetScale D.towerExp)

/-- The vector on `Hom(E, E¹²)` whose part at infinity is the Gaussian `exp(-|x|² / 2)`
(`Fock.vacVector`), whose part at the places dividing `𝔪` is the indicator of the class `y₀` of
matrices over the residue ring `𝔪.ResidueRing = O_E/𝔪`, and which agrees with the vacuum
`Space.vacElem` at the other finite places. The three parts are put together by `modDatum`. -/
noncomputable abbrev indicatorDatum {P : Parameters} (D : Data P) (𝔪 : Modulus D.E)
    (y₀ : Matrix (Fin 12) Unit 𝔪.ResidueRing) : 𝒮 D.twelveSpace :=
  modDatum (stdSpace D.E Unit) (stdSpace D.E (Fin 12)) 𝔪 (Pi.single y₀ 1) Fock.vacVector

/-- Let `D` be admissible data for the parameters `P`, with `K = P.K = ℚ(√-d)` and `E = D.E` the
cyclotomic extension `P.E D.towerExp` of `K`; `D.Φ` is the set of its infinite places `τ`. Let `w`
be a tight frame of length `M = D.M` with multiplicities `c`. Let
`μ_i(z) = periodFactor * ∑ conj(Φ_τ(w i)) z_τ` be its linear forms (`resolutionForms`, read through
an embedding `ιₚ : ℂ → ℂ_[p]`). Let `θ` be the theta function of the elliptic curve
`P.cmCurve = ℂ / cmPeriod 𝓞_K`, let `y(z) = ½(℘′(z + t) - a₁(℘(z + t) - ℘(t)))` for its point `t`
and coefficient `a₁` (`translatedY`), and `Θ = ∏ θ(μ_i z) ^ c i` (`thetaProd`).

If `3 e b i ≤ c i`, there is a vector `F` of `𝒮 D.twelveSpace`, the Heisenberg model of functions on
the adelic `12 × 1` matrices over `E`, such that
* the rescaled Taylor series `twelveTaylor F` of its theta function `Space.entireTheta F` is the
  product over twelve copies `b` of the variables of the series `∏ y(μ_i z) ^ e b i * Θ`;
* its values at the adelic vectors `finVec x = (0, α x)`, for `x` over the finite adeles `𝔸f E`, are
  integral at `ιₚ`;
* its theta function is fixed by the signed translations along `π_M 𝔞₀¹²` (`IsThetaFunction`). -/
lemma exists_integral_isThetaFunction_twelveTaylor_eq {P : Parameters} {p : ℕ} [Fact p.Prime]
    [PadicPlace p] (D : Data P) {J : Type} [Fintype J] {w : J → D.E} {c : J → ℕ}
    (hw : IsTightFrame w c D.M) {e : Fin 12 → J → ℕ}
    (he : ∀ (b : Fin 12) (i : J), e b i * 3 ≤ c i) : ∃ F : 𝒮 D.twelveSpace,
    (D.twelveTaylor F).map ιₚ = ∏ b : Fin 12, rename (copyEmbedding b)
      ((∏ i : J, (taylorVia ιₚ P.cmCurve.translatedY).subst
        (linearSeries (P.resolutionForms (p := p) D.towerExp w i)) ^ e b i) *
        P.cmCurve.thetaProd (P.resolutionForms D.towerExp w) c) ∧
    (∀ x : Fin 12 × Unit → 𝔸f D.E, ‖(ιₚ (F (finVec x)) : ℂ_[p])‖ ≤ 1) ∧
    IsThetaFunction (star (algebraMap P.K D.E D.piMBar) • idealLattice D.E (Fin 12 × Unit))
      (Space.entireTheta F) := by
  -- `y ^ e θ ^ c = (y θ ^ 3) ^ e θ ^ (c - 3 e)` is a monomial section of degree `c`
  let monomialDegrees (x : J × Fin 12 × Unit) : ℕ × ℕ × ℕ :=
    (c x.1 - e x.2.1 x.1 * 3, 0, e x.2.1 x.1)
  have h_area : P.cmCurve.area = ‖(P.cmPeriod : ℂ)‖ ^ 2 / D.M * D.M * √P.d / 2 := by
    simp [area_eq_of_eq_scaledIdeal latticeModule_cmCurve, NeZero.ne D.M]
  obtain ⟨F, hF, hF_int, h_periods⟩ := exists_isResolutionProduct_of_isTightFrame D.twelveSpace
    D.piMBar (NeZero.ne D.M) D.piMBar_mul_conj hw monomialDegrees
    (fun x ↦ Nat.sub_add_cancel (he x.2.1 x.1)) cmPeriod_mem_cmCurve_lattice h_area
  refine ⟨F, ?_, hF_int p, h_periods⟩
  have h_scale : P.cmPeriod / conj ↑D.piMBar / P.areaScale *
      (conj ↑D.piMBar * P.jetScale D.towerExp) = P.periodFactor D.towerExp := by
    simp [jetScale, field]
  -- the form `μ_i` in the variables of copy `b`
  let copyForm : J × Fin 12 × Unit → D.Φ × Fin 12 × Unit → ℂ :=
    resolutionFormCoeff (P.periodFactor D.towerExp) w
  have h_taylor : D.twelveTaylor F = ∏ x : J × Fin 12 × Unit,
      (taylorAtZero (P.cmCurve.monomialSection (monomialDegrees x))).subst
        (linearSeries (copyForm x)) := by
    simpa [resolutionShift, h_scale] using hF.jetSeries_translate 0
      (conj ↑D.piMBar * P.jetScale D.towerExp)
  have h_monomial (x : J × Fin 12 × Unit) :
      taylorAtZero (P.cmCurve.monomialSection (monomialDegrees x)) =
      taylorAtZero P.cmCurve.translatedY ^ e x.2.1 x.1 * taylorAtZero P.cmCurve.θ ^ c x.1 := by
    simp (disch := fun_prop) [monomialDegrees, taylorAtZero_congr _ (monomialSection_eq _ _),
      Nat.sub_add_cancel (he x.2.1 x.1), mul_comm (taylorAtZero P.cmCurve.θ ^ c x.1)]
  have h_copy (f : ℂ → ℂ) (i : J) (b : Fin 12) :
      ((taylorAtZero f).subst (linearSeries (copyForm (i, b, ())))).map ιₚ =
        rename (copyEmbedding b)
          ((taylorVia ιₚ f).subst (linearSeries (P.resolutionForms (p := p) D.towerExp w i))) :=
    map_subst_linearSeries_copy f (fun τ ↦ P.periodFactor D.towerExp * conj (New.Φ τ (w i))) b
  have h_subst (x : J × Fin 12 × Unit) : PowerSeries.HasSubst (linearSeries (copyForm x)) :=
    .of_constantCoeff_zero (constantCoeff_linearSeries _)
  simp only [h_taylor, h_monomial, PowerSeries.subst_mul (h_subst _),
    PowerSeries.subst_pow (h_subst _), map_prod, map_mul, map_pow, prod_prod_type_right,
    Fintype.prod_unique, h_copy, thetaProd, prod_mul_distrib]

/-- Let `D` be admissible data for the parameters `P`, with CM field `E = D.E` over `K = P.K`, and
let `F` lie in `𝒮 D.twelveSpace`, the Heisenberg model of functions on the adelic `12 × 1` matrices
over `E`. Let `F` have integral values at the adelic vectors `finVec x = (0, α x)`, for `x` over the
finite adeles `𝔸f E` and `α` the finite idele of the Weil data of `E`. Let its theta function be
fixed by the signed translations along `π_M 𝔞₀¹²`. Let `𝔪 = (π_M)`. For every linear form `L` and
every vector `y` over `𝔸f E` there is a class `y₀` modulo `𝔪` such that the valuation of
`L (indicatorDatum 𝔪 y₀)` is at most that of `M ^ (12 f) L(F)` times the value of the vacuum at
`finVec y`. -/
lemma exists_norm_le_norm_indicatorDatum {P : Parameters} {p : ℕ} [Fact p.Prime] [PadicPlace p]
    (D : Data P) {F : 𝒮 D.twelveSpace}
    (hF_int : ∀ x : Fin 12 × Unit → 𝔸f D.E, ‖(ιₚ (F (finVec x)) : ℂ_[p])‖ ≤ 1)
    (h_periods : IsThetaFunction
      (star (algebraMap P.K D.E D.piMBar) • idealLattice D.E (Fin 12 × Unit)) (Space.entireTheta F))
    {𝔪 : Modulus D.E} (h𝔪 : 𝔪.ideal = .span {D.piM}) (L : 𝒮 D.twelveSpace →ₗ[ℂ] ℂ)
    (y : Fin 12 × Unit → 𝔸f D.E) : ∃ y₀ : Matrix (Fin 12) Unit 𝔪.ResidueRing,
    ‖(ιₚ (D.M ^ (D.f * 12) * L F * D.twelveSpace.vacElem (finVec y)) : ℂ_[p])‖ ≤
      ‖(ιₚ (L (D.indicatorDatum 𝔪 y₀)) : ℂ_[p])‖ := by
  -- Fourier inversion writes `M ^ (12 f) F = ∑ i, c i • ϱ(u i) vac` with `π̄_M u i` in `𝔞₀¹²`,
  -- where `ϱ(u i)` is the translation by the finite part of the rational vector `u i`.
  set v : ℂ := D.twelveSpace.vacElem (finVec y)
  have h_integral : algebraMap D.E (𝔸f D.E) (algebraMap P.K D.E D.piMBar) ∈ Ô D.E :=
    coe_mem_Ô (algebraMap (NumberField.RingOfIntegers P.K) _ D.piMBar)
  have h_norm : algebraMap P.K D.E D.piMBar * star (algebraMap P.K D.E D.piMBar) = D.M :=
    (New.Φ 1).injective (by simpa using D.piMBar_mul_conj)
  obtain ⟨Y, Γ, _, _, u, γ, c, hu, -, -, h_average, h_inversion⟩ :=
    D.twelveSpace.exists_fourier_coefficients h_integral (NeZero.ne D.M) h_norm h_periods
  -- The values of `c i • vac`, among them `c i * v`, are integral with those of `F`.
  have hc (i : Y) : ‖(ιₚ (c i * v) : ℂ_[p])‖ ≤ 1 :=
    D.twelveSpace.norm_mul_vacElem_le_one_of_eq_sum hF_int (h_average i) y
  -- Each translate of the vacuum is a sum of indicator data times roots of unity.
  have h_translate (i : Y) : ∃ z : Matrix (Fin 12) Unit 𝔪.ResidueRing → 𝔸f D.E,
      D.twelveSpace.ϱ (finVec (finiteImage (u i))) D.twelveSpace.vacElem =
        ∑ y₀ : Matrix (Fin 12) Unit 𝔪.ResidueRing,
          stdLattice.selfDualAddChar D.E (z y₀) • D.indicatorDatum 𝔪 y₀ := by
    refine exists_rho_finVec_vacElem_eq_sum_modDatum _ _ h𝔪 fun k ↦ ?_
    change algebraMap D.E (𝔸f D.E) (algebraMap P.K D.E D.piMBar) * finiteImage (u i) k ∈ Ô D.E
    simpa [finiteImage, mul_left_comm, Algebra.smul_def] using mem_idealLattice.1 (hu i) k
  choose z hz using h_translate
  have h_sum : D.M ^ (D.f * 12) * L F * v = ∑ x : Y × Matrix (Fin 12) Unit 𝔪.ResidueRing,
      stdLattice.selfDualAddChar D.E (z x.1 x.2) * (c x.1 * v) * L (D.indicatorDatum 𝔪 x.2) :=
    calc D.M ^ (D.f * 12) * L F * v
        = L ((D.M : ℂ) ^ card (D.Φ × Fin 12 × Unit) • F) * v := by simp
      _ = ∑ i : Y, c i * (∑ y₀ : Matrix (Fin 12) Unit 𝔪.ResidueRing,
            stdLattice.selfDualAddChar D.E (z i y₀) * L (D.indicatorDatum 𝔪 y₀)) * v := by
        simp only [← h_inversion, hz, map_sum, map_smul, smul_eq_mul, Finset.sum_mul]
      _ = _ := by
        simp only [Finset.mul_sum, Finset.sum_mul, sum_prod_type]
        exact sum_congr rfl fun i _ ↦ sum_congr rfl fun y₀ _ ↦ by ring
  obtain ⟨y₀, h_max⟩ := Finite.exists_max fun y₁ : Matrix (Fin 12) Unit 𝔪.ResidueRing ↦
    ‖(ιₚ (L (D.indicatorDatum 𝔪 y₁)) : ℂ_[p])‖
  refine ⟨y₀, ?_⟩
  rw [h_sum, map_sum]
  refine norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun x _ ↦ ?_
  grw [map_mul, map_mul, norm_mul, norm_mul, norm_map_selfDualAddChar, hc, one_mul, one_mul,
    h_max x.2]

/-- Reduction to the curve. Let `D` be admissible data for the parameters `P`, with CM field
`E = D.E = P.E D.towerExp`, whose `f = D.f` infinite places form `D.Φ`; valuations are taken at
`ιₚ : ℂ → ℂ_[p]`. Let `w` be a tight frame of length `M = D.M` with linear forms `μ_i`
(`resolutionForms`) and multiplicities `c i ≥ 3 |l|`. Suppose `val₁₂(l) ≤ r` (`LeastValLE`): some
coefficient of degree `l` in some product over twelve copies of the variables of series `H Θ` has
valuation at most `r`, where `Θ = ∏ θ(μ_i z) ^ c i` and each `H` is an integral series in the
`y(μ_i z)`, for the functions `θ` and `y` of the elliptic curve `P.cmCurve`. Then for some class
`y₀` modulo `𝔪 = (π_M)`, `π_M = D.piM`, some coefficient of degree `l` of the rescaled Taylor series
(`twelveTaylor`) of the theta function of `indicatorDatum 𝔪 y₀`, times `vacuumScale ^ 12`, has
valuation at most `r + v(M ^ (12 f) c₀)`.

The vacuum is the Gaussian times the twisted indicator of the standard lattice, on the adelic
`12 × 1` matrices over `E` (`twelveSpace`); `indicatorDatum 𝔪 y₀` is the vacuum with its part at the
places dividing `𝔪` replaced by the indicator of `y₀`. The integral vacuum `intVacuum` is the vacuum
times `vacuumScale ^ 12`, a constant that makes its values integral, and `c₀` is its value at the
adelic vector `finVec y` with zero part at infinity. -/
lemma exists_le_norm_coeff_indicatorDatum {P : Parameters} {p : ℕ} [Fact p.Prime] [PadicPlace p]
    (D : Data P) {J : Type} [Fintype J] {w : J → D.E} {c : J → ℕ}
    (hw : IsTightFrame w c D.M) {l : D.Φ × Unit →₀ ℕ} (hc : ∀ i : J, l.degree * 3 ≤ c i) {r : ℝ}
    (h_val : P.cmCurve.LeastValLE (p := p) (P.resolutionForms D.towerExp w) c 12 l r)
    {𝔪 : Modulus D.E} (h𝔪 : 𝔪.ideal = .span {D.piM}) (y : Fin 12 × Unit → 𝔸f D.E) :
    ∃ (γ : D.Φ × Fin 12 × Unit →₀ ℕ) (y₀ : Matrix (Fin 12) Unit 𝔪.ResidueRing),
      (∀ σ : D.Φ, ∑ b : Fin 12, γ (σ, b, ()) = l (σ, ())) ∧
      p ^ (-r) * ‖(ιₚ (D.M ^ (D.f * 12) * intVacuum D.twelveSpace (finVec y)) : ℂ_[p])‖ ≤
        ‖(ιₚ (P.vacuumScale D.towerExp ^ 12 * coeff γ (D.twelveTaylor (D.indicatorDatum 𝔪 y₀))) :
          ℂ_[p])‖ := by
  -- Take twelve series `∏ y(μ_i z) ^ e b i * Θ` with `|e b| ≤ |l|` whose coefficients at exponents
  -- `α b` of sum `l` have a product of valuation at most `r`. Lift them to a vector and expand it.
  obtain ⟨α, e, rfl, he_deg, h_prod⟩ := h_val.exists_monomial
  have he (b : Fin 12) (i : J) : e b i * 3 ≤ c i := by grw [le_degree, he_deg, hc]
  obtain ⟨F, h_series, hF_int, h_periods⟩ :=
    D.exists_integral_isThetaFunction_twelveTaylor_eq (p := p) hw he
  obtain ⟨y₀, h_indicator_bound⟩ := D.exists_norm_le_norm_indicatorDatum hF_int h_periods h𝔪
    (P.vacuumScale D.towerExp ^ 12 • coeff (copyExponent α) ∘ₗ D.twelveTaylor) y
  refine ⟨copyExponent α, y₀, by simp [copyExponent_apply], ?_⟩
  set a : ℂ := coeff (copyExponent α) (D.twelveTaylor F) with ha
  have h_coeff : p ^ (-r) ≤ ‖(ιₚ a : ℂ_[p])‖ := by
    rwa [ha, ← coeff_map, h_series, coeff_prod_rename_copyEmbedding, norm_prod]
  have h_vac : a * (D.M ^ (D.f * 12) * intVacuum D.twelveSpace (finVec y)) =
      D.M ^ (D.f * 12) * (P.vacuumScale D.towerExp ^ 12 * a) *
        D.twelveSpace.vacElem (finVec y) := by
    rw [intVacuum, Space.smul_apply, Fintype.card_prod, Fintype.card_fin, Fintype.card_unique]
    ring
  calc p ^ (-r) * ‖(ιₚ (D.M ^ (D.f * 12) * intVacuum D.twelveSpace (finVec y)) : ℂ_[p])‖
      ≤ ‖(ιₚ a : ℂ_[p])‖ *
        ‖(ιₚ (D.M ^ (D.f * 12) * intVacuum D.twelveSpace (finVec y)) : ℂ_[p])‖ := by gcongr
    _ = ‖(ιₚ (D.M ^ (D.f * 12) * (P.vacuumScale D.towerExp ^ 12 * a) *
          D.twelveSpace.vacElem (finVec y)) : ℂ_[p])‖ := by
      rw [← norm_mul, ← map_mul, h_vac]
    _ ≤ _ := h_indicator_bound

/-- Let `D` be admissible data for the parameters `P`, with CM field `E = D.E`, whose `f = D.f`
infinite places form `D.Φ`. For degrees `l ≤ κ + x ^ 42` at the weights `κ = D.weight`, all
conjugates of `t = M ^ (12 f) c₀ ∏ B_τ ^ 2` are at most `exp (f m b / k)` in absolute value. Here
`x`, `b` are scales and `m`, `r` ranks of `D`, with `k = D.k = r + 1 - m` and `M = D.M`. Further
`B_τ = D.lossProduct (l τ) = (l⁻ + 1) ⋯ (l⁻ + n)` with `n = D.lossFactorCount = ⌈6 b / k⌉` and
`l⁻ = (l τ - n)₊`. The number `c₀` is the value at `finVec y`, an adelic vector with zero part at
infinity, of the integral vacuum `intVacuum`: the Gaussian times the twisted indicator of the
standard lattice on the adelic `12 × 1` matrices over `E` (`twelveSpace`), multiplied by the
constant `vacuumScale ^ 12` that makes its values integral. -/
lemma norm_map_mul_intVacuum_le {P : Parameters} (D : Data P) {l : D.Φ → ℕ}
    (hl : ∀ τ : D.Φ, (l τ : ℝ) ≤ D.weight τ + D.x ^ 42)
    (y : Fin 12 × Unit → 𝔸f D.E) (σ : ℂ ≃+* ℂ) :
    ‖σ ((D.M ^ (D.f * 12) * ∏ τ : D.Φ, D.lossProduct (l τ) ^ 2 : ℕ) *
      intVacuum D.twelveSpace (finVec y))‖ ≤ exp (D.f * D.m / D.k * D.b) := by
  -- the vacuum and each loss product are bounded by exponentials; their exponents add up
  set lossBase : ℝ := 2 * D.b + D.lossFactorCount with h_lossBase
  have h_vac : ‖σ (intVacuum D.twelveSpace (finVec y))‖ ≤
      exp (12 * (P.constantBound * D.q₁ ^ 2)) := by
    have h_const : (P.vacuumBoundConst : ℝ) ≤ P.constantBound := by
      rw [Parameters.constantBound, add_assoc]
      exact le_add_of_nonneg_right (by positivity)
    grw [norm_ringEquiv_intVacuum_le, ← exp_nat_mul, h_const]
    simp
  have h_loss (τ : D.Φ) : (D.lossProduct (l τ) : ℝ) ≤ lossBase ^ D.lossFactorCount := by
    grw [lossProduct, ascFactorial_le_pow_add, tsub_le_self, cast_pow, cast_add, hl τ,
      weight_add_x_pow_le_two_mul_b]
  have h_int : ((D.M ^ (D.f * 12) * ∏ τ : D.Φ, D.lossProduct (l τ) ^ 2 : ℕ) : ℝ) ≤
      exp (12 * D.f * Real.log D.M + 2 * D.f * D.lossFactorCount * Real.log lossBase) := by
    have h_lossBase_pos : 0 < lossBase := by positivity
    calc _ ≤ (D.M : ℝ) ^ (D.f * 12) * ∏ _τ : D.Φ, (lossBase ^ D.lossFactorCount) ^ 2 := by
          push_cast
          grw [h_loss]
      _ = exp (Real.log D.M) ^ (D.f * 12) *
            (exp (Real.log lossBase) ^ D.lossFactorCount) ^ (2 * D.f) := by
          simp [exp_log, NeZero.pos D.M, h_lossBase_pos, ← pow_mul, mul_assoc]
      _ = _ := by
          simp only [← exp_nat_mul, ← exp_add]
          congr 1
          push_cast
          ring
  have h_exponent : 12 * D.f * Real.log D.M + 2 * D.f * D.lossFactorCount * Real.log lossBase +
      12 * (P.constantBound * D.q₁ ^ 2) ≤ D.f * D.m / D.k * D.b := by
    rw [h_lossBase, lossFactorCount]
    exact D.le_of_hasLogBound
  grw [map_mul, norm_mul, map_natCast, Complex.norm_natCast, h_int, h_vac, ← exp_add, h_exponent]

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.univ in
/-- Sharpness. Let `D` be admissible data for the parameters `P`, with `K = ℚ(√-d)` for the prime
`d = P.d` and `E = D.E = P.E D.towerExp` the extension of `K` by the roots of unity of order
`q₁ = D.q₁`. For degrees `l` with `κ ≤ l ≤ κ + x ^ 42` at the weights `κ = D.weight` there is a
number `t ≠ 0` with all conjugates at most `exp (f m b / k)` such that, at every prime `p` and
embedding `ιₚ : ℂ → ℂ_[p]`, for some exponent `γ` of degree `l` and some class `y₀` modulo
`𝔪 = (π_M)` the valuation of the coefficient at `γ` of `twelveTaylor (indicatorDatum 𝔪 y₀)`, times
`vacuumScale ^ 12 ∏ l!`, is at most `S_p + v(t)`.

The numbers `x`, `b` are scales and `m`, `r` ranks of `D`, `k = r + 1 - m`, and `π_M = D.piM` is an
integer of `K` of norm `D.M`. -/
theorem exists_rpow_neg_localPrimeSumTotal_le_norm_coeff {P : Parameters} (D : Data P) (l : D.Φ → ℕ)
    (hl : ∀ τ : D.Φ, (D.weight τ : ℝ) ≤ l τ ∧ l τ ≤ (D.weight τ : ℝ) + D.x ^ 42) :
    ∃ t : ℂ, t ≠ 0 ∧
      (∀ σ : ℂ ≃+* ℂ, ‖σ t‖ ≤ exp (D.f * D.m / D.k * D.b)) ∧
      ∀ 𝔪 : Modulus D.E, 𝔪.ideal = .span {D.piM} → ∀ (p : ℕ) [Fact p.Prime] [PadicPlace p],
        ∃ (γ : D.Φ × Fin 12 × Unit →₀ ℕ) (y₀ : Matrix (Fin 12) Unit 𝔪.ResidueRing),
          (∀ τ : D.Φ, ∑ b : Fin 12, γ (τ, b, ()) = l τ) ∧
          p ^ (-D.localPrimeSumTotal p) ≤ ‖ιₚ
            (P.vacuumScale D.towerExp ^ 12 / t * (∏ τ : D.Φ, (l τ)!) *
            coeff γ (D.twelveTaylor (D.indicatorDatum 𝔪 y₀)))‖ := by
  -- Take `t = M ^ (12 f) c₀ ∏ B_τ ^ 2` for a nonzero value `c₀` of the integral vacuum; combine
  -- the reduction with the bound for `val₁₂(l)`.
  obtain ⟨y, hy⟩ := exists_intVacuum_ne_zero (V := D.twelveSpace)
  -- a tight frame with multiplicities at least `6 f b` and a unit linear form at every prime
  obtain ⟨J, _, w, c, hw, hc, h_unit⟩ := D.exists_isTightFrame
  let intFactor : ℕ := D.M ^ (D.f * 12) * ∏ τ : D.Φ, D.lossProduct (l τ) ^ 2
  set c₀ : ℂ := intVacuum D.twelveSpace (finVec y)
  have ht : intFactor * c₀ ≠ 0 := by
    simp [intFactor, NeZero.ne D.M, hy, Finset.prod_eq_zero_iff, D.lossProduct_ne_zero]
  refine ⟨intFactor * c₀, ht, D.norm_map_mul_intVacuum_le (fun τ ↦ (hl τ).2) y,
    fun 𝔪 h𝔪 p hp _ ↦ ?_⟩
  obtain ⟨ν, rfl⟩ : ∃ ν : D.Φ × Unit →₀ ℕ, (fun τ ↦ ν (τ, ())) = l :=
    ⟨equivFunOnFinite.symm fun x ↦ l x.1, rfl⟩
  obtain ⟨i₀, hi₀⟩ := h_unit p
  have h_degree (i : J) : ν.degree * 3 ≤ c i := by
    have h_sum : (ν.degree : ℝ) ≤ D.f * (2 * D.b) := by
      grw [degree_eq_sum, cast_sum, (hl _).2, weight_add_x_pow_le_two_mul_b]
      simp
    rify
    linarith [hc i]
  let valLoss : ℝ := ∑ τ : D.Φ, (padicValNat p (D.lossProduct (ν (τ, ()))) : ℝ)
  let valFactorial : ℝ := ∑ τ : D.Φ, (padicValNat p (ν (τ, ()))! : ℝ)
  have h_leastVal : P.cmCurve.LeastValLE (p := p) (P.resolutionForms D.towerExp w) c 12 ν
      (D.localPrimeSumTotal p + 2 * valLoss - valFactorial) := by
    simpa only [sum_prod_type, Fintype.sum_unique, PUnit.default_eq_unit] using
      D.leastValLE_twelve ⟨fun τ ↦ (hl τ).1, fun τ ↦ (hl τ).2⟩ hw (i₀ := i₀) fun x ↦ hi₀ x.1
  obtain ⟨γ, y₀, hγ, h_coeff⟩ := D.exists_le_norm_coeff_indicatorDatum hw h_degree h_leastVal h𝔪 y
  refine ⟨γ, y₀, hγ, ?_⟩
  -- Multiply by `l!` and divide by `t`.
  set scaledVac : ℂ := D.M ^ (D.f * 12) * c₀ with h_scaledVac
  have hp_pos : (0 : ℝ) < p := mod_cast hp.out.pos
  have h_normVac : 0 < ‖(ιₚ scaledVac : ℂ_[p])‖ := by simp [h_scaledVac, NeZero.ne D.M, hy]
  have h_factor :
      intFactor * c₀ = scaledVac * (∏ τ : D.Φ, D.lossProduct (ν (τ, ())) : ℕ) ^ 2 := by
    simp [h_scaledVac, intFactor, Finset.prod_pow, mul_right_comm]
  have h_normLoss : ‖(ιₚ (∏ τ : D.Φ, D.lossProduct (ν (τ, ())) : ℕ) : ℂ_[p])‖ = p ^ (-valLoss) :=
    norm_natCast_prod_eq_rpow_neg_sum fun τ ↦ D.lossProduct_ne_zero _
  have h_normFactorial : ‖(ιₚ (∏ τ : D.Φ, (ν (τ, ()))! : ℕ) : ℂ_[p])‖ = p ^ (-valFactorial) :=
    norm_natCast_prod_eq_rpow_neg_sum fun τ ↦ factorial_ne_zero _
  calc (p : ℝ) ^ (-D.localPrimeSumTotal p)
      = (‖(ιₚ scaledVac : ℂ_[p])‖ * (p ^ (-valLoss)) ^ 2)⁻¹ * p ^ (-valFactorial) *
          (p ^ (-(D.localPrimeSumTotal p + 2 * valLoss - valFactorial)) *
            ‖(ιₚ scaledVac : ℂ_[p])‖) := by
        simp only [neg_sub, rpow_sub hp_pos, rpow_add hp_pos, rpow_neg hp_pos.le, two_mul]
        field
    _ ≤ (‖(ιₚ scaledVac : ℂ_[p])‖ * (p ^ (-valLoss)) ^ 2)⁻¹ * p ^ (-valFactorial) *
          ‖ιₚ (P.vacuumScale D.towerExp ^ 12 * coeff γ
            (D.twelveTaylor (D.indicatorDatum 𝔪 y₀)))‖ := by
        gcongr
    _ = _ := by
        rw [← h_normLoss, ← h_normFactorial, h_factor]
        simp only [map_mul, map_div₀, map_pow, norm_mul, norm_div, norm_pow]
        ring

end Data

end New
