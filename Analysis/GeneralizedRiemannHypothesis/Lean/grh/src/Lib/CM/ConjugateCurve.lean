import Lib.CM.GoodReduction

/-!
# Galois conjugates of CM curves: conjugate sections, isogenies and translates of θ

Let `σ` be a field automorphism of `ℂ`, and let `C`, `C'` be CM data (`New.CMLattice`) with
`C'.a₁ = σ C.a₁`, so that their cubics y² + a₁xy = x³ + x are conjugate under `σ`. Write `θ`, `θ'`
for their theta functions, and `New.taylorVia σ f` for the Taylor series of `f` at 0 with `σ`
applied to its coefficients. The bare letter `σ` is the automorphism, while `C.σ` is the sigma
function of the lattice of `C`. For `σ ∈ Aut(ℂ/K)` with `K = ℚ(√-d)` (`quadInt d` is the image of
`𝓞_K` in `ℂ`, fixed by `σ`), a conjugate CM datum exists, and conjugation extends to isogenies and
to translates of `θ`; this is a step towards `New.CMLattice.complex_multiplication_theta`.

## Main definitions and results

* `New.thetaQuotient`: the quotient `θ' / σ θ` of power series, by which the theta functions differ.
* `New.taylorAtZero_monomialSection`, `New.exists_conjugate_section`: monomial sections, and hence
  all sections `f` of degree `m` of `C`, have conjugates with Taylor series `(θ' / σ θ) ^ m * σ f`;
  the second lemma transports points as well.
* `New.CMLattice.exists_galConjugate_of_g₂_g₃`, `New.CMLattice.galConjugate`: a lattice with the
  invariants `σ g₂`, `σ g₃` carries a CM datum with the number `σ a₁`, and one such datum is chosen.
* `New.CMLattice.thetaQuotient_eq_one`, `New.CMLattice.taylorAtZero_theta_eq_taylorVia`: for a CM
  datum `D` with invariant `σ a₁`, the Taylor series of the theta function is the conjugate of that
  of `θ`.
* `New.CMLattice.exists_taylorVia_twistedTranslate_theta`: when the lattice of `C` is `Ω 𝓞_K` and
  `S` is a finite subset of `K`, there is a period `v` of `D` such that, for all `s ∈ S`, the Taylor
  series of the translate by `s v` of the theta function of `D` is the conjugate of that of the
  translate of `θ` by `s Ω`.

Notions from other files:
* `New.CMLattice.θ`: The twisted translate (`twistedTranslate 1 u f` is
  `z ↦ exp(−π(zū + |u|²/2)/area Λ) f(z + u)`) of the sigma function `C.σ` by the point t of order
  two, normalised to 1 at 0; it vanishes exactly on t + Λ.
* `New.CMLattice.translatedX`, `New.CMLattice.translatedY`: The coordinates x(z) = ℘(z + t) − ℘(t)
  and y(z) = ½(℘′(z + t) − a₁x(z)) of the curve.
* `New.CMLattice.sections`: The sections of degree m: theta functions for the lattice Λ with
  hermitian form mH and multiplier χ^m, for the hermitian form H and multiplier χ of `θ`.
* `PeriodPair.IsIsogeny`: L.IsIsogeny M a N says that a maps the periods of L to those of M and that
  a·ā·area(L) = N·area(M).
* `New.CMLattice.monomialSection`: For j = (a, b, c), the section θ^a·(C.σ²)^b·G^c of degree
  a + 2b + 3c, with C.σ the sigma function and G = `New.CMLattice.translatedYThetaCube`.

## Relation to the literature

Part of a known result: Main theorem of complex multiplication for elliptic curves, soft form. See
`Lib.CM.ChowlaSelberg`. No reciprocity law is used: the conjugate lattice comes from uniformisation,
and points are matched by transporting sections.
-/

/-!
## Transport of sections and points to a conjugate curve

The series of `x` and `y` are conjugate because they solve the same differential system.
-/

namespace New

open PowerSeries CMLattice PeriodPair Submodule

variable {d d' : ℕ}

/-- The power series θ′/σθ: the Taylor series of the theta function of C' times the inverse of
the σ-conjugate of that of C. -/
noncomputable def thetaQuotient (C : CMLattice d) (σ : ℂ ≃+* ℂ) (C' : CMLattice d') : ℂ⟦X⟧ :=
  taylorAtZero C'.θ * (taylorVia σ C.θ)⁻¹

variable {C : CMLattice d} (σ : ℂ ≃+* ℂ) {C' : CMLattice d'}

/-- For CM lattices `C`, `C'` and a ring automorphism `σ` of `ℂ` with `C'.a₁ = σ C.a₁`, the Taylor
series at 0 of `C'.translatedX` and `C'.translatedY` are obtained from those of `C` by applying `σ`
to the coefficients. Here `translatedX` is x(z) = ℘(z + t) − ℘(t) and `translatedY` is
y(z) = ½(℘′(z + t) − a₁x(z)), with ℘ the Weierstrass function of the lattice and `t` its point of
order two. -/
lemma map_taylorAtZero_translatedX_and_translatedY (ha₁ : C'.a₁ = σ C.a₁) :
    (taylorAtZero C.translatedX).map ↑σ = taylorAtZero C'.translatedX ∧
    (taylorAtZero C.translatedY).map ↑σ = taylorAtZero C'.translatedY := by
  -- Both pairs vanish at `0` and solve the same system `x' = 2y + a₁x`, `y' = 1 + 3x² - a₁y`, so
  -- they agree. For the induction on the coefficient allow an arbitrary factor `a`: by the product
  -- rule the derivatives of `a x`, `a y` are combinations of 1, `x`, `y`, `x²` with such factors.
  have h_coeff (n : ℕ) (a : ℂ⟦X⟧) :
      coeff n (a * taylorVia ↑σ C.translatedX) = coeff n (a * taylorVia (.id ℂ) C'.translatedX) ∧
      coeff n (a * taylorVia ↑σ C.translatedY) =
        coeff n (a * taylorVia (.id ℂ) C'.translatedY) := by
    induction n generalizing a with
    | zero => simp [translatedX]
    | succ n ih =>
      have h_succ (f : ℂ⟦X⟧) : coeff (n + 1) f = coeff n (d⁄dX f) / (n + 1) :=
        eq_div_of_mul_eq (by norm_cast) (coeff_derivative f n).symm
      have h_wp {e : ℕ} (B : CMLattice e) (ι : ℂ →+* ℂ) :
          d⁄dX (a * taylorVia ι B.translatedX) = 2 * a * taylorVia ι B.translatedY +
            (d⁄dX a + a * PowerSeries.C (ι B.a₁)) * taylorVia ι B.translatedX := by
        simp only [Derivation.leibniz, derivative_taylorVia_translatedX, smul_eq_mul]
        ring
      have h_y {e : ℕ} (B : CMLattice e) (ι : ℂ →+* ℂ) :
          d⁄dX (a * taylorVia ι B.translatedY) = a + 3 * a * taylorVia ι B.translatedX ^ 2 +
            (d⁄dX a - a * PowerSeries.C (ι B.a₁)) * taylorVia ι B.translatedY := by
        simp only [Derivation.leibniz, derivative_taylorVia_translatedY, smul_eq_mul]
        ring
      -- The induction hypothesis, used once for each factor, also covers `x²`.
      have h_sq (b : ℂ⟦X⟧) : coeff n (b * taylorVia ↑σ C.translatedX ^ 2) =
          coeff n (b * taylorVia (.id ℂ) C'.translatedX ^ 2) := by
        rw [sq, ← mul_assoc, (ih _).1, mul_right_comm, (ih _).1, sq, ← mul_assoc]
      have hσ_a₁ : (σ : ℂ →+* ℂ) C.a₁ = RingHom.id ℂ C'.a₁ := ha₁.symm
      constructor
      · rw [h_succ, h_succ, h_wp, h_wp, map_add, map_add, hσ_a₁, (ih _).2, (ih _).1]
      · rw [h_succ, h_succ, h_y, h_y, map_add, map_add, map_add, map_add, hσ_a₁, h_sq, (ih _).2]
  simpa [PowerSeries.ext_iff, forall_and] using fun n ↦ h_coeff n 1

/-- Let the invariant `a₁` of the CM datum `C'` be the conjugate of that of `C` by the automorphism
`σ` of `ℂ`. For exponents `j = (a, b, c)`, the Taylor series of the monomial section
`θ' ^ a * (C'.σ ^ 2) ^ b * C'.translatedYThetaCube ^ c` of `C'` is the conjugate of the series of
that of `C` times `(θ' / σ θ) ^ (a + 2 b + 3 c)`, where `θ' / σ θ` is `New.thetaQuotient`. -/
lemma taylorAtZero_monomialSection (ha₁ : C'.a₁ = σ C.a₁) (j : ℕ × ℕ × ℕ) :
    taylorAtZero (C'.monomialSection j) =
      thetaQuotient C σ C' ^ monomialDeg j * taylorVia σ (C.monomialSection j) := by
  obtain ⟨hx, hy⟩ := map_taylorAtZero_translatedX_and_translatedY σ ha₁
  have hθ : thetaQuotient C σ C' * taylorVia σ C.θ = taylorAtZero C'.θ := by
    simp [thetaQuotient, mul_assoc, PowerSeries.inv_mul_cancel]
  simp only [taylorVia] at hθ ⊢
  rw [taylorAtZero_monomialSection_eq, taylorAtZero_monomialSection_eq, map_mul, map_mul, map_pow,
    map_pow, map_pow, hx, hy, ← hθ, mul_pow, mul_assoc]

/-- The case `θ' z = 0` of `exists_conjugate_point`: if `z` is congruent to the point `t` of `C'`,
the values at `z` of `θ'`, `C'.σ ^ 2` and of the entire function `translatedYThetaCube` = `yθ'³` are
`μ`, `μ²`, `μ³` times the `σ`-conjugates of those of `C` at its point `t`, for some `μ ≠ 0`. -/
lemma exists_conjugate_factor_of_mem {z : ℂ} (hz : z + C'.t ∈ C'.Λ) :
    ∃ μ ≠ (0 : ℂ),
      C'.θ z = μ * σ (C.θ C.t) ∧
      C'.σ z ^ 2 = μ ^ 2 * σ (C.σ C.t ^ 2) ∧
      C'.translatedYThetaCube z = μ ^ 3 * σ (C.translatedYThetaCube C.t) := by
  -- `C'.θ` vanishes at `z` and `C.θ` at `C.t`, where the curve equation
  -- `translatedYThetaCube_sq_add` reads `translatedYThetaCube² = C.σ⁶ ≠ 0`, and likewise for `C'`.
  have hθz : C'.θ z = 0 := by simpa
  have hθt : C.θ C.t = 0 := by simp [C.two_t_mem]
  have h_z : C'.translatedYThetaCube z ^ 2 = C'.σ z ^ 6 := by
    simpa [hθz] using C'.translatedYThetaCube_sq_add z
  have h_t : σ (C.translatedYThetaCube C.t) ^ 2 = σ (C.σ C.t) ^ 6 := by
    simpa [hθt] using congrArg σ (C.translatedYThetaCube_sq_add C.t)
  have hσz : C'.σ z ≠ 0 := by grind [sigma_eq_zero_iff, t_notMem, add_mem_cancel_left]
  have hσt : σ (C.σ C.t) ≠ 0 := by simp [sigma_eq_zero_iff, C.t_notMem]
  have hGt : σ (C.translatedYThetaCube C.t) ≠ 0 := fun h ↦ hσt (by simpa [h] using h_t.symm)
  -- With `r`, `q` the ratios of the values of `translatedYThetaCube` and of the sigma functions,
  -- `r² = q⁶`; so `μ = r / q²` has `μ² = q²` and `μ³ = r`.
  set r : ℂ := C'.translatedYThetaCube z / σ (C.translatedYThetaCube C.t) with hr
  set q : ℂ := C'.σ z / σ (C.σ C.t) with hq
  have h_ratio : r ^ 2 = q ^ 6 := by rw [div_pow, div_pow, h_z, h_t]
  have hμ₂ : (r / q ^ 2) ^ 2 = q ^ 2 := by simp [div_pow, h_ratio, field]
  have hμ₃ : (r / q ^ 2) ^ 3 = r := by simp [pow_succ _ 2, hμ₂, field]
  have hq₀ : q ≠ 0 := div_ne_zero hσz hσt
  refine ⟨r / q ^ 2, fun h ↦ hq₀ (by simpa [h] using hμ₂.symm),
    by simp [hθz, hθt], ?_, by rw [hμ₃, hr, div_mul_cancel₀ _ hGt]⟩
  rw [hμ₂, map_pow, ← mul_pow, hq, div_mul_cancel₀ _ hσt]

/-- The case `θ' z ≠ 0` of `exists_conjugate_point`, where `θ'` is the theta function `C'.θ`: let
`σ` be an automorphism of `ℂ`, let `C`, `C'` be CM lattices with `C'.a₁ = σ C.a₁`, and let `z`
satisfy `z + C'.t ∉ C'.Λ`, i.e. `z` is not congruent to the point `t` of order two of `C'`. Then for
some `u` and some `μ ≠ 0`, the values at `z` of `C'.θ`, `C'.σ ^ 2` (the sigma function squared) and
`C'.translatedYThetaCube` (equal to `yθ³` off `t + Λ`, with `y` = `translatedY`) are `μ`, `μ²`, `μ³`
times the `σ`-images of the corresponding values for `C` at `u`. -/
lemma exists_conjugate_point_of_notMem (ha₁ : C'.a₁ = σ C.a₁) {z : ℂ} (hz : z + C'.t ∉ C'.Λ) :
    ∃ u : ℂ, ∃ μ ≠ (0 : ℂ),
      C'.θ z = μ * σ (C.θ u) ∧
      C'.σ z ^ 2 = μ ^ 2 * σ (C.σ u ^ 2) ∧
      C'.translatedYThetaCube z = μ ^ 3 * σ (C.translatedYThetaCube u) := by
  -- Pull the point `(x, y)(z)` of the cubic of `C'` back by `σ`; it lies on the cubic of `C`.
  -- In Weierstrass coordinates `(℘, ℘')` it is the image of some `w`; take `u = w - C.t`.
  obtain ⟨w, hw, hwx, hwy⟩ :
      ∃ w ∉ C.Λ,
        ℘[C.periodPair] w = σ.symm (C'.translatedX z) + ℘[C.periodPair] C.t ∧
        ℘'[C.periodPair] w = σ.symm (℘'[C'.periodPair] (z + C'.t)) := by
    apply C.exists_weierstrassP_eq_of_cubic
    have h_curve : σ.symm (C'.translatedY z) ^ 2 +
        C.a₁ * σ.symm (C'.translatedX z) * σ.symm (C'.translatedY z) =
          σ.symm (C'.translatedX z) ^ 3 + σ.symm (C'.translatedX z) := by
      simpa [ha₁] using congrArg σ.symm (C'.weierstrass_equation hz)
    simp only [translatedY, ha₁, map_div₀, map_sub, map_mul, map_ofNat,
      RingEquiv.symm_apply_apply] at h_curve
    -- Express `g₂` and `g₃` through `a₁` and `℘(t)`.
    grind [CMLattice, g₂_eq, g₃_eq]
  -- By `sigma_sq_eq_and_translatedYThetaCube_eq`, `C.σ ^ 2 = xθ²` and `translatedYThetaCube = yθ³`
  -- at `u`, likewise for `C'` at `z`, and `x`, `y` are conjugate there.
  have hθz : C'.θ z ≠ 0 := by simpa using hz
  have hθu : σ (C.θ (w - C.t)) ≠ 0 := by simpa using hw
  have hx : σ (C.translatedX (w - C.t)) = C'.translatedX z := by simp [translatedX, hwx]
  have hy : σ (C.translatedY (w - C.t)) = C'.translatedY z := by
    simp [translatedY, hx, hwy, ha₁, map_ofNat]
  obtain ⟨hσ_z, hG_z⟩ := C'.sigma_sq_eq_and_translatedYThetaCube_eq z hz
  obtain ⟨hσ_u, hG_u⟩ := C.sigma_sq_eq_and_translatedYThetaCube_eq (w - C.t) (by simpa using hw)
  exact ⟨w - C.t, C'.θ z / σ (C.θ (w - C.t)), div_ne_zero hθz hθu, (div_mul_cancel₀ _ hθu).symm,
    by simp [hσ_z, hσ_u, hx, field], by simp [hG_z, hG_u, hy, field]⟩

/-- Let the invariant `a₁` of the CM datum `C'` be the `σ`-conjugate of that of `C`. A point `z` of
`C'` has a matching point `u` of `C`: the values at `z` of the generators `θ'` (the theta function
of `C'`), `C'.σ ^ 2` (the square of the sigma function of the lattice) and `C'.translatedYThetaCube`
(the entire function `yθ'³`) are the conjugates of the values at `u` of those of `C`, up to factors
`μ`, `μ²`, `μ³` with `μ ≠ 0`. If `θ'` vanishes at `z`, then `u` is the point `t` of order two
of `C`. -/
lemma exists_conjugate_point (ha₁ : C'.a₁ = σ C.a₁) (z : ℂ) :
    ∃ u : ℂ, ∃ μ ≠ (0 : ℂ),
      (C'.θ z = 0 → u = C.t) ∧
      C'.θ z = μ * σ (C.θ u) ∧
      C'.σ z ^ 2 = μ ^ 2 * σ (C.σ u ^ 2) ∧
      C'.translatedYThetaCube z = μ ^ 3 * σ (C.translatedYThetaCube u) := by
  by_cases hz : z + C'.t ∈ C'.Λ
  · obtain ⟨μ, hμ, h_values⟩ := exists_conjugate_factor_of_mem (C := C) σ hz
    exact ⟨C.t, μ, hμ, fun _ ↦ rfl, h_values⟩
  · obtain ⟨u, μ, hμ, h_values⟩ := exists_conjugate_point_of_notMem σ ha₁ hz
    exact ⟨u, μ, hμ, fun hθ ↦ absurd (C'.theta_eq_zero_iff.1 hθ) hz, h_values⟩

/-- If the invariant `a₁` of `C'` is the `σ`-conjugate of that of `C`, a point `z` of `C'` has a
matching point `u` of `C` and a factor `μ ≠ 0`: every section `f` of degree `m` of `C` (a theta
function for its lattice) has a conjugate section `g` of `C'`, with Taylor series
`(θ' / σ θ) ^ m * σ f`, where `θ' / σ θ` is `New.thetaQuotient`, and value `g z = μ ^ m * σ (f u)`.
If `θ'` vanishes at `z`, then `u` is the point `t` of order two of `C`. -/
lemma exists_conjugate_section (ha₁ : C'.a₁ = σ C.a₁) (z : ℂ) :
    ∃ u : ℂ, ∃ μ ≠ (0 : ℂ),
      (C'.θ z = 0 → u = C.t) ∧
      ∀ {m : ℕ} {f : ℂ → ℂ}, f ∈ C.sections m → ∃ g ∈ C'.sections m,
        taylorAtZero g = thetaQuotient C σ C' ^ m * taylorVia σ f ∧ g z = μ ^ m * σ (f u) := by
  obtain ⟨u, μ, hμ, hu, hθ, hσ, hG⟩ := exists_conjugate_point σ ha₁ z
  refine ⟨u, μ, hμ, hu, fun {m f} hf ↦ ?_⟩
  -- Sections are spanned by monomials; differentiability is carried along for `taylorAtZero`.
  suffices h_both : Differentiable ℂ f ∧ ∃ g ∈ C'.sections m,
      taylorAtZero g = thetaQuotient C σ C' ^ m * taylorVia σ f ∧ g z = μ ^ m * σ (f u) from
    h_both.2
  replace hf := C.sections_le_span_monomialSection m hf
  induction hf using span_induction with
  | mem f hf =>
    obtain ⟨j, ⟨-, rfl⟩, rfl⟩ := hf
    refine ⟨C.differentiable_monomialSection j, C'.monomialSection j, C'.monomialSection_mem j,
      taylorAtZero_monomialSection σ ha₁ j, ?_⟩
    simp [monomialSection, hθ, hσ, hG, pow_add, mul_pow, pow_mul', field]
  | zero => exact ⟨by fun_prop, 0, by simp, by simp [Pi.zero_def, taylorVia]⟩
  | add f₁ f₂ _ _ ih₁ ih₂ =>
    obtain ⟨hf₁_diff, g₁, hg₁, hg₁_ser, hg₁_val⟩ := ih₁
    obtain ⟨hf₂_diff, g₂, hg₂, hg₂_ser, hg₂_val⟩ := ih₂
    have hg₁_diff : Differentiable ℂ g₁ := hg₁.1
    have hg₂_diff : Differentiable ℂ g₂ := hg₂.1
    refine ⟨by fun_prop, g₁ + g₂, add_mem hg₁ hg₂, ?_, by simp [mul_add, hg₁_val, hg₂_val]⟩
    simp (disch := fun_prop) [Pi.add_def, taylorVia, mul_add, hg₁_ser, hg₂_ser]
  | smul c f _ ih =>
    obtain ⟨hf_diff, g, hg, hg_ser, hg_val⟩ := ih
    have hg_diff : Differentiable ℂ g := hg.1
    refine ⟨by fun_prop, σ c • g, smul_mem _ _ hg, ?_, by simp [mul_left_comm, hg_val]⟩
    simp (disch := fun_prop) [Pi.smul_def, taylorVia, mul_left_comm, hg_ser]

end New

section ConjugateCurve

namespace New

open CMLattice PowerSeries

variable {d d' : ℕ} {C D : CMLattice d} {a : ℂ} [PrimeSevenModEight d] (σ : Gal(ℂ/QuadField d))

/-! ### Conjugate isogenies -/

/-- Let `σ` be an automorphism of `ℂ` over `ℚ(√-d)`, with `d` a prime `≡ 7 (mod 8)`. Let `a` be an
isogeny from `C` to `D` of degree `N`, that is `a Λ_C ⊆ Λ_D` and `|a|² area C = N area D`. Let `C'`,
`D'` be CM data for any `d'` whose invariants `a₁` (square roots of `12 ℘(t)`) are the
`σ`-conjugates of those of `C`, `D`. There are sections `A`, `B` of `C'` (theta functions for its
lattice) of degrees `2 N`, `N`, corresponding to the sections `D.σ (a * z) ^ 2` and `D.θ (a * z)` of
`C`. They have the values 0 and 1 at 0. `A` vanishes at the point `t` of order two of `C'` only if
`a` takes the point `t` of `C` to a period of `D`. The series of `B` is `(θ' / σ θ) ^ N` (see
`New.thetaQuotient`) times the conjugate series of `D.θ (a * z)`. And `A / B ^ 2` is
`D'.σ ^ 2 / D'.θ ^ 2` taken at `σ a * z`. -/
lemma exists_conj_isogeny_sections {C' D' : CMLattice d'} {N : ℕ} (hC : C'.a₁ = σ C.a₁)
    (hD : D'.a₁ = σ D.a₁) (ha : C.IsIsogeny D.periodPair a N) :
    ∃ A ∈ C'.sections (2 * N), ∃ B ∈ C'.sections N,
      A 0 = 0 ∧
      B 0 = 1 ∧
      (A C'.t = 0 → a * C.t ∈ D.Λ) ∧
      taylorAtZero B = thetaQuotient C σ C' ^ N * taylorVia σ (fun z : ℂ ↦ D.θ (a * z)) ∧
      ∀ z : ℂ, A z * D'.θ (σ a * z) ^ 2 = D'.σ (σ a * z) ^ 2 * B z ^ 2 := by
  -- `transport` sends a section `f` of degree `m` of `C` to a section `g` of `C'` with series
  -- `thetaQuotient C σ C' ^ m * σ f` and value `g C'.t = μ ^ m * σ (f u)`; `hu` gives `u = C.t`.
  obtain ⟨u, μ, hμ, hu, transport⟩ := exists_conjugate_section σ hC C'.t
  obtain rfl : u = C.t := hu (C'.theta_eq_zero_iff.2 C'.two_t_mem)
  have h_transport (j : ℕ × ℕ × ℕ) : ∃ g ∈ C'.sections (monomialDeg j * N),
      taylorAtZero g = thetaQuotient C σ C' ^ (monomialDeg j * N) *
        taylorVia σ (fun z ↦ D.monomialSection j (a * z)) ∧
      g C'.t = μ ^ (monomialDeg j * N) * σ (D.monomialSection j (a * C.t)) :=
    transport (C.comp_mul_mem_sections ha (D.monomialSection_mem j))
  obtain ⟨A, hA, hA_ser, hA_t⟩ := h_transport (0, 1, 0)
  obtain ⟨B, hB, hB_ser, -⟩ := h_transport (1, 0, 0)
  have hA_diff : Differentiable ℂ A := hA.1
  have hB_diff : Differentiable ℂ B := hB.1
  -- Both sides are entire; in their Taylor series the powers of `thetaQuotient` agree.
  have h_fun : (fun z ↦ A z * D'.monomialSection (1, 0, 0) (σ a * z) ^ 2) =
      fun z ↦ D'.monomialSection (0, 1, 0) (σ a * z) * B z ^ 2 := by
    refine eq_of_taylorAtZero_eq (by fun_prop) (by fun_prop) ?_
    simp (disch := fun_prop) [hA_ser, hB_ser, taylorAtZero_monomialSection σ hD, ← rescale_map,
      taylorVia, monomialDeg]
    ring
  refine ⟨A, hA, B, by simpa [monomialDeg] using hB, ?_, ?_, fun h_zero ↦ ?_, ?_, fun z ↦ ?_⟩
  · -- The value at 0 is the constant coefficient.
    simpa [thetaQuotient, monomialSection] using congrArg constantCoeff hA_ser
  · simpa [thetaQuotient, monomialSection] using congrArg constantCoeff hB_ser
  · -- Here `0 = μ ^ (2 * N) * σ (D.σ (a * C.t) ^ 2)`, and `D.σ` vanishes only at periods.
    simpa [h_zero, hμ, monomialSection] using hA_t
  · simpa [monomialSection, monomialDeg] using hB_ser
  · simpa [monomialSection] using congrFun h_fun z

/-- Let `a` be an isogeny of degree `N` from `C` to `D` (it maps periods to periods and
`a * conj a * area C = N * area D`), and let the invariants `a₁` of `C'`, `D'` be the
`σ`-conjugates of those of `C`, `D`, for `σ` an automorphism of `ℂ` over `ℚ(√-d)`. Then `σ a`
takes periods of `C'` to periods of `D'`. -/
lemma conj_isogeny_mul_mem_lattice {C' D' : CMLattice d'} {N : ℕ} (hC : C'.a₁ = σ C.a₁)
    (hD : D'.a₁ = σ D.a₁) (ha : C.IsIsogeny D.periodPair a N) {l : ℂ} (hl : l ∈ C'.Λ) :
    σ a * l ∈ D'.Λ := by
  -- `hA_per`, `hB_per` are the quasi-periodicity of the sections `A`, `B` of `C'`.
  obtain ⟨A, ⟨-, hA_per⟩, B, ⟨-, hB_per⟩, hA_zero, hB_zero, -, -, h_quot⟩ :=
    exists_conj_isogeny_sections σ hC hD ha
  -- On the lattice of `C'`, `A` vanishes and `B` does not, so `D'.σ (σ a * l) = 0`.
  have hA_l : A l = 0 := by simpa [hA_zero] using hA_per l hl 0
  have hB_l : B l ≠ 0 := by
    rw [← zero_add l, hB_per l hl 0]
    simp [hB_zero, C'.isAppellHumbert_multiplier.ne_zero hl]
  exact sigma_eq_zero_iff.1 (by simpa [hA_l, hB_l] using h_quot l)

/-- Let `a` be an isogeny of degree `N` from `C` to `D`, and let the invariants `a₁` of `C'`, `D'`
be the `σ`-conjugates of those of `C`, `D`. If `σ a` takes the point `t` of order two of `C'` to a
period of `D'`, then `a` takes the point `t` of `C` to a period of `D`. -/
lemma mul_t_mem_of_conj_isogeny_mul_t_mem {C' D' : CMLattice d'} {N : ℕ}
    (hC : C'.a₁ = σ C.a₁) (hD : D'.a₁ = σ D.a₁) (ha : C.IsIsogeny D.periodPair a N)
    (ht : σ a * C'.t ∈ D'.Λ) :
    a * C.t ∈ D.Λ := by
  obtain ⟨A, -, B, -, -, -, hA_t, -, h_quot⟩ := exists_conj_isogeny_sections σ hC hD ha
  -- At the period `σ a * C'.t` the function `D'.σ` vanishes and `D'.θ` does not.
  have hθ_ne : D'.θ (σ a * C'.t) ≠ 0 := by
    simp [theta_eq_zero_iff, add_mem_cancel_left ht, D'.t_notMem]
  have hA_zero : A C'.t = 0 := by simpa [hθ_ne, sigma_eq_zero_iff.2 ht] using h_quot C'.t
  exact hA_t hA_zero

omit [PrimeSevenModEight d] in
/-- An automorphism of `ℂ` over `K` fixes the elements of `quadInt d`, the image of `𝓞_K` in `ℂ`. -/
@[simp, grind]
lemma map_eq_self_of_mem_quadInt (ha : a ∈ quadInt d) : σ a = a := by
  obtain ⟨x, rfl⟩ := ha
  exact σ.commutes (x : QuadField d)

/-! ### The conjugate CM datum -/

namespace CMLattice

variable (C)

/-- Let `d` be a prime `≡ 7 (mod 8)` and `K = ℚ(√-d)`. A CM datum is a lattice stable under `𝓞 K`
with a point `t` of order two such that neither `ω t` nor `ω̄ t` lies in it (`ω = (1 + √-d)/2`),
scaled so `℘''(t) = 2`, and with a square root `a₁` of `12 ℘(t)`. For a CM datum `C` and an
automorphism `σ` of `ℂ` over `K`, every lattice `L` whose invariants are `σ C.g₂` and `σ C.g₃`
carries a CM datum whose `a₁` is `σ C.a₁`. -/
lemma exists_galConjugate_of_g₂_g₃ (L : PeriodPair) (hg₂ : L.g₂ = σ C.g₂) (hg₃ : L.g₃ = σ C.g₃) :
    ∃ C' : CMLattice d, C'.periodPair = L ∧ C'.a₁ = σ C.a₁ := by
  -- Take the point `t` of order two of `L` at which `℘` has the conjugate value.
  obtain ⟨t, ht, ht_wp, ht_wp'⟩ : ∃ t ∉ L.lattice,
      L.weierstrassP t = σ (C.weierstrassP C.t) ∧ L.derivWeierstrassP t = 0 :=
    L.exists_weierstrassP_eq_of_cubic _ 0 (by grind [g₃_eq, map_ofNat])
  -- For `d = 0` no complex multiplication is asked, so this is already a datum `D : CMLattice 0`.
  have h_g₂ : L.g₂ = 12 * L.weierstrassP t ^ 2 - 4 := by simp [hg₂, g₂_eq, ht_wp, map_ofNat]
  have h_two : t + t ∈ L.lattice := by simpa [← derivWeierstrassP_eq_zero_iff, ht] using ht_wp'
  have h_sq : σ C.a₁ ^ 2 = 12 * L.weierstrassP t := by simp [← map_pow, a₁_sq, ht_wp, map_ofNat]
  let D : CMLattice 0 :=
    { periodPair := L, t, a₁ := σ C.a₁, g₂_eq := h_g₂, two_t_mem := h_two, t_notMem := ht
      a₁_sq := h_sq
      mul_mem_of_quadInt := fun {h₀} ↦ absurd rfl h₀.out
      quadGen_mul_t_notMem := fun {h₀} ↦ absurd rfl h₀.out }
  -- Conjugating the endomorphisms `a ∈ quadInt d` of `C`, which `σ` fixes, supplies the rest.
  have h_end {a : ℂ} (ha : a ∈ quadInt d) :
      (∀ l ∈ L.lattice, a * l ∈ L.lattice) ∧ (a * t ∈ L.lattice → a * C.t ∈ C.Λ) := by
    obtain ⟨N, hN⟩ := exists_isIsogeny_of_mul_mem_lattice (C.mul_mem_of_quadInt ha)
    have h_per (l : ℂ) (hl : l ∈ D.Λ) : σ a * l ∈ D.Λ :=
      conj_isogeny_mul_mem_lattice σ rfl rfl hN hl
    have h_t : σ a * D.t ∈ D.Λ → a * C.t ∈ C.Λ :=
      mul_t_mem_of_conj_isogeny_mul_t_mem σ rfl rfl hN
    rw [map_eq_self_of_mem_quadInt σ ha] at h_per h_t
    exact ⟨h_per, h_t⟩
  obtain ⟨hω, hω_conj⟩ := C.quadGen_mul_t_notMem
  obtain ⟨-, h_gen⟩ := h_end quadGen_mem_quadInt
  obtain ⟨-, h_gen_conj⟩ := h_end (conj_mem_quadInt quadGen_mem_quadInt)
  exact ⟨{ D with
    mul_mem_of_quadInt := fun ha ↦ (h_end ha).1
    quadGen_mul_t_notMem := ⟨mt h_gen hω, mt h_gen_conj hω_conj⟩ }, rfl, rfl⟩

/-- For a CM datum `C` with `d` a prime `≡ 7 (mod 8)` and an automorphism `σ` of `ℂ` over
`K = ℚ(√-d)` there is a CM datum whose number `a₁` is the conjugate `σ C.a₁` of that of `C`.
The proof takes the lattice with the invariants `σ g₂`, `σ g₃`. -/
lemma exists_galConjugate : ∃ C' : CMLattice d, C'.a₁ = σ C.a₁ := by
  obtain ⟨L, hg₂, hg₃⟩ : ∃ L : PeriodPair, L.g₂ = σ C.g₂ ∧ L.g₃ = σ C.g₃ :=
    exists_lattice_of_g₂_g₃
      (by simpa [map_ofNat] using σ.injective.ne (weierstrass_disc_ne_zero C.periodPair))
  obtain ⟨C', -, h_a₁⟩ := C.exists_galConjugate_of_g₂_g₃ σ L hg₂ hg₃
  exact ⟨C', h_a₁⟩

/-- The conjugate curve: a chosen CM lattice whose number `a₁` is `σ C.a₁`, see
`New.CMLattice.galConjugate_a₁`. -/
noncomputable def galConjugate : CMLattice d := (C.exists_galConjugate σ).choose

/-- For `d` a prime `≡ 7 mod 8` and `σ` an automorphism of `ℂ` fixing `QuadField d = ℚ(√-d)`, the
Galois conjugate `C.galConjugate σ` of a CM lattice `C` has number `a₁` equal to `σ C.a₁`. Here `a₁`
is the chosen square root of `12 ℘(t)`, for `t` the 2-torsion point of `C`. -/
lemma galConjugate_a₁ : (C.galConjugate σ).a₁ = σ C.a₁ := (C.exists_galConjugate σ).choose_spec

end CMLattice

/-! ### The theta function of a conjugate datum -/

omit [PrimeSevenModEight d] in
/-- A section is fixed by its zeros up to a constant. Let `a ≠ 0` and let `g(z) = (T_u θ)(a z)`,
with `θ` and the twisted translation `T_u` formed for a CM datum `E`, be a section of degree `m` of
`C`. A section `f` of degree `m` of `C` that vanishes at the zeros of `g` is a constant multiple of
`g`. -/
lemma CMLattice.exists_eq_const_mul_twistedTranslate_theta (C : CMLattice d) {e m : ℕ}
    (E : CMLattice e) {f : ℂ → ℂ} {u a : ℂ} (ha : a ≠ 0)
    (hg : (fun z : ℂ ↦ E.twistedTranslate 1 u E.θ (a * z)) ∈ C.sections m) (hf : f ∈ C.sections m)
    (h_zero : ∀ z : ℂ, E.twistedTranslate 1 u E.θ (a * z) = 0 → f z = 0) :
    ∃ c : ℂ, ∀ z : ℂ, f z = c * E.twistedTranslate 1 u E.θ (a * z) := by
  -- The quotient `q`, with `q * g = f`, is a section of degree `0`, hence constant.
  obtain ⟨q, hq_const, hq⟩ := C.exists_mul_eq_of_mem_sections E u C.sections_zero_le_const hg hf ha
    rfl h_zero
  obtain ⟨c, rfl⟩ := Submodule.mem_one.1 hq_const
  exact ⟨c, fun z ↦ by simp [← hq]⟩

/-- Let `a ≠ 0` be an isogeny from `C` to `D` of degree `N`, let the invariants `a₁` of `C'`, `D'`
be the `σ`-conjugates of those of `C`, `D`, and let `σ a` be an isogeny from `C'` to `D'` of
degree `N` (the classes `PrimeSevenModEight` say that `d`, `d'` are primes ≡ 7 mod 8). Then the
quotient `θ' / σ θ` of Taylor series of theta functions (`thetaQuotient`) for `D` and `D'`, taken
at `σ a * z`, is the `N`-th power of that for `C` and `C'`. -/
lemma rescale_thetaQuotient_of_conj_isogeny [PrimeSevenModEight d'] {C' D' : CMLattice d'} {N : ℕ}
    (hC : C'.a₁ = σ C.a₁) (hD : D'.a₁ = σ D.a₁) (ha : C.IsIsogeny D.periodPair a N) (ha₀ : a ≠ 0)
    (h_isog : C'.IsIsogeny D'.periodPair (σ a) N) :
    rescale (σ a) (thetaQuotient D σ D') = thetaQuotient C σ C' ^ N := by
  obtain ⟨A, -, B, hB, -, hB_zero, -, hB_ser, h_quot⟩ := exists_conj_isogeny_sections σ hC hD ha
  -- `B` and `D'.θ (σ a * z)` are sections of degree `N` and the first vanishes at the zeros of
  -- the second, so their quotient is constant; both are 1 at 0, so they are equal.
  have h_zero (z : ℂ) (hz : D'.θ (σ a * z) = 0) : B z = 0 := by
    have h_notMem : σ a * z ∉ D'.Λ := fun h ↦
      D'.t_notMem ((add_mem_cancel_left h).1 (D'.theta_eq_zero_iff.1 hz))
    simpa [hz, h_notMem] using h_quot z
  have hB_eq : B = fun z ↦ D'.θ (σ a * z) := by
    obtain ⟨c, hc⟩ : ∃ c : ℂ, ∀ z : ℂ, B z = c * D'.θ (σ a * z) := by
      simpa using C'.exists_eq_const_mul_twistedTranslate_theta D' (u := 0) (a := σ a)
        (by simpa using ha₀) (by simpa using C'.comp_mul_mem_sections h_isog D'.theta_mem) hB
        (by simpa using h_zero)
    obtain rfl : 1 = c := by simpa [hB_zero] using hc 0
    simpa [funext_iff] using hc
  have hθ : taylorAtZero D'.θ = thetaQuotient D σ D' * taylorVia (↑σ) D.θ := by
    simpa [monomialSection] using taylorAtZero_monomialSection σ hD (1, 0, 0)
  -- Compare the two forms of the series of `B` and cancel the conjugate series of `D.θ (a * z)`.
  have h_series : rescale (σ a) (taylorAtZero D'.θ) =
      thetaQuotient C σ C' ^ N * rescale (σ a) (taylorVia σ D.θ) := by
    simpa [taylorVia, ← rescale_map, hB_eq] using hB_ser
  rw [hθ, map_mul] at h_series
  exact mul_right_cancel₀ (ne_of_apply_ne (coeff 0) (by simp)) h_series

/-- For a prime `d ≡ 7 (mod 8)` the number `ω = (1 + i√d) / 2` has modulus greater than 1. -/
lemma one_lt_norm_quadGen : 1 < ‖quadGen d‖ := by
  have hd : (3 : ℝ) < d := mod_cast (by grind [PrimeSevenModEight] : 3 < d)
  have h_sq : ‖quadGen d‖ ^ 2 = (1 + d) / 4 := by
    norm_num [quadGen, div_pow, Complex.sq_norm, Complex.normSq_apply]
  nlinarith [norm_nonneg (quadGen d)]

namespace CMLattice

/-- Let `d` be a prime `≡ 7 (mod 8)` and `σ` an automorphism of `ℂ` over `ℚ(√-d)`. Let `C`, `D` be
CM lattices, each a lattice stable under `𝓞_K` with a point `t` of order two scaled so that
`℘''(t) = 2`, a square root `a₁` of `12 ℘(t)`, and a theta function. If `D.a₁ = σ C.a₁`, the Taylor
series of the theta function of `D` is the `σ`-conjugate of that of `C`: the quotient `θ' / σ θ` is
1. -/
lemma thetaQuotient_eq_one (hD : D.a₁ = σ C.a₁) : thetaQuotient C σ D = 1 := by
  -- Write `q = thetaQuotient C σ D`, `ω = quadGen d`, and suppose `q - 1 = X ^ n * W` with
  -- `W 0 ≠ 0`. The relation `q (ω z) = q ^ (ω ω̄)` gives `ω ^ n = ω ω̄` in degree `n`; moduli give
  -- `n = 2`, so `ω` would be real.
  by_contra h_ne
  obtain ⟨n, W, hW, h_fac⟩ :
      ∃ (n : ℕ) (W : ℂ⟦X⟧), ¬X ∣ W ∧ thetaQuotient C σ D - 1 = X ^ n * W :=
    WfDvdMonoid.max_power_factor (sub_ne_zero.2 h_ne) X_irreducible
  let ω : ℂ := quadGen d
  have hω_mem : ω ∈ quadInt d := quadGen_mem_quadInt
  have hω_norm : 1 < ‖ω‖ := one_lt_norm_quadGen
  have hω_ne : ω ≠ 0 := norm_pos_iff.1 (one_pos.trans hω_norm)
  obtain ⟨N, hN⟩ := exists_isIsogeny_of_mul_mem_lattice (C.mul_mem_of_quadInt hω_mem)
  have h_norm : ω * star ω = N := by simpa [(area_pos C.periodPair).ne'] using hN.2
  have h_rescale : rescale ω (thetaQuotient C σ D - 1) = thetaQuotient C σ D ^ N - 1 := by
    have h_isog : D.IsIsogeny D.periodPair (σ ω) N := by
      simpa [hω_mem] using ⟨D.mul_mem_of_quadInt hω_mem, by simp [← h_norm]⟩
    simpa [hω_mem] using rescale_thetaQuotient_of_conj_isogeny σ hD hD hN hω_ne h_isog
  -- The coefficients of `X ^ n` are `ω ^ n * W 0` and `W 0 * N`, as `q` has constant term 1.
  have h_pow : ω ^ n = ω * star ω := by
    have h_series : rescale ω (X ^ n * W) =
        X ^ n * (W * ∑ i ∈ Finset.range N, thetaQuotient C σ D ^ i) := by
      rw [← mul_assoc, ← h_fac, mul_geom_sum, h_rescale]
    have h_coeff : ω ^ n * constantCoeff W = constantCoeff W * N := by
      simpa [coeff_X_pow_mul', thetaQuotient] using
        (coeff_rescale ..).symm.trans (congrArg (coeff n) h_series)
    rw [h_norm]
    exact mul_right_cancel₀ (mt X_dvd_iff.2 hW) (h_coeff.trans (mul_comm _ _))
  obtain rfl : n = 2 := by
    have h_moduli : ‖ω‖ ^ n = ‖ω‖ ^ 2 := by rw [← norm_pow, h_pow, norm_mul, norm_star, sq]
    exact pow_right_injective₀ (by positivity) hω_norm.ne' h_moduli
  -- This is absurd: `ω = (1 + i√d) / 2` has a nonzero imaginary part.
  have h_real : ω = star ω := mul_left_cancel₀ hω_ne (by rw [← h_pow, sq])
  simp [ω, quadGen, Complex.ext_iff, NeZero.ne, eq_neg_iff_add_eq_zero] at h_real

/-- If `D.a₁ = σ C.a₁` for an automorphism `σ` of `ℂ` over `K`, the Taylor series at 0 of every
monomial section of `D` is the `σ`-conjugate of that of `C`. -/
lemma taylorAtZero_monomialSection_eq_taylorVia {C D : CMLattice d} (hD : D.a₁ = σ C.a₁)
    (j : ℕ × ℕ × ℕ) : taylorAtZero (D.monomialSection j) = taylorVia σ (C.monomialSection j) := by
  simpa [thetaQuotient_eq_one σ hD] using taylorAtZero_monomialSection σ hD j

/-- If `D.a₁ = σ C.a₁` for an automorphism `σ` of `ℂ` over `K`, the Taylor series at 0 of the
theta function of `D` is the `σ`-conjugate of that of `C`. -/
lemma taylorAtZero_theta_eq_taylorVia (hD : D.a₁ = σ C.a₁) :
    taylorAtZero D.θ = taylorVia σ C.θ := by
  simpa [monomialSection] using taylorAtZero_monomialSection_eq_taylorVia σ hD (1, 0, 0)

/-! ### Translates of θ by torsion points -/

variable (C D)

section

omit [PrimeSevenModEight d]

/-- The twisted translate of `θ` by `u + u` takes the value `θ u` at `-u`. -/
lemma twistedTranslate_add_self_apply_neg (u : ℂ) :
    C.twistedTranslate 1 (u + u) C.θ (-u) = C.θ u := by
  -- `hermitianForm` stays folded: the exponent of the translate vanishes by linearity alone.
  simp [thetaShift_apply, -hermitianForm_apply]

/-- If `θ u = 0`, the twisted translate of `θ` by `u + u` takes the value `-1` at 0. -/
lemma twistedTranslate_add_self_apply_zero {u : ℂ} (hu : C.θ u = 0) :
    C.twistedTranslate 1 (u + u) C.θ 0 = -1 := by
  -- Here `u + C.t` is a period, hence so are `u + u` and `u - C.t`, and the sign is `-1`.
  have h_add : u + C.t ∈ C.Λ := C.theta_eq_zero_iff.1 hu
  have h_two : u + u ∈ C.Λ := by simpa using add_mem h_add (sub_mem h_add C.two_t_mem)
  have h_half : (u + u) / 2 - C.t ∈ C.Λ := by simpa using sub_mem h_add C.two_t_mem
  rw [(C.twistedTranslate_theta_eq_neg_iff h_two).mpr h_half, Pi.neg_apply, theta_zero]

/-- Let `N u` be a period of `C` for a natural number `N`, and let `l` be a period. Then the
twisted translate `z ↦ exp (-π (z ū + |u|² / 2) / area Λ) * θ (z + u)` of the theta function by the
point `u + 2 N l` is its twisted translate by `u`. -/
lemma twistedTranslate_theta_add_two_mul (C : CMLattice d) {u l : ℂ} {N : ℕ}
    (hu : (N : ℂ) * u ∈ C.Λ) (hl : l ∈ C.Λ) :
    C.twistedTranslate 1 (u + 2 * N * l) C.θ = C.twistedTranslate 1 u C.θ := by
  -- Moving by the period `2 N l` multiplies the translate by the multiplier there, which is `1`,
  -- and by `exp (-π i E(u, 2 N l)) = exp (-2 π i E(N u, l)) = 1`, as `E(N u, l)` is an integer.
  have h_Nl : (N : ℂ) * l ∈ C.Λ := by simpa using nsmul_mem hl N
  have h_period : 2 * N * l ∈ C.Λ := by simpa [two_mul, add_mul] using add_mem h_Nl h_Nl
  have h_multiplier : C.multiplier (2 * N * l) = 1 := by
    have h_eq : (C.t + C.t + 2 * N * l) / 2 = C.t + N * l := by ring
    simp [C.multiplier_eq_neg_sigmaSign h_period, sigmaSign, h_eq, add_mem_cancel_right h_Nl,
      C.t_notMem]
  obtain ⟨k, hk⟩ : ∃ k : ℤ, C.hermitianForm.riemannForm (N * u) l = k :=
    C.isAppellHumbert_multiplier.le_dualLattice hu l hl
  have h_form : (1 • C.hermitianForm).riemannForm u (2 * N * l) = 2 * k := by
    simp [← hk, riemannForm_hermitianForm]
    ring
  have h_phase : Complex.exp
      (-(Real.pi * Complex.I * (1 • C.hermitianForm).riemannForm u (2 * N * l))) = 1 := by
    rw [h_form, Complex.exp_eq_one_iff]
    exact ⟨-k, by push_cast; ring⟩
  rw [CMLattice.twistedTranslate, IsAppellHumbert.thetaShift_add_eq_smul_of_mem C.theta_mem u
    h_period,
    h_phase, pow_one, h_multiplier, one_mul, one_smul]

end

/-- Let `e` and `m` be nonzero natural numbers such that `Ω e` and `m s Ω` are periods of `C`, and
let `(s' - s) / (2 m e)` be integral. Then the translate of `θ` by `s' Ω` is its translate by
`s Ω`. -/
lemma twistedTranslate_theta_eq_of_isIntegral (C : CMLattice d) {Ω : ℂ} {e m : ℕ}
    {s s' : QuadField d} (he : e ≠ 0) (hm : m ≠ 0) (hΩ : Ω * e ∈ C.Λ) (hs : (m : ℂ) * (s * Ω) ∈ C.Λ)
    (h_int : IsIntegral ℤ ((s' - s) / ((2 * m * e : ℕ) : QuadField d))) :
    C.twistedTranslate 1 (s' * Ω) C.θ = C.twistedTranslate 1 (s * Ω) C.θ := by
  -- `s' Ω = s Ω + 2 m l` with the period `l = k Ω e`, where `k = (s' - s) / (2 m e)`.
  let k : QuadField d := (s' - s) / ((2 * m * e : ℕ) : QuadField d)
  have hl : (k : ℂ) * (Ω * e) ∈ C.Λ := C.mul_mem_of_quadInt ⟨⟨k, h_int⟩, rfl⟩ hΩ
  have h_split : (s' : ℂ) * Ω = s * Ω + 2 * m * (k * (Ω * e)) := by
    push_cast [k, show ((2 : QuadField d) : ℂ) = 2 from map_ofNat (QuadField d).val 2]
    field
  rw [h_split, C.twistedTranslate_theta_add_two_mul hs hl]

/-- Let `n` be an integer with `n s ∈ 𝓞_K`, and let `v` be a period of `C`. The translate of
`θ` by `s v`, taken at `n z`, is a section of degree `n²`. -/
lemma twistedTranslate_theta_comp_intCast_mul_mem (C : CMLattice d) {n : ℤ} {s v : ℂ}
    (hs : n * s ∈ quadInt d) (hv : v ∈ C.Λ) :
    (fun z : ℂ ↦ C.twistedTranslate 1 (s * v) C.θ (n * z)) ∈ C.sections (1 * (n * n).natAbs) := by
  have h_per : n * (s * v) ∈ C.Λ := by simpa [mul_assoc] using C.mul_mem_of_quadInt hs hv
  have h_isog : C.IsIsogeny C.periodPair (starRingEnd ℂ n) (n * n).natAbs :=
    ⟨fun l hl ↦ by simpa using zsmul_mem hl n, by simp⟩
  simpa using C.twistedTranslate_comp_mem h_isog h_per

/-- Suppose that for all `m`, every section `f` of `D` of degree `m` has a `σ`-conjugate section of
`C` with value `μ ^ m * σ (f u')` at `u`, `σ` being an automorphism of `ℂ` over `K`. Then for
`a ∈ quadInt d` there is one `N` such that, for all `m` and all such `f`, every entire function with
Taylor series conjugate to that of `f` takes the value `μ ^ (m N) * σ (f (a u'))` at `a u`. -/
lemma exists_forall_apply_mul_eq_pow_mul {C D : CMLattice d} {a u u' μ : ℂ} (ha : a ∈ quadInt d)
    (transport : ∀ {m : ℕ} {f : ℂ → ℂ}, f ∈ D.sections m →
      ∃ g ∈ C.sections m, taylorAtZero g = taylorVia σ f ∧ g u = μ ^ m * σ (f u')) :
    ∃ N : ℕ, ∀ {m : ℕ} {f g : ℂ → ℂ}, f ∈ D.sections m → taylorAtZero g = taylorVia σ f →
      Differentiable ℂ g → g (a * u) = μ ^ (m * N) * σ (f (a * u')) := by
  obtain ⟨N, hN⟩ := exists_isIsogeny_of_mul_mem_lattice (D.mul_mem_of_quadInt ha)
  refine ⟨N, fun {m f g} hf hfg hg ↦ ?_⟩
  -- Transport `f (a z)`; by uniqueness of Taylor series the result is `g (a z)`.
  obtain ⟨G, hG, hG_ser, hG_val⟩ := transport (D.comp_mul_mem_sections hN hf)
  have hf_diff : Differentiable ℂ f := hf.1
  obtain rfl : G = fun z : ℂ ↦ g (a * z) := by
    refine eq_of_taylorAtZero_eq hG.1 (by fun_prop) ?_
    simp (disch := fun_prop) [hG_ser, hfg, taylorVia, ← rescale_map,
      map_eq_self_of_mem_quadInt σ ha]
  exact hG_val

/-- In the situation of `exists_forall_apply_mul_eq_pow_mul` (each section `f` of degree `m` of `D`
gives a section of `C` with conjugate series and value `μ ^ m * σ (f u')` at `u`; `a ∈ quadInt d`)
let `μ ≠ 0`. If the Taylor series of the entire function `g` is conjugate to that of the section `f`
of `D`, then `g` vanishes at `a u` exactly when `f` vanishes at `a u'`. -/
lemma apply_mul_eq_zero_iff_of_transport {C D : CMLattice d} {a u u' μ : ℂ} {m : ℕ} {f g : ℂ → ℂ}
    (hμ : μ ≠ 0) (ha : a ∈ quadInt d)
    (transport : ∀ {m : ℕ} {f : ℂ → ℂ}, f ∈ D.sections m →
      ∃ g ∈ C.sections m, taylorAtZero g = taylorVia σ f ∧ g u = μ ^ m * σ (f u'))
    (hf : f ∈ D.sections m) (hfg : taylorAtZero g = taylorVia σ f) (hg : Differentiable ℂ g) :
    g (a * u) = 0 ↔ f (a * u') = 0 := by
  obtain ⟨N, hN⟩ := exists_forall_apply_mul_eq_pow_mul σ ha transport
  simp [hN hf hfg hg, hμ]

/-- If `n ≠ 0`, the lattice of `C` is `2 n² w 𝓞_K` and the translate of `θ` by `2 n² s w` vanishes
at `n z`, then `z = (b - 2 n s) w` for some `b ∈ quadInt d`. -/
lemma exists_quadInt_of_twistedTranslate_theta_eq_zero (C : CMLattice d) {n : ℤ} {s w z : ℂ}
    (hn : n ≠ 0) (hΛ : ∀ {l : ℂ}, l ∈ C.latticeModule ↔ ∃ a ∈ quadInt d, 2 * n ^ 2 * w * a = l)
    (hz : C.twistedTranslate 1 (s * (2 * n ^ 2 * w)) C.θ (n * z) = 0) :
    ∃ b ∈ quadInt d, z = (b - (n * s + n * s)) * w := by
  replace hz : n * z + s * (2 * n ^ 2 * w) + C.t ∈ C.Λ := by simpa [thetaShift_apply] using hz
  -- Twice a point congruent to `C.t` modulo the lattice is a period.
  obtain ⟨b, hb, hb_eq⟩ : ∃ b ∈ quadInt d, 2 * n ^ 2 * w * b =
      n • (n * z + s * (2 * n ^ 2 * w) + C.t + (n * z + s * (2 * n ^ 2 * w) + C.t -
        (C.t + C.t))) :=
    hΛ.1 (zsmul_mem (add_mem hz (sub_mem hz C.two_t_mem)) n)
  refine ⟨b, hb, mul_left_cancel₀ (a := (2 * n ^ 2 : ℂ)) (by simp [hn]) ?_⟩
  rw [zsmul_eq_mul] at hb_eq
  linear_combination -hb_eq

/-- `sections m` are the theta functions with form `m H` and multiplier `χ^m`;
`twistedTranslate m y f` is `z ↦ exp(−mπ(zȳ + |y|²/2)/A) f(z + y)`, `A` the area of `Λ`; `quadInt d`
is the image of `𝓞_K` in `ℂ`. Suppose the Taylor series of `C.θ` at 0 is the `σ`-conjugate of that
of `D.θ`. Suppose also that each degree-`m` section `f` of `D` gives a section `g` of `C` with
conjugate series and `g w = μ^m σ(f w')`, where `μ ≠ 0`. Let `n s ∈ quadInt d` and `2 n² w' ∈ D.Λ`.
If `c` times the degree-1 translate of `C.θ` by `s 2n² w`, at `n z`, is a degree-`n²` section whose
series is the conjugate of that of the translate of `D.θ` by `s 2n² w'` at `n z`, then `c = 1`. -/
lemma eq_one_of_taylorVia_twistedTranslate_theta {C D : CMLattice d} {n : ℤ} {s w w' c μ : ℂ}
    (hμ : μ ≠ 0) (hs : n * s ∈ quadInt d) (hv : 2 * n ^ 2 * w' ∈ D.Λ)
    (hθ : taylorAtZero C.θ = taylorVia σ D.θ)
    (transport : ∀ {m : ℕ} {f : ℂ → ℂ}, f ∈ D.sections m →
      ∃ g ∈ C.sections m, taylorAtZero g = taylorVia σ f ∧ g w = μ ^ m * σ (f w'))
    (hg : (fun z : ℂ ↦ c * C.twistedTranslate 1 (s * (2 * n ^ 2 * w)) C.θ (n * z)) ∈
      C.sections (1 * (n * n).natAbs))
    (hg_ser : taylorAtZero (fun z : ℂ ↦
        c * C.twistedTranslate 1 (s * (2 * n ^ 2 * w)) C.θ (n * z)) =
      taylorVia σ (fun z : ℂ ↦ D.twistedTranslate 1 (s * (2 * n ^ 2 * w')) D.θ (n * z))) :
    c = 1 := by
  -- The translate is by `2 p`, `p = n² s w`. At `n z = -p` its exponential factor is 1, so its
  -- value is `θ_C p`, as is that of `θ_C (n z)`; likewise for `D`. If `θ_C p = 0`, both translates
  -- take the value `-1` at 0.
  have h_scaled_mem (E : CMLattice d) :
      (fun z : ℂ ↦ E.θ (n * z)) ∈ E.sections (1 * (n * n).natAbs) := by
    simpa using E.twistedTranslate_theta_comp_intCast_mul_mem hs (zero_mem _)
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ {m : ℕ} {f g : ℂ → ℂ}, f ∈ D.sections m →
      taylorAtZero g = taylorVia σ f → Differentiable ℂ g →
      g (-(n * s) * w) = μ ^ (m * N) * σ (f (-(n * s) * w')) :=
    exists_forall_apply_mul_eq_pow_mul σ (neg_mem hs) transport
  have h_shift : c * C.twistedTranslate 1 (s * (2 * n ^ 2 * w)) C.θ (-(n * (n * s * w))) =
      μ ^ ((n * n).natAbs * N) *
        σ (D.twistedTranslate 1 (s * (2 * n ^ 2 * w')) D.θ (-(n * (n * s * w')))) := by
    simpa using hN (D.twistedTranslate_theta_comp_intCast_mul_mem hs hv) hg_ser hg.1
  have h_plain : C.θ (n * (n * s * w)) =
      μ ^ ((n * n).natAbs * N) * σ (D.θ (n * (n * s * w'))) := by
    have h_scaled : taylorAtZero (fun z : ℂ ↦ C.θ (n * z)) =
        taylorVia σ (fun z : ℂ ↦ D.θ (n * z)) := ext (by simp [hθ])
    simpa using hN (h_scaled_mem D) h_scaled (h_scaled_mem C).1
  have h_origin : c * C.twistedTranslate 1 (s * (2 * n ^ 2 * w)) C.θ 0 =
      σ (D.twistedTranslate 1 (s * (2 * n ^ 2 * w')) D.θ 0) := by
    simpa using congrArg constantCoeff hg_ser
  have h_double (v : ℂ) : s * (2 * n ^ 2 * v) = n * (n * s * v) + n * (n * s * v) := by ring
  rw [h_double, h_double] at h_shift h_origin
  by_cases hp : C.θ (n * (n * s * w)) = 0
  · have hq : D.θ (n * (n * s * w')) = 0 := by simpa [hp, hμ] using h_plain
    rw [C.twistedTranslate_add_self_apply_zero hp,
      D.twistedTranslate_add_self_apply_zero hq] at h_origin
    simpa using h_origin
  · rw [twistedTranslate_add_self_apply_neg, twistedTranslate_add_self_apply_neg,
      ← h_plain] at h_shift
    exact (mul_eq_right₀ hp).1 h_shift

/-- Let `d` be a prime `≡ 7 (mod 8)` and `K = ℚ(√-d)`. Let `C`, `D` be CM lattices, each a lattice
stable under `𝓞_K` with a point `t` of order two scaled so that `℘''(t) = 2`, a square root `a₁` of
`12 ℘(t)`, and a theta function `θ`. Suppose `D.a₁ = σ C.a₁` for an automorphism `σ` of `ℂ` over
`K`, and the lattice of `C` is `Ω 𝓞_K`. Then for every finite set `S ⊆ K` there is a period `v` of
`D` such that, for all `s ∈ S`, applying `σ` to the Taylor coefficients at 0 of the translate of `θ`
by `s Ω` gives those of the translate by `s v` of the theta function of `D`. The translate by `u` is
the twisted one, `z ↦ exp (-π (z ū + |u|² / 2) / area Λ) * θ (z + u)`. -/
lemma exists_taylorVia_twistedTranslate_theta (hD : D.a₁ = σ C.a₁) (Ω : ℂ)
    (hΛ : ∀ {z : ℂ}, z ∈ C.latticeModule ↔ ∃ a ∈ quadInt d, Ω * a = z) (S : Finset (QuadField d)) :
    ∃ v ∈ D.latticeModule, ∀ s ∈ S, taylorVia σ (C.twistedTranslate 1 (s * Ω) C.θ) =
      taylorAtZero (D.twistedTranslate 1 (s * v) D.θ) := by
  -- Take `n ≠ 0` with `n S ⊆ 𝓞_K`, write `Ω = 2 n² w` and transport by `σ.symm` from `D` to `C`;
  -- a point `w'` of `D` matches `w`, and `v = 2 n² w'`. The transport of `(T_{s v} θ_D)(n z)`
  -- vanishes at the zeros of `(T_{s Ω} θ_C)(n z)`, so it is a multiple of it, and comparing
  -- values gives the factor 1.
  obtain ⟨n, hn, hS⟩ : ∃ n : ℤ, n ≠ 0 ∧ ∀ s ∈ S, IsIntegral ℤ (n • s) :=
    exists_integral_multiples ℤ ℚ S
  obtain ⟨w, rfl⟩ : (2 * n ^ 2 : ℂ) ∣ Ω := by simp [hn]
  have hC : C.a₁ = σ.symm D.a₁ := by simp [hD]
  have hΩ : 2 * n ^ 2 * w ∈ C.Λ := hΛ.2 ⟨1, by simp, mul_one _⟩
  -- As `thetaQuotient D σ.symm C = 1`, the transported series are plainly conjugate.
  obtain ⟨w', μ, hμ, transport⟩ : ∃ w' : ℂ, ∃ μ ≠ (0 : ℂ),
      ∀ {m : ℕ} {f : ℂ → ℂ}, f ∈ D.sections m → ∃ g ∈ C.sections m,
        taylorAtZero g = taylorVia σ.symm f ∧ g w = μ ^ m * σ.symm (f w') := by
    obtain ⟨w', μ, hμ, -, h_section⟩ := exists_conjugate_section σ.symm hC w
    simp only [thetaQuotient_eq_one σ.symm hC, one_pow, one_mul] at h_section
    exact ⟨w', μ, hμ, h_section⟩
  have h_mon_zero {a : ℂ} (ha : a ∈ quadInt d) (j : ℕ × ℕ × ℕ) :
      C.monomialSection j (a * w) = 0 ↔ D.monomialSection j (a * w') = 0 :=
    apply_mul_eq_zero_iff_of_transport σ.symm hμ ha transport (D.monomialSection_mem j)
      (taylorAtZero_monomialSection_eq_taylorVia σ.symm hC j) (C.monomialSection_mem j).1
  -- The zeros of `C.σ ^ 2` and `D.σ ^ 2` are the periods.
  have hv : 2 * n ^ 2 * w' ∈ D.Λ := by
    simpa [monomialSection] using (h_mon_zero (mod_cast intCast_mem _ (2 * n ^ 2)) (0, 1, 0)).1
      (by simpa [monomialSection] using hΩ)
  refine ⟨2 * n ^ 2 * w', hv, fun s hsS ↦ ?_⟩
  have hs : n * (s : ℂ) ∈ quadInt d :=
    ⟨⟨n * s, by simpa [zsmul_eq_mul, mem_integralClosure_iff] using hS s hsS⟩, rfl⟩
  have h_sec := D.twistedTranslate_theta_comp_intCast_mul_mem hs hv
  -- `g` is the transport of the translate by `s v` of `D.θ`, taken at `n z`.
  obtain ⟨g, hg, hg_ser⟩ : ∃ g ∈ C.sections (1 * (n * n).natAbs), taylorAtZero g =
      taylorVia σ.symm (fun z ↦ D.twistedTranslate 1 (s * (2 * n ^ 2 * w')) D.θ (n * z)) :=
    (transport h_sec).imp fun _ h ↦ h.imp_right And.left
  have h_vanish (z : ℂ) (hz : C.twistedTranslate 1 (s * (2 * n ^ 2 * w)) C.θ (n * z) = 0) :
      g z = 0 := by
    obtain ⟨b, hb, rfl⟩ : ∃ b ∈ quadInt d, z = (b - (n * s + n * s)) * w :=
      C.exists_quadInt_of_twistedTranslate_theta_eq_zero hn hΛ hz
    have h_point (u : ℂ) :
        n * ((b - (n * s + n * s)) * u) + s * (2 * n ^ 2 * u) = n * b * u := by ring
    have h_theta : n * b * w + C.t ∈ C.Λ ↔ n * b * w' + D.t ∈ D.Λ := by
      simpa [monomialSection] using h_mon_zero (zsmul_mem hb n) (1, 0, 0)
    have hbw : n * b * w + C.t ∈ C.Λ := by simpa [thetaShift_apply, h_point] using hz
    refine (apply_mul_eq_zero_iff_of_transport σ.symm hμ (sub_mem hb (add_mem hs hs)) transport
      h_sec hg_ser hg.1).2 ?_
    simpa [thetaShift_apply, h_point] using h_theta.1 hbw
  obtain ⟨c, hc⟩ := C.exists_eq_const_mul_twistedTranslate_theta C (Int.cast_ne_zero.2 hn)
    (C.twistedTranslate_theta_comp_intCast_mul_mem hs hΩ) hg h_vanish
  obtain rfl : g = fun z : ℂ ↦ c * C.twistedTranslate 1 (s * (2 * n ^ 2 * w)) C.θ (n * z) :=
    funext hc
  obtain rfl : c = 1 := eq_one_of_taylorVia_twistedTranslate_theta σ.symm hμ hs hv
    (taylorAtZero_theta_eq_taylorVia σ.symm hC) transport hg hg_ser
  -- Apply `σ` to the `k`-th coefficient of `hg_ser` and undo the scaling by `n`.
  ext k
  simpa [hn] using congrArg σ (PowerSeries.ext_iff.1 hg_ser k)

end CMLattice

end New

end ConjugateCurve
