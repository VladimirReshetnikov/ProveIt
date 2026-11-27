import Lib.CM.Integrality.IntegralSections

/-!
# Isogenies and translates act integrally on expansions

Let `p` be a prime and `ιₚ : ℂ →+* ℂ_[p]` a fixed embedding. For a lattice `Λ` of a `CMLattice`, the
function `y_Λ = translatedY` is the second Weierstrass coordinate at `z + t` in the model of the
lattice, `(℘′(z + t) - a₁ x(z)) / 2` with `x(z) = ℘(z + t) - ℘(t)`, `a₁` the `xy`-coefficient of
that Weierstrass model and `t` the chosen point of order two, and `translatedYThetaCube` is the
entire extension of `y θ³`, where `θ` is the theta function of degree one, normalised by `θ(0) = 1`.
The ring `integralSeriesRing` is `𝒪[[y_Λ]]`, the integral power series in the Taylor series of
`y_Λ`, and `taylorVia ιₚ f` is the Taylor series of `f` at `0` with `ιₚ` applied to its
coefficients.

* `New.CMLattice.exists_rescale_theta_eq_theta_pow_mul`: an isogeny of degree `N` pulls `θ` back to
  `θ ^ N` times an integral series in `y`.
* `New.CMLattice.rescale_translatedY_mem_integralSeriesRing`: an isogeny pulls `y` back to an
  integral series in `y`.
* `New.CMLattice.norm_le_one_of_mapsTo_lattice`: the multiplier of an isogeny is integral at `p`.
* `New.CMLattice.exists_rescale_twistedTranslate_eq_theta_pow_mul`: the pull-back of a torsion
  translate of `θ`.

The pull-back statements rest on the integrality principle for sections with integral torsion
values, and the integrality of the multiplier follows from the pull-back of `y`.

## Relation to the literature

Known result: an isogeny of elliptic curves with good reduction acts on the formal groups by an
integral power series. Background: Silverman, *The Arithmetic of Elliptic Curves*, Chapters IV and
VII.
-/

open PowerSeries ComplexConjugate

namespace New.CMLattice

variable {d : ℕ} [PrimeSevenModEight d] (C : CMLattice d) {p : ℕ} [Fact p.Prime] [PadicPlace p]

/-- Let multiplication by `a` be an isogeny of degree `N` from the lattice `Λ` of `C` to the lattice
`Λ'` of `C'`, and let `G` be a section of degree `n` for `C'` (a theta function of that degree)
with integral torsion values (their images under `ιₚ` have norm at most `1`). Then the series of
`G(a z)` (Taylor series at `0`, mapped to `ℂ_[p]` by `ιₚ`) is the `N n`-th power of that of
`θ_Λ = C.θ` times an element of `C.integralSeriesRing`, the ring of integral power series in the
series of `y_Λ = C.translatedY`. -/
lemma exists_rescale_eq_theta_pow_mul {C' : CMLattice d} {a : ℂ} {N n : ℕ} {G : ℂ → ℂ}
    (h_isog : C.IsIsogeny C'.periodPair a N) (hG_mem : G ∈ C'.sections n)
    (hG_int : C'.HasIntegralValues (p := p) n G) :
    ∃ u ∈ C.integralSeriesRing, (taylorVia ιₚ G).rescale (ιₚ a) = (taylorVia ιₚ C.θ ^ N) ^ n *
      u := by
  -- The pull-back `G(a z)` is a section of degree `n N` with integral torsion values.
  have h_int : C.HasIntegralValues (p := p) (n * N) fun z : ℂ ↦ G (a * z) :=
    hG_int.comp_isogeny h_isog
  simpa only [taylorVia, taylorAtZero_comp_mul, rescale_map, pow_mul'] using
    C.exists_taylorVia_eq_theta_pow_mul (C.comp_mul_mem_sections h_isog hG_mem) h_int

/-- Let multiplication by `a` be an isogeny of degree `N` from the lattice `Λ` of `C` to the lattice
`Λ'` of `C'`, and let `θ` be the normalised theta function of degree one. Then the series of
`θ_Λ'(a z)` (Taylor series at `0`, mapped to `ℂ_[p]` by `ιₚ`) is the `N`-th power of that of `θ_Λ`
times an element of `C.integralSeriesRing`. That ring consists of the integral power series in the
series of `y_Λ = C.translatedY`, where `y(z) = ½(℘′(z + t) − a₁ x(z))`, `x(z) = ℘(z + t) − ℘(t)` and
`t` is the chosen point of order two. -/
lemma exists_rescale_theta_eq_theta_pow_mul {C' : CMLattice d} {a : ℂ} {N : ℕ}
    (h_isog : C.IsIsogeny C'.periodPair a N) :
    ∃ v ∈ C.integralSeriesRing, (taylorVia ιₚ C'.θ).rescale (ιₚ a) = taylorVia ιₚ C.θ ^ N * v := by
  simpa only [pow_one] using
    C.exists_rescale_eq_theta_pow_mul h_isog C'.theta_mem C'.hasIntegralValues_theta

/-- Let multiplication by `a` be an isogeny of degree `N` from the lattice `Λ` of `C` to the lattice
`Λ'` of `C'`, and write `y = translatedY`, that is, `y(z) = ½(℘′(z + t) − a₁ x(z))` with
`x(z) = ℘(z + t) − ℘(t)` for the chosen point `t` of order two of each lattice. Then the series of
`y_Λ'(a z)` (Taylor series at `0`, mapped to `ℂ_[p]` by `ιₚ`) lies in `C.integralSeriesRing`, the
ring of integral power series in the series of `y_Λ`. -/
lemma rescale_translatedY_mem_integralSeriesRing {C' : CMLattice d} {a : ℂ} {N : ℕ}
    (h_isog : C.IsIsogeny C'.periodPair a N) :
    (taylorVia ιₚ C'.translatedY).rescale (ιₚ a) ∈ C.integralSeriesRing := by
  -- The series of `θ_Λ'(a z)` is `θ_Λ ^ N R₁` and that of `(y θ³)_Λ'(a z)` is `θ_Λ ^ (3 N) R₃`,
  -- with `R₁`, `R₃` in `𝒪[[y_Λ]]` and `R₁(0) = 1`. So the series of `y_Λ'(a z)` is `R₃ / R₁ ^ 3`.
  have h_cube_mem : C'.translatedYThetaCube ∈ C'.sections 3 := by
    -- `translatedYThetaCube` is the monomial section with exponents `(0, 0, 1)`.
    simpa only [monomialSection, monomialDeg, pow_zero, pow_one, one_mul, zero_mul, zero_add] using
      C'.monomialSection_mem (0, 0, 1)
  obtain ⟨R₁, hR₁, hθ⟩ := C.exists_rescale_theta_eq_theta_pow_mul (p := p) h_isog
  obtain ⟨R₃, hR₃, h_cube⟩ : ∃ R₃ ∈ C.integralSeriesRing,
      (taylorVia ιₚ C'.translatedYThetaCube).rescale (ιₚ a) = (taylorVia ιₚ C.θ ^ N) ^ 3 * R₃ :=
    C.exists_rescale_eq_theta_pow_mul h_isog h_cube_mem C'.hasIntegralValues_translatedYThetaCube
  have h_factor : taylorVia ιₚ C'.translatedYThetaCube =
      taylorVia ιₚ C'.translatedY * taylorVia ιₚ C'.θ ^ 3 := by
    simp (disch := fun_prop) only [taylorVia, taylorAtZero_mul, taylorAtZero_pow, map_mul, map_pow,
      C'.taylorAtZero_congr fun _ hz ↦ C'.translatedYThetaCube_eq_translatedY_mul_theta_cube hz]
  -- Both theta series have constant term `1`, so `R₁` is a unit of `𝒪[[y]]`, with inverse `S`.
  have hθ_const (D : CMLattice d) : constantCoeff (taylorVia ιₚ D.θ) = 1 := by
    rw [constantCoeff_taylorVia, theta_zero, map_one]
  have h_const : constantCoeff R₁ = 1 := by
    simpa [constantCoeff_rescale, hθ_const] using (congrArg constantCoeff hθ).symm
  obtain ⟨S, hS, h_inv⟩ : ∃ S ∈ C.integralSeriesRing, R₁ * S = 1 :=
    C.isSeriesGenerator_translatedY.exists_mul_eq_one hR₁ (by rw [h_const, norm_one])
  have hθ_ne : (taylorVia ιₚ C.θ ^ N) ^ 3 ≠ 0 :=
    pow_ne_zero 3 (pow_ne_zero N (ne_of_apply_ne constantCoeff (by simp)))
  have h_quot : (taylorVia ιₚ C'.translatedY).rescale (ιₚ a) * R₁ ^ 3 = R₃ := by
    rw [h_factor, map_mul, map_pow, hθ] at h_cube
    exact mul_left_cancel₀ hθ_ne (by linear_combination h_cube)
  have hy : (taylorVia ιₚ C'.translatedY).rescale (ιₚ a) = R₃ * S ^ 3 := by
    rw [← h_quot, mul_assoc, ← mul_pow, h_inv, one_pow, mul_one]
  rw [hy]
  exact mul_mem hR₃ (pow_mem hS 3)

/-- Let `d` be a prime that is 7 modulo 8 and `ιₚ : ℂ → ℂ_[p]` a `p`-adic place. Let `C`, `C'` have
lattices `Λ`, `Λ'`, and suppose multiplication by `a` maps `Λ` into `Λ'` with
`a ā area(Λ) = N area(Λ')`; for `a ≠ 0` this makes it an isogeny of degree `N`. Write
`y = translatedY`, that is `y(z) = ½(℘′(z + t) − a₁x(z))` with `x(z) = ℘(z + t) − ℘(t)`, and
`𝒪[[y_Λ]] = C.integralSeriesRing` for the ring of integral power series over `ℂ_[p]` in the Taylor
series of `y_Λ`. Then the Taylor series at `0` of `y_Λ'(a z)`, with coefficients mapped by `ιₚ`,
lies in `𝒪[[y_Λ]]`, and that of the theta function `θ_Λ'(a z)` is the `N`-th power of that of `θ_Λ`
times an element of `𝒪[[y_Λ]]`. This corollary collects `rescale_translatedY_mem_integralSeriesRing`
and `exists_rescale_theta_eq_theta_pow_mul`. -/
lemma rescale_translatedY_mem_and_rescale_theta_eq {C' : CMLattice d} {a : ℂ} {N : ℕ}
    (h_isog : C.IsIsogeny C'.periodPair a N) :
    (taylorVia ιₚ C'.translatedY).rescale (ιₚ a) ∈ C.integralSeriesRing ∧
      ∃ v ∈ C.integralSeriesRing, (taylorVia ιₚ C'.θ).rescale (ιₚ a) = taylorVia ιₚ C.θ ^ N * v :=
  ⟨C.rescale_translatedY_mem_integralSeriesRing h_isog,
    C.exists_rescale_theta_eq_theta_pow_mul h_isog⟩

/-- If multiplication by `a` maps the lattice `Λ` of `C` into the lattice `Λ'` of `C'`, then `a` is
integral at `p`: its image under the embedding `ιₚ : ℂ →+* ℂ_[p]` has norm at most `1`. This relies
on both lattices carrying the normalisation of `CMLattice`, namely `℘''(t) = 2` at the chosen point
`t` of order two, with `d` a prime congruent to 7 mod 8. -/
lemma norm_le_one_of_mapsTo_lattice {C' : CMLattice d} {a : ℂ} (h_maps : ∀ x ∈ C.Λ, a * x ∈ C'.Λ) :
    ‖ιₚ a‖ ≤ 1 := by
  -- The coefficient of `z` in the series of `y_Λ'(a z)`, which lies in `𝒪[[y_Λ]]`, is `ιₚ a`.
  obtain ⟨N, hN⟩ : ∃ N : ℕ, C.IsIsogeny C'.periodPair a N :=
    exists_isIsogeny_of_mul_mem_lattice h_maps
  have h_le : ‖coeff 1 ((taylorVia ιₚ C'.translatedY).rescale (ιₚ a))‖ ≤ 1 :=
    C.isSeriesGenerator_translatedY.norm_coeff_one_le_one
      (C.rescale_translatedY_mem_integralSeriesRing hN)
  rwa [coeff_rescale, C'.isSeriesGenerator_translatedY.coeff_one, pow_one, mul_one] at h_le

/-- Let `δ ≠ 0`, let multiplication by the conjugate `δ̄` be an isogeny of degree `N` of the
lattice `Λ` to itself, and let `δ v ∈ Λ`. Let `T_v θ = C.twistedTranslate 1 v C.θ`, the function
`z ↦ exp(-π (z v̄ + |v|²/2) / A) θ(z + v)` with `A` the area of `Λ`. Then the series of
`(T_v θ)(δ̄ z)` (Taylor series at `0`, mapped to `ℂ_[p]` by `ιₚ`) is the `N`-th power of that of
`θ` times an element of `C.integralSeriesRing`, the ring of integral power series in the series of
`y_Λ = C.translatedY`. -/
lemma exists_rescale_twistedTranslate_eq_theta_pow_mul {δ v : ℂ} {N : ℕ}
    (h_isog : C.IsIsogeny C.periodPair (conj δ) N) (hδ₀ : δ ≠ 0) (hv : δ * v ∈ C.Λ) :
    ∃ R ∈ C.integralSeriesRing, (taylorVia ιₚ (C.twistedTranslate 1 v C.θ)).rescale (ιₚ (conj δ)) =
      taylorVia ιₚ C.θ ^ N * R := by
  -- The function is a section of degree `N = δ δ̄`. It is a pull-back of a translate of `θ` by a
  -- torsion point, so its torsion values are integral.
  have ⟨h_maps, h_degree⟩ : (∀ x ∈ C.periodPair.lattice, conj δ * x ∈ C.periodPair.lattice) ∧
      conj δ * conj (conj δ) * C.area = N * C.area := h_isog
  have hN : conj δ * δ = N := by
    have h_area : (C.area : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (area_pos C.periodPair).ne'
    simpa only [Complex.conj_conj] using mul_right_cancel₀ h_area h_degree
  have h_torsion : C.IsTorsion v := by
    have hN₀ : N ≠ 0 := by
      rintro rfl
      simp [hδ₀] at hN
    refine ⟨N, hN₀, ?_⟩
    simpa only [← hN, mul_assoc] using h_maps (δ * v) hv
  have h_int : C.HasIntegralValues N fun z : ℂ ↦ C.twistedTranslate 1 v C.θ (conj δ * z) := by
    simpa only [one_mul] using (C.hasIntegralValues_theta.translate h_torsion).comp_isogeny h_isog
  -- The Taylor series of `z ↦ f (c z)` is that of `f` rescaled by `c`.
  simpa only [taylorVia, taylorAtZero_comp_mul, rescale_map] using
    C.exists_taylorVia_eq_theta_pow_mul (C.twistedTranslate_comp_mem h_isog hv) h_int

end New.CMLattice
