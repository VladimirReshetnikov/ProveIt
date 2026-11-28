import New.Derivatives.FormalGroup.Resolution
import New.Derivatives.Vacuum.IntegralVacuum

/-!
# The scale of the Taylor series of a vector

* `New.Space.jet_jetSeries_of_isHomogeneous`: the derivative of the Taylor series along a
  homogeneous polynomial is a theta value times a power of the scale.
* `New.Parameters.norm_periodFactor_mul_daggerForms_le_one`: the scaled linear form of a vector `y`
  is integral at `p` if `α⁻¹ y` is integral above `p`.
* `New.Parameters.norm_jetScale_sq`: the modulus of `jetScale`, from the area of the CM lattice and
  the formula of Chowla and Selberg.

The period scale is `jetScale` times an integer `π_M` of `K` of norm `M`. The statements with this
factor are `New.Data.norm_conj_piMBar_mul_jetScale_sq` and
`New.Data.norm_taylorScale_eq_one_of_not_dvd`.

The statements use these notions:
* `jetSeries a f`: the Taylor series of the theta function of `f`, with variables scaled by `a`;
  `jet R Q F` is the derivative at zero of the series `F` along the polynomial `Q`.
* `daggerForms u j`: the coefficients in `ℂ_p` of the linear form `z ↦ y† z` of the vector
  `y = u j`; at a pair `(v, i)` of an infinite place and a coordinate the coefficient is the image
  in `ℂ_p` of the complex conjugate of `Φ_v (y i)`, with `Φ_v` the embedding chosen at `v`.
* `periodFactor`: the complex number `vacuumRoot / chowlaSelbergUnit`, where `vacuumRoot` is a root
  of the inverse of the value `chiFin α` of a character at the idele `α` and the denominator is a
  unit at every `p`-adic place; `jetScale` is `periodFactor * √(2π / √d) / cmPeriod`, where
  `cmPeriod * 𝓞_K` is the lattice of the CM curve of the field `K = ℚ(i√d)`.

## Relation to the literature

The modulus of `jetScale` is computed from the formula of Chowla and Selberg,
`New.CMLattice.chowla_selberg`.
-/

open NumberField ComplexConjugate MvPolynomial

namespace New

/-- Scaling all variables of a power series `F` by `a` multiplies the derivative `jet R Q F` at
zero along a homogeneous polynomial `Q` of degree `l` by `a ^ l`. -/
lemma jet_rescale {R X : Type} [CommRing R] {Q : MvPolynomial X R} {l : ℕ}
    (hQ : Q.IsHomogeneous l) (a : R) (F : MvPowerSeries X R) :
    jet R Q (MvPowerSeries.rescale (fun (_ : X) ↦ a) F) = a ^ l * jet R Q F := by
  rw [jet_eq_sum, jet_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α hα ↦ ?_
  have h_degree : α.degree = l := by
    by_contra h_ne
    exact mem_support_iff.1 hα (hQ.coeff_eq_zero h_ne)
  rw [MvPowerSeries.coeff_rescale, ← h_degree, Finsupp.degree_apply, ← Finset.prod_pow_eq_pow_sum]
  simp only [Finsupp.prod]
  ring

/-- Let `E` be a CM number field with a chosen CM type (`CMType`) and the data of its Weil
representation (`WeilData`). For a homogeneous polynomial `Q` of degree `l` and a vector `f` of
the Weil representation `𝒮 V` of the hermitian space `V` with signs `ε`, the derivative at zero
along `Q` of the series `V.jetSeries a f` is `a ^ l θ(v_Q ⊗ f)`. Here `θ` is the theta functional,
`realSigns E ε` gives each pair (infinite place, coordinate) the sign of the coordinate,
`v_Q = polyVector Q` is the Fock vector of `Q` for these signs, and `⊗` is `V.integrated`, the
bilinear map that integrates the action of the real Heisenberg group on `f` against `v_Q`. The
series `V.jetSeries a f` has one variable for each such pair; its coefficient at the monomial
`z ^ α` is `a ^ |α| / α! * θ(v_{z ^ α} ⊗ f)`. -/
lemma Space.jet_jetSeries_of_isHomogeneous {E n : Type} [Field E] [CMType E] [WeilData E]
    [Fintype n] [DecidableEq n] {ε : n → ℤˣ} (V : Space E n ε)
    {Q : MvPolynomial (InfinitePlace E × n) ℂ} {l : ℕ} (hQ : Q.IsHomogeneous l) (a : ℂ) (f : 𝒮 V) :
    jet ℂ Q (V.jetSeries a f) =
      a ^ l * V.θ (V.integrated (Fock.polyVector (realSigns E ε) Q) f) := by
  -- Write the scale as `a * 1`, take out `a ^ l` and use the formula at the scale `1`.
  rw [← mul_one a, jetSeries_mul_eq_rescale, jet_rescale hQ, jet_jetSeries_eq_theta, mul_one]
  simp only [one_smul, aeval_X_left_apply]

/-- Let `σ` be an embedding of the number field `E` into a `p`-adic field `F`, that is, a normed
algebra over `ℚ_p` that is a field, here ultrametric and not necessarily complete. The image of a
finite adele `x` under the extension of `σ` to finite adeles has norm at most one if and only if
the component of `x` at the place induced by `σ` is integral. -/
lemma norm_adeleExtension_le_one_iff {E F : Type} [Field E] [NumberField E] {p : ℕ} [Fact p.Prime]
    [NormedField F] [IsUltrametricDist F] [CharZero F] [PadicField F p] (σ : E →+* F)
    {x : 𝔸f E} : ‖adeleExtension σ x‖ ≤ 1 ↔ Valued.v (evalAt (placeOfEmb σ) x) ≤ 1 := by
  -- `adeleExtension σ` is by definition the component at the place, mapped by the extension of `σ`.
  change ‖placeOfEmbExtension σ (evalAt (placeOfEmb σ) x)‖ ≤ 1 ↔ _
  exact (valuation_comap_placeOfEmbExtension_isEquiv σ).le_one_iff_le_one

/-- Let `d` be a prime that is `7` modulo `8`. Two CM lattices for `d` with the same invariant
`a₁` (a square root of `12 ℘(t)` for the marked point `t` of order two) have the same area. -/
lemma CMLattice.area_eq_of_a₁_eq {d : ℕ} [PrimeSevenModEight d] {C D : CMLattice d}
    (h_a₁ : C.a₁ = D.a₁) : C.area = D.area := by
  -- Each lattice contains the other, so each area is an integral multiple of the other.
  have h_multiple (C' D' : CMLattice d) (h_a₁' : C'.a₁ = D'.a₁) :
      ∃ N : ℕ, (C'.area : ℂ) = N * D'.area := by
    have h_id : D'.IsIsogeny D'.periodPair 1 1 :=
      ⟨fun x hx ↦ by rwa [one_mul], by rw [map_one, one_mul, Nat.cast_one]⟩
    obtain ⟨N, -, hN⟩ := exists_isIsogeny_of_mul_mem_lattice
      fun _ ↦ conj_isogeny_mul_mem_lattice 1 (C' := C') (D' := D') h_a₁' rfl h_id
    rw [AlgEquiv.one_apply, map_one, one_mul, one_mul] at hN
    exact ⟨N, hN⟩
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (C.area : ℂ) = N * D.area := h_multiple C D h_a₁
  obtain ⟨N', hN'⟩ : ∃ N' : ℕ, (D.area : ℂ) = N' * C.area := h_multiple D C h_a₁.symm
  have h_prod : N * N' = 1 := by
    have h_ne : (C.area : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (area_pos C.periodPair).ne'
    rw [hN', ← mul_assoc, eq_comm, mul_eq_right₀ h_ne] at hN
    exact_mod_cast hN
  rw [Nat.eq_one_of_mul_eq_one_left h_prod, Nat.cast_one, one_mul] at hN'
  exact_mod_cast hN'.symm

namespace Parameters

/-- Let `y = u j` be a vector over the field `E = P.E s` of the parameters at the index `s`, a
cyclotomic extension of `K = P.K = ℚ(i√d)`, and `α = P.α s` their idele. Let `ιₚ : ℂ → ℂ_p` be the
ring homomorphism chosen by `PadicPlace p`. For a pair `x = (v, i)` of an infinite place of `E` and
a coordinate, `daggerForms u j x` is the image under `ιₚ` of the complex conjugate of `Φ_v (y i)`,
with `Φ_v : E → ℂ` the embedding that the CM type chooses at `v`. If the finite adelic vector
`α⁻¹ y` (`finiteImage (u j)`) is integral at all places above `p` (`integralAfter 1`), then the
product of `ιₚ periodFactor` and this coefficient has norm at most one. -/
lemma norm_periodFactor_mul_daggerForms_le_one {P : Parameters} {s : ℕ} {n : Type} {p : ℕ}
    [Fact p.Prime] [PadicPlace p] {J : Type} {u : J → n → P.E s} {j : J}
    (h_integral :
      finiteImage (u j) ∈ integralAfter (1 : 𝓞 P.K) fun w : FinPlace (P.E s) ↦ ↑p ∈ w.asIdeal)
    (x : InfinitePlace (P.E s) × n) :
    ‖ιₚ (P.periodFactor s) * daggerForms u j x‖ ≤ 1 := by
  -- The norm in question is that of the coordinate `x.2` of `α⁻¹ y` at the place given by `x.1`.
  let σ : P.E s →+* ℂ_[p] := weightEmbedding ιₚ x.1
  have h_int : ‖adeleExtension σ (finiteImage (u j) x.2)‖ ≤ 1 := by
    have h_val : Valued.v (evalAt (placeOfEmb σ)
        (algebraMap (P.E s) (𝔸f (P.E s)) (algebraMap P.K (P.E s) ((1 : 𝓞 P.K) : P.K)) *
          finiteImage (u j) x.2)) ≤ 1 := h_integral x.2 _ (natCast_mem_placeOfEmb σ)
    rw [RingOfIntegers.coe_eq_algebraMap, map_one, map_one, map_one, one_mul] at h_val
    exact (norm_adeleExtension_le_one_iff σ).2 h_val
  have h_image : finiteImage (u j) x.2 =
      ((P.α s)⁻¹).val * algebraMap (P.E s) (𝔸f (P.E s)) (u j x.2) := rfl
  have h_form : daggerForms u j x = σ (u j x.2) := by
    rw [daggerForms, dagger, RingHom.comp_apply, RingHom.comp_apply, starRingEnd_apply,
      starRingEnd_apply, map_star_complex]
  rw [h_image, map_mul, norm_mul, map_units_inv, norm_inv, adeleExtension_algebraMap] at h_int
  rwa [norm_mul, norm_iota_periodFactor x.1, h_form]

/-- Let `P` be the fixed parameters, and `E = P.E s` the field at the index `s`, a cyclotomic
extension of `K = ℚ(i√d)`. The squared modulus of `jetScale = periodFactor * √(2π / √d) / cmPeriod`,
the scale of the Taylor series at the index `s`, is the inverse of
`bigOmega = exp (γ - Re L'/L(1, χ_K)) * 2π / rd_E`. Here `γ` is Euler's constant, `χ_K` the
quadratic character of `K` and `rd_E` the root discriminant of `E`. -/
lemma norm_jetScale_sq (P : Parameters) (s : ℕ) : ‖P.jetScale s‖ ^ 2 = (P.bigOmega s)⁻¹ := by
  -- This is the formula of Chowla and Selberg for `σ = 1`: the lattice chosen as the conjugate by
  -- `1` has the invariant `a₁`, hence the area, of `cmPeriod * 𝓞_K`.
  have h_area : (P.cmCurve.galConjugate 1).area = ‖(P.cmPeriod : ℂ)‖ ^ 2 * √P.d / 2 := by
    have h_a₁ : (P.cmCurve.galConjugate 1).a₁ = P.cmCurve.a₁ :=
      P.cmCurve.galConjugate_a₁ 1
    rw [CMLattice.area_eq_of_a₁_eq h_a₁,
      QuadField.area_eq_of_eq_scaledIdeal latticeModule_cmCurve]
    simp only [Units.val_one, map_one, Rat.cast_one, mul_one]
  rw [← P.norm_gal_periodFactor_div_mul_areaScale_sq s h_area, jetScale, AlgEquiv.one_apply,
    div_mul_eq_mul_div]

end Parameters

end New
