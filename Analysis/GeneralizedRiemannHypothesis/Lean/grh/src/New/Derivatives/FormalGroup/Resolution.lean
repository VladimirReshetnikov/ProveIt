import Lib.CM.Integrality.LogTheta
import Lib.Weil.Construction.ThetaJets

/-!
# Resolutions of the identity and power series in the compositions `y(μ_i z)`

This file is about families of vectors `u j` in `Eⁿ`, taken `m j` times, with
`z = ∑ m j (u j† z) u j` for all complex vectors `z` indexed by `InfinitePlace E × n`, where `u j`
is read as such a vector through the CM type, and about power series composed with linear forms
`μ_i z`: products of the series `θ(μ_i z)`, for the theta function `θ` of a lattice `C`, and
integral series in the `y(μ_i z)`, for the parameter `y` of the elliptic curve of `C`.

The following imported notions occur in the statements.

* `Φ w` is the complex embedding of the CM type at the infinite place `w` of `E`.
* `ιₚ` is a fixed embedding of `ℂ` into `ℂ_p`, and `valRingCp p` is the closed unit ball of `ℂ_p`.
* `C.multiSeriesRing μ` is the ring of power series with integral coefficients in the series
  `y(μ_i z)`, where `y` is the Taylor series of the parameter `C.translatedY` of the curve.

## Main definitions and results

* `New.dagger`: the coefficients of the linear form `y† z` of a vector `y` in `Eⁿ`;
  `New.daggerForms`: the same for a family of vectors, read in `ℂ_p`.
* `New.IsResolution`: families of vectors `u j`, taken `m j` times, with
  `z = ∑ m j (u j† z) u j` (Parseval frames).
* `New.IsIntegralAbove`: elements of `E` that are integral at all places above `p`; they are
  quotients of elements of `𝓞 E` by natural numbers prime to `p`
  (`New.IsIntegralAbove.exists_mul_eq`).
* `New.CMLattice.thetaProd`: the product of copies of `θ` along linear forms.
* `New.CMLattice.rescale_thetaProd`, `New.CMLattice.rescale_mem_multiSeriesRing`: scaling the
  variables scales the linear forms in a product of copies of `θ` and in an integral series in
  copies of the parameter.
* `New.CMLattice.pderiv_mem_multiSeriesRing`: for integral linear forms, partial derivatives
  preserve the ring of such series.

## Relation to the literature

A resolution of the identity is a Parseval frame.
-/

/-! ## Resolutions of the identity, integrality above a prime, and products of theta series -/

section Resolution

open NumberField ComplexConjugate IsDedekindDomain

namespace New
variable {E n J : Type} [DecidableEq n] [Field E] [CMType E] [Fintype J]

/-- The coefficient at the coordinate `x = (w, c)` of the linear form
`y† z = ∑ conj (Φ w (y c)) z (w, c)`, where `Φ w` is the embedding of the CM type at the infinite
place `w` and the sum is over all pairs `(w, c)`. -/
def dagger (y : n → E) (x : InfinitePlace E × n) : ℂ := conj (Φ x.1 (y x.2))

/-- The vectors `u j` of `Eⁿ`, taken `m j` times, are a resolution of the identity:
`z = ∑ m j (u j† z) u j` for all complex vectors `z` indexed by the pairs `(w, c)`, written in
coordinates. Here `u j` is read as the vector with coordinates `Φ w (u j c)`, where `Φ w` is the
embedding of the CM type at the infinite place `w`, and `dagger (u j)` gives the coefficients of
the linear form `u j† z`. -/
def IsResolution (u : J → n → E) (m : J → ℕ) : Prop :=
  ∀ x y : InfinitePlace E × n,
    ∑ j : J, m j * (Φ x.1 (u j x.2) * dagger (u j) y) = if x = y then 1 else 0

/-- Parseval's identity. If `∑ m_j u_j u_j† = 1` (`IsResolution u m`), then
`∑ m_j conj (u_j† z') (u_j† z) = ∑ conj z'_x z_x` for all complex vectors `z` and `z'`. -/
lemma IsResolution.sum_conj_mul [Fintype n] {u : J → n → E} {m : J → ℕ}
    (hu : IsResolution u m) (z z' : InfinitePlace E × n → ℂ) :
    ∑ j : J, m j * (conj (∑ x : InfinitePlace E × n, dagger (u j) x * z' x) *
        ∑ y : InfinitePlace E × n, dagger (u j) y * z y) =
      ∑ x : InfinitePlace E × n, conj (z' x) * z x := by
  calc ∑ j, m j * (conj (∑ x, dagger (u j) x * z' x) * ∑ y, dagger (u j) y * z y)
      = ∑ j, ∑ x, ∑ y, m j * (Φ x.1 (u j x.2) * dagger (u j) y) * (conj (z' x) * z y) := by
        simp only [map_sum, map_mul, dagger, Complex.conj_conj, Finset.sum_mul_sum]
        simp only [Finset.mul_sum]
        congr! 3
        ring
    _ = ∑ x, ∑ y, ∑ j, m j * (Φ x.1 (u j x.2) * dagger (u j) y) * (conj (z' x) * z y) :=
      Finset.sum_comm.trans (Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm)
    _ = ∑ x, conj (z' x) * z x := by simp [← Finset.sum_mul, hu _ _]

/-- The element `y` of the number field `E` is integral at all places above `p`. A finite place
`w : FinPlace E` is a nonzero prime of `𝓞 E` (a point of `HeightOneSpectrum (𝓞 E)`), `w.asIdeal` is
its underlying ideal and `w.valuation E` is its adic valuation on `E`. -/
def IsIntegralAbove (p : ℕ) (y : E) : Prop :=
  ∀ w : FinPlace E, ↑p ∈ w.asIdeal → w.valuation E y ≤ 1

variable {p : ℕ} [Fact p.Prime]

/-- Let `E` be a CM number field with a CM type (`CMType E`) and `p` a prime number. An element `y`
of `E` that is integral at all primes of `𝓞 E` above `p` is the quotient of an integer `α` of `E`
by a natural number `N` prime to `p`. -/
lemma IsIntegralAbove.exists_mul_eq {p : ℕ} [Fact p.Prime] {y : E} (hy : IsIntegralAbove p y) :
    ∃ (N : ℕ) (α : 𝓞 E), p.Coprime N ∧ (N : E) * y = (α : E) := by
  have hp : p.Prime := Fact.out
  -- Write a denominator of `y` as `p ^ k * N` with `N` prime to `p`.
  obtain ⟨D, β, hD, hβ⟩ : ∃ (D : ℕ) (β : 𝓞 E), D ≠ 0 ∧ D • y = (β : E) :=
    ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).2
      (Algebra.IsAlgebraic.isAlgebraic y)).exists_nsmul_eq (𝓞 E)
  obtain ⟨k, N, hN, rfl⟩ : ∃ k N : ℕ, ¬p ∣ N ∧ D = p ^ k * N :=
    Nat.exists_eq_pow_mul_and_not_dvd hD p hp.ne_one
  have h_mul_denom (w : FinPlace E) : w.valuation E ((p : E) ^ k * (N * y)) ≤ 1 := by
    rw [← mul_assoc, ← Nat.cast_pow, ← Nat.cast_mul, ← nsmul_eq_mul, hβ]
    exact w.valuation_le_one β
  -- `N y` is integral above `p` because `y` is, and elsewhere because `p ^ k N y` is and `p` is a
  -- unit there.
  have h_val (w : FinPlace E) : w.valuation E (N * y) ≤ 1 := by
    by_cases hw : ↑p ∈ w.asIdeal
    · simpa only [map_mul] using
        mul_le_one' (by simpa using w.valuation_le_one (N : 𝓞 E)) (hy w hw)
    · have h_unit : w.valuation E (p : E) = 1 := (w.valuation_eq_one_iff_notMem (K := E)).2 hw
      simpa only [map_mul, map_pow, h_unit, one_pow, one_mul] using h_mul_denom w
  obtain ⟨α, hα⟩ : ∃ α : 𝓞 E, (α : E) = N * y :=
    HeightOneSpectrum.mem_integers_of_valuation_le_one E (N * y : E) h_val
  exact ⟨N, α, hp.coprime_iff_not_dvd.2 hN, hα.symm⟩

/-- An element integral above `p` is integral under every embedding into `ℂ_p`. -/
lemma IsIntegralAbove.norm_le_one {y : E} (hy : IsIntegralAbove p y) (σ : E →+* ℂ_[p]) :
    ‖σ y‖ ≤ 1 :=
  (isEquiv_placeOfEmb σ).le_one_iff_le_one.2 (hy _ (natCast_mem_placeOfEmb σ))

/-- If `y` is integral above `p`, then the complex conjugate of its image under any complex
embedding `τ` has norm at most one in `ℂ_p`, read there by `ιₚ`. -/
lemma IsIntegralAbove.norm_conj_le_one [PadicPlace p] {y : E} (hy : IsIntegralAbove p y)
    (τ : E →+* ℂ) : ‖ιₚ (conj (τ y))‖ ≤ 1 :=
  hy.norm_le_one (ιₚ.comp ((starRingEnd ℂ).comp τ))

/-- The coefficients of the linear forms `u_j† z` of a family of vectors, read in `ℂ_p` by `ιₚ`. -/
noncomputable def daggerForms [PadicPlace p] (u : J → n → E) (j : J) (x : InfinitePlace E × n) :
    ℂ_[p] :=
  ιₚ (dagger (u j) x)

/-- Let `∑ m_j u_j u_j† = 1` (`IsResolution u m`), where `u j` in `Eⁿ` is read as the complex vector
with coordinates `Φ w (u j c)`, and fix `x = (w, c)`. Suppose the integral elements `ν j` of `ℂ_p`
are the images of `Φ w (u j c)` under the embedding `ιₚ` of `ℂ`, and the integral vectors `μ j` are
the coefficients `daggerForms u j` of the forms `u_j† z`, read in `ℂ_p` by `ιₚ`. Then
`∑ m_j ν_j (μ_j z) = z_x` as power series over the valuation ring `valRingCp p` of `ℂ_p`. -/
lemma IsResolution.sum_smul_linearSeries [PadicPlace p] [Fintype n] {u : J → n → E} {m : J → ℕ}
    (hu : IsResolution u m) (x : InfinitePlace E × n) {ν : J → valRingCp p}
    {μ : J → InfinitePlace E × n → valRingCp p}
    (hν : ∀ j : J, (ν j : ℂ_[p]) = ιₚ (Φ x.1 (u j x.2)))
    (hμ : ∀ (j : J) (y : InfinitePlace E × n), (μ j y : ℂ_[p]) = daggerForms u j y) :
    ∑ j : J, (m j * ν j) • linearSeries (μ j) = MvPowerSeries.X x := by
  have h_entry (y : InfinitePlace E × n) : ∑ j, m j * ν j * μ j y = if x = y then 1 else 0 := by
    ext
    simpa [hν, hμ, daggerForms, mul_assoc, apply_ite] using congrArg ιₚ (hu x y)
  simp [linearSeries, Finset.smul_sum, smul_smul, Finset.sum_comm (γ := J), ← Finset.sum_smul,
    h_entry]

/-- The product `∏ θ(μ_j z) ^ m j` of copies of the theta function `C.θ` along linear forms `μ_j`,
as a power series with coefficients in `ℂ_p`. Here `C` is a lattice in `ℂ` with a point `t` of
order two, stable under the ring of integers of `ℚ(√-d)` if `d ≠ 0`; `C.θ` is the twisted
translate by `t` of its sigma function, normalized by `θ(0) = 1`; `taylorVia ιₚ f` is the Taylor
series of `f` at `0`, its coefficients read in `ℂ_p` by the embedding `ιₚ` of `ℂ`; and
`linearSeries (μ j)` is the linear form `μ_j z = ∑ μ j x * z x`. -/
noncomputable def CMLattice.thetaProd [PadicPlace p] {d : ℕ} (C : CMLattice d) {X : Type}
    [Fintype X] (μ : J → X → ℂ_[p]) (m : J → ℕ) : MvPowerSeries X ℂ_[p] :=
  ∏ j : J, (taylorVia ιₚ C.θ).subst (linearSeries (μ j)) ^ m j

end New

end Resolution

/-! ## Scaling and derivatives of series composed with linear forms -/

section ThetaRing

open MvPowerSeries

namespace New

section LinearForms
variable {R X : Type} [CommRing R]

/-- Scaling every variable by `a` in the power series `g.subst (linearSeries c)`, i.e. `g` evaluated
at the linear form `∑ c_i z_i`, gives `g.subst (linearSeries (a • c))`. -/
lemma rescale_subst_linearSeries_eq_subst_smul [Fintype X] (a : R) (c : X → R) (g : PowerSeries R) :
    rescale (fun _ : X ↦ a) (g.subst (linearSeries c)) = g.subst (linearSeries (a • c)) := by
  rw [rescale_subst_linearSeries_eq_mul]
  rfl

/-- Applying a ring homomorphism `φ` to the coefficients turns a scaling of the variables by `a`
into a scaling by `φ a`. -/
lemma map_rescale {S : Type} [CommRing S] (φ : R →+* S) (a : R) (F : MvPowerSeries X R) :
    map φ (rescale (fun _ : X ↦ a) F) = rescale (fun _ : X ↦ φ a) (map φ F) := by
  ext α
  simp [Finsupp.prod]

end LinearForms

/-- Multiplying the scale `b` of the series `V.jetSeries b f` by `a` scales its variables by `a`.
The coefficient of `z ^ α` in `V.jetSeries b f` is `b ^ |α| / α!` times the theta functional of
`v ⊗ f`, where `v` is the Fock vector of `z ^ α`. -/
lemma Space.jetSeries_mul_eq_rescale {E n : Type} [Field E] [CMType E] [WeilData E] [Fintype n]
    [DecidableEq n] {ε : n → ℤˣ} (V : Space E n ε) (a b : ℂ) (f : 𝒮 V) :
    V.jetSeries (a * b) f =
      rescale (fun _ : NumberField.InfinitePlace E × n ↦ a) (V.jetSeries b f) := by
  ext α
  rw [coeff_rescale, Finsupp.prod, Finset.prod_pow_eq_pow_sum, ← Finsupp.degree_apply]
  simp only [coeff_apply, jetSeries_apply]
  ring

namespace CMLattice

/-- Scaling all variables of the product by `a` multiplies each linear form `μ_i` by `a`. -/
lemma rescale_thetaProd {d : ℕ} (C : CMLattice d) {p : ℕ} [Fact p.Prime] [PadicPlace p]
    {I X : Type} [Fintype I] [Fintype X] (a : ℂ_[p]) (μ : I → X → ℂ_[p]) (m : I → ℕ) :
    rescale (fun _ : X ↦ a) (C.thetaProd μ m) = C.thetaProd (a • μ) m := by
  simp only [thetaProd, map_prod, map_pow, rescale_subst_linearSeries_eq_subst_smul, Pi.smul_apply]

variable {d : ℕ} (C : CMLattice d) {p : ℕ} [Fact p.Prime] [PadicPlace p]
  {I X : Type} [Fintype I] [Fintype X]

/-- Let `d` be any natural number and `C` a lattice in `ℂ` that is stable under the ring of integers
of `ℚ(√-d)`, with a point `t` of order two. Let `y` be the Taylor series at `0`, read in `ℂ_p`, of
the function `C.translatedY z = (℘'(z + t) - a₁ (℘(z + t) - ℘(t))) / 2`, where `a₁ ^ 2 = 12 ℘(t)`,
so that `C.multiSeriesRing μ` is the ring of power series with integral coefficients in the
`y(μ_i z)`. If `H(z)` is such a series in the `y(μ_i z)`, then `H(a z)` is such a series in the
`y((a μ_i) z)`. -/
lemma rescale_mem_multiSeriesRing {μ : I → X → ℂ_[p]} {H : MvPowerSeries X ℂ_[p]} (a : ℂ_[p])
    (hH : H ∈ C.multiSeriesRing μ) :
    rescale (fun _ : X ↦ a) H ∈ C.multiSeriesRing (a • μ) := by
  -- Write `H` as `G(y(μ_i z))`; then `H(a z)` is `G(y((a μ_i) z))`.
  obtain ⟨G, rfl⟩ := C.mem_multiSeriesRing_iff.1 hH
  refine C.mem_multiSeriesRing_iff.2 ⟨G, ?_⟩
  have h_rescale (i : I) : rescale (fun _ : X ↦ a)
      ((taylorVia ιₚ C.translatedY).subst (linearSeries (μ i))) =
        (taylorVia ιₚ C.translatedY).subst (linearSeries ((a • μ) i)) := by
    rw [rescale_subst_linearSeries_eq_subst_smul, Pi.smul_apply]
  rw [rescale_eq_subst, subst_comp_subst_apply (C.hasSubst_translatedY_subst μ) (.smul_X _)]
  simp only [← rescale_eq_subst, h_rescale]

/-- For linear forms `μ_i` with coefficients of norm at most one, partial derivatives preserve the
ring `C.multiSeriesRing μ` of power series with integral coefficients in the `y(μ_i z)`. Here `d`
is a prime congruent to `7` modulo `8`, the lattice `C` is stable under the ring of integers of
`ℚ(√-d)`, and `y` is the Taylor series of the parameter `C.translatedY` of its elliptic curve. -/
lemma pderiv_mem_multiSeriesRing [PrimeSevenModEight d]
    {μ : I → X → ℂ_[p]} {H : MvPowerSeries X ℂ_[p]}
    (hμ : ∀ (i : I) (x : X), ‖μ i x‖ ≤ 1) (hH : H ∈ C.multiSeriesRing μ) (x : X) :
    pderiv x H ∈ C.multiSeriesRing μ := by
  -- Write `H` as `G(y(μ_i z))` for an integral series `G`. By the chain rule it is enough to
  -- treat the derivatives of `G` and of each `y(μ_i z)`.
  obtain ⟨G, rfl⟩ := C.mem_multiSeriesRing_iff.1 hH
  rw [pderiv_subst (C.hasSubst_translatedY_subst μ)]
  refine sum_mem fun i _ ↦ mul_mem ?_ ?_
  · exact C.mem_multiSeriesRing_iff.2 ⟨pderiv i G, by rw [map_pderiv]⟩
  · -- The derivative of `y` lies in the ring `C.integralSeriesRing` of integral series in `y`.
    rw [pderiv_subst_linearSeries]
    exact C.smul_mem_multiSeriesRing (hμ i x) (subst_mem_multiSeriesRing μ
      (C.derivative_mem_integralSeriesRing C.isSeriesGenerator_translatedY.generator_mem) i)

end CMLattice

end New

end ThetaRing
