import New.Derivatives.Sharpness.Couplings
import New.Derivatives.Sharpness.NearPairs
import New.Derivatives.Vacuum.Scale

/-!
# The valuation bound `v(l!) + val₁₂(l) ≤ S_p + 2 ∑ v(B_τ)` for every prime

Let `w` be a tight frame of length `M` with a linear form of unit coefficients, and let `val₆` and
`val₁₂` be the least valuations on six and twelve copies along `w`. This file proves the bound
`v(l!) + val₁₂(l) ≤ S_p + 2 ∑ v(B_τ)` for every prime `p` and every degree `l` near the weights,
that is, with `κ(τ) ≤ l_τ ≤ κ(τ) + x ^ 42` at all places `τ`. Here `v` is the `p`-adic valuation,
`l! = ∏ l_τ!`, and `x = D.x` is the length of the prime sum.

## Main definitions and results

* `New.Parameters.resolutionForms`: the linear forms of a resolution, read in `ℂ_p`.
* `New.Data.isResolution_resolutionVectors`: a tight frame of length `M`, divided by an integer of
  `K` of norm `M`, is a resolution of the identity.
* `New.Data.leastValLE_six_zero_of_inert`: at an inert prime, `val₆(ν) ≤ 0` in all degrees.
* `New.Data.exists_hasNormalForm_resolutionForms`: at an inert prime the theta product along the
  frame has a normal form with unit leading coefficients.
* `New.Data.leastValLE_twelve`: `v(l!) + val₁₂(l) ≤ S_p + 2 ∑ v(B_τ)` for every prime `p`.

Notions from other files:
* `IsTightFrame w c M`: the `w_i` lie in the lattice `𝔞₀` of `E` and satisfy
  `∑ c_i σ(w_i) conj (τ(w_i)) = M δ_(σ τ)` for all places `σ`, `τ` of the CM type.
* `C.LeastValLE μ c n ν r`: `val_n(ν) ≤ r`, where `val_n(ν)` is the least valuation of a coefficient
  of degree `ν` in a product of `n` copies of `Θ = ∏ θ(μ_i z) ^ c_i` times integral series.
* `chiK P.d p`: the character of `K = ℚ(√-d)`; it is `1`, `-1`, `0` for split, inert, ramified `p`.
* `gammaPrime P.d p`, `partnerExponents P.d p`: the rate `γ_p`, and the set `I_p°` of exponents (the
  odd numbers if `p` is inert, all numbers if `p = d`); `I_p` consists of its positive elements.
* `D.weight τ`, `P.partner D.towerExp p e τ`: the weight `κ(τ)` and the partner `-p ^ e * τ` of a
  place `τ`.
* `l₀ = New.l₀ D.towerExp`: the range of exponents in which the `b`-places are sparse.
* `D.localPrimeSumTotal p`, `D.lossProduct l_τ`: the predicted valuation
  `S_p = ∑ D.localPrimeSum p κ(τ) τ`, and the product `B_τ` of the `n♯ = D.lossFactorCount` integers
  after `(l_τ - n♯)₊`.
* `P.cmCurve`: the curve `ℂ / Ω₀ 𝓞_K`, whose theta series is `θ`.
-/

/-!
## Least valuations along a tight frame at non-split primes

A prime that does not split in `K` does not divide `q₁ M`, where `q₁ = D.q₁`.
-/

section SharpnessFrame

open MvPowerSeries Finset Nat ComplexConjugate NumberField

namespace New
variable {p : ℕ} [Fact p.Prime]

/-- If `N y` is an algebraic integer for a natural number `N` prime to `p`, then `y` is integral at
all places above `p`. -/
lemma isIntegralAbove_of_isIntegral_mul {E : Type} [Field E] [CMType E] {N : ℕ} {y : E}
    (hN : ¬p ∣ N) (hy : IsIntegral ℤ (N * y)) : IsIntegralAbove p y := by
  intro v hv
  have hN_val : v.valuation E (N : E) = 1 := by
    rw [← map_natCast (algebraMap (𝓞 E) E), v.valuation_eq_one_iff_notMem]
    exact mt (v.natCast_mem_iff_dvd hv).1 hN
  have h_val : v.valuation E (N * y) ≤ 1 := v.valuation_le_one (⟨N * y, hy⟩ : 𝓞 E)
  rwa [map_mul, hN_val, one_mul] at h_val

variable [PadicPlace p] {J : Type} [Fintype J]

/-- Multiplying the linear forms `μ_j` by `s` turns the product `Θ(z) = ∏ θ(μ_j z) ^ m j` of copies
of the theta series of `C` into `Θ(s z)`. -/
lemma CMLattice.thetaProd_smul {d : ℕ} (C : CMLattice d) {X : Type} [Fintype X]
    (μ : J → X → ℂ_[p]) (m : J → ℕ) (s : ℂ_[p]) :
    C.thetaProd (s • μ) m = (C.thetaProd μ m).rescale fun _ : X ↦ s := by
  simp only [thetaProd, map_prod, map_pow, rescale_subst_linearSeries,
    subst_rescale_eq_subst_smul _ (.of_constantCoeff_zero (constantCoeff_linearSeries _))]
  simp [linearSeries, smul_sum, smul_smul]

/-- For a family `w` in the field `E = P.E s`, the linear forms `μ_i z = ∑ μ_(i τ) z_τ` with the
coefficients `μ_(i τ) = periodFactor * conj (τ (w i))` at the places `τ`, read in `ℂ_p` by the
homomorphism `ιₚ : ℂ → ℂ_p`. The complex number `periodFactor = P.periodFactor s` normalises the
Taylor series of theta functions. For a tight frame `w` of length `π π̄` these are the forms
`𝔰 u† z = 𝔰 ∑ conj (τ u) z_τ` of the resolution `u = w / π̄`, with `𝔰 = π * periodFactor`. -/
noncomputable def Parameters.resolutionForms (P : Parameters) (s : ℕ) (w : J → P.E s) (i : J)
    (x : P.Φ s × Unit) : ℂ_[p] :=
  ιₚ (P.periodFactor s * conj (New.Φ x.1 (w i)))

namespace Data

variable {P : Parameters}

/-- The vectors `u = w / π̄_M` of `E¹`, where the integer `π̄_M = D.piMBar` of `K` has norm
`M = D.M`. -/
noncomputable def resolutionVectors (D : Data P) (w : J → D.E) (i : J) (_ : Unit) : D.E :=
  w i / algebraMap P.K (P.E D.towerExp) D.piMBar

/-- The scale `𝔰 = periodFactor * π_M` of the Taylor series, read in `ℂ_p`, where `π_M` is the
conjugate of `D.piMBar`. -/
noncomputable def taylorScale (D : Data P) : ℂ_[p] :=
  ιₚ (P.periodFactor D.towerExp * conj (D.piMBar : ℂ))

lemma piMBar_mul_conj (D : Data P) : D.piMBar * conj (D.piMBar : ℂ) = D.M := by
  simpa [M] using congrArg (fun z : 𝓞 P.K ↦ (z : ℂ)) D.piMBar_mul_star

lemma coe_piMBar_ne_zero (D : Data P) : (D.piMBar : ℂ) ≠ 0 :=
  left_ne_zero_of_mul (D.piMBar_mul_conj.trans_ne (cast_ne_zero.2 (NeZero.ne D.M)))

/-- The period scale `π_M * jetScale` has the squared modulus `M / Ω`. Here `π_M` is the complex
conjugate of `D.piMBar`, `jetScale = periodFactor * √(2π / √d) / Ω₀` is the scale of the Taylor
series of theta functions, `M = D.M` is the level, and
`Ω = P.bigOmega D.towerExp = exp (γ - Re L′/L(1, χ_K)) * 2π / rd_E`, with `γ` Euler's constant and
`rd_E` the root discriminant of `E`. -/
lemma norm_conj_piMBar_mul_jetScale_sq (D : Data P) :
    ‖conj (D.piMBar : ℂ) * P.jetScale D.towerExp‖ ^ 2 = D.M / P.bigOmega D.towerExp := by
  have h_norm : ‖conj (D.piMBar : ℂ)‖ ^ 2 = D.M := by
    rw [Complex.norm_conj, ← Complex.normSq_eq_norm_sq]
    exact_mod_cast (Complex.mul_conj _).symm.trans D.piMBar_mul_conj
  rw [norm_mul, mul_pow, h_norm, P.norm_jetScale_sq, div_eq_mul_inv]

omit [Fintype J] in
lemma phi_resolutionVectors (D : Data P) {w : J → D.E} (τ : D.Φ) (i : J) :
    New.Φ τ (D.resolutionVectors w i ()) = New.Φ τ (w i) / D.piMBar := by
  rw [resolutionVectors, map_div₀, P.phi_algebraMap]

/-- Let `D` be admissible data for the parameters `P`, with the CM field `E = D.E`, a cyclotomic
extension of the imaginary quadratic field `K = ℚ(√-d)` (`d = P.d`), and the places `τ ∈ D.Φ` of
its CM type. Let `w` be a tight frame of length `M = D.M` with multiplicities `c`: the `w_i` lie in
the lattice `𝔞₀` of `E`, and `∑ c_i σ(w_i) conj (τ(w_i)) = M δ_(σ τ)` for all `σ, τ ∈ D.Φ`. Then
the vectors `u_i = w_i / π̄_M`, where the integer `π̄_M = D.piMBar` of `K` has norm `M`, are a
resolution of the identity: `z = ∑ c_i (u_i† z) u_i` for all complex vectors `z` indexed by the
places, where `u_i† z = ∑ conj (τ u_i) z_τ` is a sum over the places `τ`. -/
lemma isResolution_resolutionVectors (D : Data P) {w : J → D.E} {c : J → ℕ}
    (hw : IsTightFrame w c D.M) : IsResolution (D.resolutionVectors w) c := by
  rintro ⟨σ, ⟨⟩⟩ ⟨τ, ⟨⟩⟩
  have h_gram : ∑ i : J, c i * (New.Φ σ (w i) * conj (New.Φ τ (w i))) =
      if σ = τ then (D.M : ℂ) else 0 := hw.sum_mul_conj σ τ
  calc ∑ i : J, c i * (New.Φ σ (D.resolutionVectors w i ()) * dagger (D.resolutionVectors w i)
         (τ, ()))
      = (∑ i : J, c i * (New.Φ σ (w i) * conj (New.Φ τ (w i)))) / D.M := by
        simp only [sum_div, dagger, phi_resolutionVectors, map_div₀, _root_.div_mul_div_comm,
          piMBar_mul_conj, mul_div_assoc]
    _ = if (σ, ()) = (τ, ()) then 1 else 0 := by simp [h_gram, ite_div, NeZero.ne D.M]

omit [Fintype J] in
/-- The forms of `w` are the scale `𝔰 = D.taylorScale` times the forms `z ↦ u† z` of the vectors
`u_i = w_i / π̄_M`. -/
lemma resolutionForms_eq_smul (D : Data P) {w : J → D.E} :
    P.resolutionForms D.towerExp w = (D.taylorScale : ℂ_[p]) • daggerForms
      (D.resolutionVectors w) := by
  ext i ⟨τ, ⟨⟩⟩
  simp only [Parameters.resolutionForms, taylorScale, daggerForms, dagger, Pi.smul_apply,
    smul_eq_mul,
    phi_resolutionVectors, ← map_mul ιₚ, map_div₀ (starRingEnd ℂ)]
  rw [mul_assoc, mul_div_cancel₀ _ ((map_ne_zero _).2 D.coe_piMBar_ne_zero)]

/-- A prime `p` that does not split in `K` (`χ_K(p) ≠ 1`) does not divide `q₁ M`, where `q₁ = D.q₁`
is the order of the root of unity that generates `E` over `K` and the level `M = D.M` is the
product of the two primes `D.levelPrime i`. -/
lemma not_dvd_q₁_mul_M (D : Data P) (h_nonsplit : chiK P.d p ≠ 1) : ¬p ∣ D.q₁ * D.M := by
  have hp : p.Prime := Fact.out
  have h_level (i : Fin 2) : ¬p ∣ D.levelPrime i := fun h_dvd ↦ by
    obtain rfl : p = D.levelPrime i := (prime_dvd_prime_iff_eq hp (D.levelPrime_prime i)).1 h_dvd
    exact h_nonsplit (Parameters.chiK_eq_one_of_modEq_one (D.levelPrime_modEq_one i))
  exact hp.not_dvd_mul (fun h_dvd ↦ h_nonsplit (P.chiK_eq_one_of_dvd hp h_dvd))
    (hp.not_dvd_mul (h_level 0) (h_level 1))

/-- Let `D` be admissible data for the parameters `P`, with the CM field `E = D.E` over the
imaginary quadratic field `K = ℚ(√-d)` (`d = P.d`). Let `w` be a tight frame of length `M = D.M`
with multiplicities `c`: the `w_i` lie in the lattice `𝔞₀` of `E`, and
`∑ c_i σ(w_i) conj (τ(w_i)) = M δ_(σ τ)` for all places `σ`, `τ` of the CM type. Let `p` be a prime
that does not split in `K` (`χ_K(p) ≠ 1`). Then `u_i = w_i / π̄_M`, where `π̄_M = D.piMBar` has norm
`M`, is integral at every finite place `v` of `E` above `p`, that is, its `v`-adic absolute value is
at most `1`. -/
lemma isIntegralAbove_resolutionVectors (D : Data P) {w : J → D.E} {c : J → ℕ}
    (hw : IsTightFrame w c D.M) (h_nonsplit : chiK P.d p ≠ 1) (i : J) (x : Unit) :
    IsIntegralAbove p (D.resolutionVectors w i x) := by
  cases x
  -- `q₁ M u = (q₁ w) π_M`, and `q₁ w` is an integer because `q₁ 𝔞₀ ⊆ 𝓞 E`
  refine isIntegralAbove_of_isIntegral_mul (D.not_dvd_q₁_mul_M h_nonsplit) ?_
  have h_int : IsIntegral ℤ (D.q₁ * w i) := by
    refine algebraMap_mem_Ô.1 ?_
    have h_mem_Ô : (D.q₁ : 𝔸f D.E) * P.α D.towerExp * finiteImage w i ∈ Ô D.E :=
      mul_mem P.q₁_mul_alpha_mem (hw.finiteImage_mem i)
    -- `finiteImage w i = α⁻¹ w_i`, so the idele `α` of `𝔞₀` cancels
    simpa [mul_assoc, finiteImage, WeilData.α] using h_mem_Ô
  have h_eq : (D.q₁ * D.M : ℕ) * D.resolutionVectors w i () =
      D.q₁ * w i * algebraMap P.K (P.E D.towerExp) (star D.piMBar : 𝓞 P.K) := by
    apply (New.Φ (1 : D.Φ)).injective
    simp only [map_mul, map_natCast, cast_mul D.q₁, phi_resolutionVectors, P.phi_algebraMap,
      show ((star D.piMBar : 𝓞 P.K) : ℂ) = conj (D.piMBar : ℂ) by simp, ← piMBar_mul_conj]
    field [D.coe_piMBar_ne_zero]
  rw [h_eq]
  exact h_int.mul (RingOfIntegers.isIntegral_coe (star D.piMBar)).algebraMap

/-- Let `D` be admissible data for the parameters `P`: the CM field `E = D.E` is generated over
`K = ℚ(√-d)` by a root of unity of order `q₁ = D.q₁`, and the level `M = D.M` is the product of the
two primes `D.levelPrime i`. For every prime `p` that does not divide `q₁ M` the scale
`𝔰 = D.taylorScale` is a `p`-adic unit. The scale is the complex number `periodFactor * π_M`, read
in `ℂ_p` by the homomorphism `ιₚ : ℂ → ℂ_p` of `PadicPlace p`. -/
lemma norm_taylorScale_eq_one_of_not_dvd (D : Data P) (h_not_dvd : ¬p ∣ D.q₁ * D.M) :
    ‖(D.taylorScale : ℂ_[p])‖ = 1 := by
  have hp : p.Prime := Fact.out
  obtain ⟨hN₁, hM⟩ : ¬p ∣ D.q₁ ∧ ¬p ∣ D.M := not_or.1 (mt hp.dvd_mul.2 h_not_dvd)
  -- `π_M` and `π̄_M` are integers whose product `M` is a unit
  have h_prod : ‖ιₚ (D.piMBar : ℂ)‖ * ‖ιₚ (conj (D.piMBar : ℂ))‖ = 1 := by
    rw [← norm_mul, ← map_mul, piMBar_mul_conj, map_natCast]
    exact (hp.coprime_iff_not_dvd.2 hM).norm_natCast_eq_one _
  have h_le : ‖ιₚ (D.piMBar : ℂ)‖ ≤ 1 := norm_ringOfIntegers_le (ιₚ.comp P.K.subtype) D.piMBar
  have h_conj : ‖ιₚ (conj (D.piMBar : ℂ))‖ = 1 :=
    (norm_ringOfIntegers_le (ιₚ.comp ((starRingEnd ℂ).comp P.K.subtype)) D.piMBar).antisymm
      (h_prod.ge.trans (mul_le_of_le_one_left (norm_nonneg _) h_le))
  rw [taylorScale, map_mul, norm_mul, P.norm_iota_periodFactor_eq_one _ hN₁, h_conj, one_mul]

/-- The scale `𝔰 = D.taylorScale` is a `p`-adic unit for every prime `p` that does not split in `K`
(`χ_K(p) ≠ 1`). -/
lemma norm_taylorScale (D : Data P) (h_nonsplit : chiK P.d p ≠ 1) :
    ‖(D.taylorScale : ℂ_[p])‖ = 1 :=
  D.norm_taylorScale_eq_one_of_not_dvd (D.not_dvd_q₁_mul_M h_nonsplit)

/-- Let `D` be admissible data for the parameters `P`, `p` a prime that is inert in `K = ℚ(√-d)`,
and `w` a tight frame of length `M = D.M` with multiplicities `c`. Then `val₆(ν) ≤ 0` for every
degree `ν`, a multi-index over the places `τ ∈ D.Φ`. -/
lemma leastValLE_six_zero_of_inert (D : Data P) {w : J → D.E} {c : J → ℕ}
    (hw : IsTightFrame w c D.M) (h_inert : chiK P.d p = -1) (ν : D.Φ × Unit →₀ ℕ) :
    P.cmCurve.LeastValLE (p := p) (P.resolutionForms D.towerExp w) c 6 ν 0 := by
  have h_nonsplit : chiK P.d p ≠ 1 := by norm_num [h_inert]
  -- `∑ c_i τ(u_i) 𝔰 u_i† z = 𝔰 z_τ`, with integral coefficients `c_i τ(u_i)`
  let a (x : D.Φ × Unit) (i : J) : valRingCp p :=
    c i * ⟨ιₚ (New.Φ x.1 (D.resolutionVectors w i x.2)),
    (D.isIntegralAbove_resolutionVectors hw h_nonsplit i x.2).norm_le_one (ιₚ.comp (New.Φ x.1))⟩
  refine P.cmCurve.leastValLE_zero_of_span c (D.norm_taylorScale h_nonsplit) (a := a)
    (fun x y ↦ ?_) ν
  calc ∑ i, (a x i : ℂ_[p]) * P.resolutionForms D.towerExp w i y
      = D.taylorScale * ιₚ (∑ i, c i *
          (New.Φ x.1 (D.resolutionVectors w i x.2) * dagger (D.resolutionVectors w i) y)) := by
        simp [a, resolutionForms_eq_smul, daggerForms, mul_sum, mul_assoc, mul_left_comm]
    _ = if x = y then D.taylorScale else 0 := by
        simp [D.isResolution_resolutionVectors hw x y, apply_ite ιₚ]

/-- Let `D` be admissible data for the parameters `P` and `p` a prime that is inert in `K = ℚ(√-d)`.
For a tight frame `w` of length `M = D.M` with multiplicities `c`, the theta product
`Θ = ∏ θ(μ_i z) ^ c_i` of the curve `P.cmCurve` along the linear forms
`μ = P.resolutionForms D.towerExp w` has a normal form `Θ(ϖ z) = W exp (c_ϖ ∑ λ_(e j) Γ_e ^ p ^ j)`:
the series `W` in the variables `z_τ` and the numbers `λ_(e j) = lam e j` are integral,
`c_ϖ = ϖ ^ (p + 1) / p`, and `Γ_e` is the coupling `∑ z_τ ^ p ^ e * z_(-p ^ e * τ)` of the places
`τ` with their partners, for `e` in `partnerExponents P.d p`, the set of odd numbers. Moreover `ϖ`
has valuation `ρ_p = varpiValuation P.d p = 1 / (p² - 1)`, and `λ_(e 0)` is a unit for odd `e`. -/
lemma exists_hasNormalForm_resolutionForms (D : Data P) {w : J → D.E} {c : J → ℕ}
    (hw : IsTightFrame w c D.M) (h_inert : chiK P.d p = -1) :
    ∃ (ϖ : ℂ_[p]) (lam : ℕ → ℕ → valRingCp p),
      ‖ϖ‖ = p ^ (-varpiValuation P.d p) ∧
      (∀ e : ℕ, Odd e → IsUnit (lam e 0)) ∧
      HasNormalForm (partnerExponents P.d p) (P.partner D.towerExp p) ϖ lam
        (P.cmCurve.thetaProd (P.resolutionForms D.towerExp w) c) := by
  have h_nonsplit : chiK P.d p ≠ 1 := by norm_num [h_inert]
  obtain ⟨ϖ, lam, hϖ, h_lam_unit, h_form⟩ := P.exists_hasNormalForm D.towerExp h_nonsplit
  have hΘ : HasNormalForm (partnerExponents P.d p) (P.partner D.towerExp p) ϖ lam
      (P.cmCurve.thetaProd (daggerForms (D.resolutionVectors w)) c) := by
    simpa only [mul_one] using h_form (D.resolutionVectors w) c
      (D.isResolution_resolutionVectors hw)
      (D.isIntegralAbove_resolutionVectors hw h_nonsplit) 1 (one_mem _)
  -- the scale `𝔰` is a unit, so it keeps the `λ_(e 0)` units
  let 𝔰 : valRingCp p := ⟨D.taylorScale, (D.norm_taylorScale h_nonsplit).le⟩
  have h𝔰 : IsUnit 𝔰 := isUnit_integer_iff_norm_eq_one.2 (D.norm_taylorScale h_nonsplit)
  refine ⟨ϖ, fun e j ↦ 𝔰 ^ ((p ^ e + 1) * p ^ j) * lam e j, hϖ,
    fun e he ↦ (h𝔰.pow _).mul (h_lam_unit h_inert e he), ?_⟩
  rw [resolutionForms_eq_smul, CMLattice.thetaProd_smul]
  exact hΘ.rescale 𝔰

/-- If `w`, taken `c i` times, is a tight frame with frame bound `M = D.M` (`IsTightFrame w c D.M`),
then every coefficient of the forms `P.resolutionForms D.towerExp w` has `p`-adic norm at most `1`,
for every prime `p`. -/
lemma norm_resolutionForms_le_one (D : Data P) {w : J → D.E} {c : J → ℕ}
    (hw : IsTightFrame w c D.M) (i : J) (x : D.Φ × Unit) :
    ‖(P.resolutionForms D.towerExp w i x : ℂ_[p])‖ ≤ 1 :=
  Parameters.norm_periodFactor_mul_conj_le_one (hw.finiteImage_mem i) x.1

end Data

end New

end SharpnessFrame

/-!
## The valuation bound on twelve copies

For non-split `p`, six copies carry couplings and six supply the remaining degrees. The three cases
are split `p`, inert `p > k` (all places are coupled with exponent `1`) and non-split `p ≤ k` (the
couplings follow the near pairs `D.IsNearPair`). They cover all primes, as the ramified prime `d` is
at most `k = D.k`.
-/

section SharpnessCases

open MvPowerSeries Finset Nat New.Parameters New.CMLattice

namespace New.Data

variable {P : Parameters}

/-- The degree `l` is near the weights: `κ(τ) ≤ l_τ ≤ κ(τ) + x ^ 42` at every place `τ`, where
`l_τ = l (τ, ())`, `κ(τ) = D.weight τ` and `x = D.x`. -/
structure IsNearWeights (D : Data P) (l : D.Φ × Unit →₀ ℕ) : Prop where
  /-- The degree at `τ` is at least the weight `κ(τ)`. -/
  weight_le (τ : D.Φ) : (D.weight τ : ℝ) ≤ l (τ, ())
  /-- The degree at `τ` exceeds the weight `κ(τ)` by at most `x ^ 42`. -/
  le_weight_add (τ : D.Φ) : l (τ, ()) ≤ (D.weight τ : ℝ) + D.x ^ 42

/-- If the degree `l` is near the weights, that is, `κ(τ) ≤ l_τ ≤ κ(τ) + x ^ 42` at all places `τ`,
then each `l_τ` is at most `2 b`, where `b = D.b` is the weight at the `b`-places. -/
lemma le_two_mul_b (D : Data P) {l : D.Φ × Unit →₀ ℕ} (hl : D.IsNearWeights l)
    (place : D.Φ × Unit) : l place ≤ 2 * D.b :=
  (hl.le_weight_add place.1).trans (D.weight_add_x_pow_le_two_mul_b place.1)

/-- Let `p` be a prime with `D.k < p`, and let the degree `l` be near the weights. Then at each
place `τ` the number `⌊(l_τ - n♯)₊ / p⌋` is at most `n♯ = D.lossFactorCount = ⌈6 * D.b / D.k⌉`. -/
lemma div_le_lossFactorCount (D : Data P) {p : ℕ} [Fact p.Prime] {l : D.Φ × Unit →₀ ℕ}
    (hl : D.IsNearWeights l) (hk : D.k < p) (place : D.Φ × Unit) :
    (l place - D.lossFactorCount) / p ≤ D.lossFactorCount := by
  have hk_pos : (0 : ℝ) < D.k := mod_cast D.k_pos
  rw [← cast_le (α := ℝ)]
  calc (((l place - D.lossFactorCount) / p : ℕ) : ℝ) ≤ l place / p := by
        grw [cast_div_le, Nat.sub_le]
    _ ≤ 2 * D.b / D.k := by grw [D.le_two_mul_b hl, ← hk]
    _ ≤ 6 * D.b / D.k := by grw [show (2 : ℝ) ≤ 6 by norm_num]
    _ ≤ D.lossFactorCount := le_ceil _

/-- At a prime `p` that is inert in `ℚ(√-d)`, `d = P.d` (`χ_K(p) = -1`), the local prime sum
`D.localPrimeSum p κ(τ) τ = ∑ (κ(τ) / p ^ e - κ(-p ^ e * τ))₊` over odd `e` at a place `τ ∈ D.Φ` of
the CM type is at least its term for `e = 1`. -/
lemma posPart_le_localPrimeSum (D : Data P) {p : ℕ} [Fact p.Prime] (h_inert : chiK P.d p = -1)
    (τ : D.Φ) :
    (D.weight τ / p - D.weight (P.partner D.towerExp p 1 τ) : ℝ)⁺ ≤
      D.localPrimeSum p (D.weight τ) τ := by
  have h_ne : p ≠ P.d := ne_of_chiK_ne_zero (by simp [h_inert])
  let t (e : ℕ) : ℝ := if e ∈ positivePartnerExponents P.d p then
    (D.weight τ / p ^ e - D.weight (D.placeOfInt (-p ^ e) * τ))⁺ else 0
  calc _ = t 1 := by simp [t, partner, one_mem_positivePartnerExponents, h_inert]
    _ ≤ ∑' e : ℕ, t e :=
      (D.summable_posPart_sub_weight p (D.weight τ) τ).le_tsum 1 fun e _ ↦ by positivity
    _ = D.localPrimeSum p (D.weight τ) τ := by
      rw [localPrimeSum, piPrimeValuation_of_ne h_ne, one_mul]

/-- Let `p > D.k` be a prime that is inert in `ℚ(√-d)` and let the degrees `l_τ` lie between the
weights `κ(τ) = D.weight τ` and `κ(τ) + D.x ^ 42`. Put `i_τ = ⌊(l_τ - n♯)₊ / p⌋` with
`n♯ = D.lossFactorCount = ⌈6 b / k⌉`, and `j_τ = min i_τ l_(-p τ)` with the partner `-p τ` of `τ`.
Then `v(l_τ!) - j_τ` exceeds the local prime sum `D.localPrimeSum p κ(τ) τ = ∑ (κ(τ) / p ^ e - κ(-p
^ e τ))₊` (over odd `e`) by at most `2 v(B_τ)`. -/
lemma padicValNat_factorial_sub_min_le (D : Data P) {p : ℕ} [Fact p.Prime] {l : D.Φ × Unit →₀ ℕ}
    (hl : D.IsNearWeights l) (h_inert : chiK P.d p = -1) (hk : D.k < p) (τ : D.Φ) :
    (padicValNat p (l (τ, ()))! : ℝ) -
        (min ((l (τ, ()) - D.lossFactorCount) / p) (l (P.partner D.towerExp p 1 τ, ())) : ℕ) ≤
      D.localPrimeSum p (D.weight τ) τ + 2 * padicValNat p (D.lossProduct (l (τ, ()))) := by
  set i : ℕ := (l (τ, ()) - D.lossFactorCount) / p with hi
  set B : ℕ := D.lossProduct (l (τ, ()))
  have h_fact : padicValNat p i ! ≤ padicValNat p B :=
    (padicValNat_mono_of_dvd (factorial_dvd_factorial (D.div_le_lossFactorCount hl hk _))
      (factorial_ne_zero _)).trans (D.padicValNat_factorial_lossFactorCount_le _)
  have h_val : padicValNat p (l (τ, ()))! ≤ i + 2 * padicValNat p B :=
    calc _ ≤ padicValNat p (l (τ, ()) - D.lossFactorCount)! + padicValNat p B :=
          D.padicValNat_factorial_le_add_lossProduct _
      _ = i + padicValNat p i ! + padicValNat p B := by rw [padicValNat_factorial_eq_div_add]
      _ ≤ i + 2 * padicValNat p B := by lia
  have h_sub_le_weight : ((l (τ, ()) - D.lossFactorCount : ℕ) : ℝ) ≤ D.weight τ := by
    rw [cast_le, tsub_le_iff_right, ← cast_le (α := ℝ), cast_add]
    linarith [hl.le_weight_add τ, D.x_pow_le_lossFactorCount]
  have h_quot : (i : ℝ) ≤ D.weight τ / p := by grw [hi, cast_div_le, h_sub_le_weight]
  have h_min : (i : ℝ) - (min i (l (P.partner D.towerExp p 1 τ, ())) : ℕ) ≤
      (D.weight τ / p - D.weight (P.partner D.towerExp p 1 τ) : ℝ)⁺ := by
    rw [cast_min, ← max_sub_sub_left, sub_self]
    exact max_le (posPart_nonneg _) ((sub_le_sub h_quot (hl.weight_le _)).trans (le_posPart _))
  rw [← cast_le (α := ℝ), cast_add, cast_mul, cast_ofNat] at h_val
  linarith [D.posPart_le_localPrimeSum h_inert τ]

/-- The errors in Legendre's formula. Let `p ≥ 3` be prime, `v` the `p`-adic valuation, and let
`l = ν' + ν'' + η` be a degree within `D.x ^ 42` above the weights `D.weight`. Then `v(l!)` exceeds
`v(ν'! ν''! η!)` by at most `3 f (log b + 2)`, where `f = D.f` is the number of infinite places and
`log b = D.logB` is the logarithm of the weight `b = D.b` at the `b`-places; the number
`3 (log b + 2)` bounds the valuation of a multinomial coefficient. -/
lemma sum_padicValNat_factorial_le_add (D : Data P) {p : ℕ} [Fact p.Prime] {l : D.Φ × Unit →₀ ℕ}
    (hl : D.IsNearWeights l) (hp3 : 3 ≤ p) {ν' ν'' η : D.Φ × Unit →₀ ℕ}
    (h_decomp : l = ν' + ν'' + η) :
    ∑ x : D.Φ × Unit, (padicValNat p (l x)! : ℝ) ≤
      ∑ x : D.Φ × Unit, (padicValNat p (ν' x)! : ℝ) +
        ∑ x : D.Φ × Unit, (padicValNat p (ν'' x)! : ℝ) +
        ∑ x : D.Φ × Unit, (padicValNat p (η x)! : ℝ) + 3 * D.f * (D.logB + 2) := by
  subst h_decomp
  have h_place (x : D.Φ × Unit) : (padicValNat p ((ν' + ν'' + η) x)! : ℝ) ≤
      padicValNat p (ν' x)! + padicValNat p (ν'' x)! + padicValNat p (η x)! + 3 * (D.logB + 2) :=
    D.padicValNat_factorial_add_add_le hp3 (D.le_two_mul_b hl x)
  refine (sum_le_sum fun x _ ↦ h_place x).trans_eq ?_
  simp [sum_add_distrib, mul_left_comm, mul_assoc]

/-- Comparison with the predicted valuation `S_p = D.localPrimeSumTotal p`, the sum over the
places `τ` of `v(π_p) ∑ (κ(τ) / p ^ e - κ(-p ^ e τ))₊` over `e ∈ I_p`, where `κ = D.weight` and
`v(π_p)` is `1/2` for `p = d` and `1` otherwise. The set `I_p` consists of the odd numbers if `p`
is inert in `ℚ(√-d)`, of all positive numbers if `p = d`, and is empty if `p` splits. Let
`p ≤ k = D.k` be a prime and `l` a degree with `κ(τ) ≤ l_τ ≤ κ(τ) + x ^ 42`, `x = D.x`. Suppose
every near pair `(τ, e')` has `e' = e τ` and `j τ = ⌊l_τ / p ^ e'⌋`; near means that `e' ∈ I_p`,
that `e' < l₀ / 2`, where `l₀` is the least power of `3` above `27 * D.towerExp`, and that `τ`
and its partner `-p ^ e' * τ` are `b`-places, that is, lie in `D.bPlaces`, where the weight is
`b = D.b`. Then `γ_p |l| - |j| + 3 f (log b + 2) ≤ S_p + ∑ v(B_τ)`, where
`γ_p = gammaPrime P.d p` is `0`, `p / (p² - 1)`, `1 / (2 p - 2)` for split, inert, ramified `p`,
`f = D.f` is the number of infinite places, `log b = D.logB` and `B_τ = D.lossProduct l_τ` is the
product of the `n♯ = D.lossFactorCount` integers after `(l_τ - n♯)₊`. -/
lemma gammaPrime_mul_degree_sub_le_localPrimeSumTotal_add (D : Data P) {p : ℕ} [Fact p.Prime]
    {l : D.Φ × Unit →₀ ℕ} (hl : D.IsNearWeights l) (hk : p ≤ D.k) {e j : D.Φ → ℕ}
    (h_exponent : ∀ (τ : D.Φ) (e' : ℕ), D.IsNearPair p τ e' → e' = e τ)
    (h_floor : ∀ (τ : D.Φ) (e' : ℕ), D.IsNearPair p τ e' → j τ = l (τ, ()) / p ^ e') :
    gammaPrime P.d p * l.degree - ∑ τ : D.Φ, (j τ : ℝ) + 3 * D.f * (D.logB + 2) ≤
      D.localPrimeSumTotal p + ∑ τ : D.Φ, (padicValNat p (D.lossProduct (l (τ, ()))) : ℝ) := by
  set γ : ℝ := gammaPrime P.d p
  have hγ : γ ≤ 1 := gammaPrime_le_one P.d p
  have h_excess : γ * l.degree ≤ γ * ∑ τ : D.Φ, (D.weight τ : ℝ) + ∑ _τ : D.Φ, D.x ^ 42 := by
    simp only [Finsupp.degree_eq_sum, cast_sum, Fintype.sum_prod_type, Fintype.sum_unique, mul_sum,
      ← sum_add_distrib]
    refine sum_le_sum fun τ _ ↦ ?_
    linarith [hl.le_weight_add τ, mul_le_of_le_one_left (sub_nonneg.2 (hl.weight_le τ)) hγ]
  have h_weights_sub_predicted :
      γ * ∑ τ : D.Φ, (D.weight τ : ℝ) - D.localPrimeSumTotal p ≤ ∑ τ : D.Φ, D.partnerMinSum p τ :=
    (D.mul_sum_weight_sub_localPrimeSumTotal p).trans_le <|
      mul_le_of_le_one_left (sum_nonneg fun τ _ ↦ D.partnerMinSum_nonneg τ)
        (piPrimeValuation_le_one P.d p)
  have h_place (τ : D.Φ) : 3 * (D.logB + 2) + D.x ^ 42 + D.partnerMinSum p τ - j τ ≤
      padicValNat p (D.lossProduct (l (τ, ()))) := by
    have h_min : D.partnerMinSum p τ ≤ j τ + 1 + l₀ D.towerExp * (D.a / D.x₁) + 2 * D.b /
      (D.k * p) := by
      refine D.partnerMinSum_le (e₀ := e τ) (cast_nonneg _) fun e' he' ↦ ⟨h_exponent τ e' he', ?_⟩
      calc (D.weight τ : ℝ) / p ^ e' ≤ l (τ, ()) / (p ^ e' : ℕ) := by grw [hl.weight_le τ, cast_pow]
        _ ≤ j τ + 1 := by grw [h_floor τ e' he', ← floor_div_eq_div (K := ℝ), ← lt_floor_add_one]
    linarith [D.error_le_padicValNat_lossProduct hk (l (τ, ()))]
  have h_sum : ∑ τ : D.Φ, (3 * (D.logB + 2) + D.x ^ 42 + D.partnerMinSum p τ - j τ) ≤
      ∑ τ : D.Φ, (padicValNat p (D.lossProduct (l (τ, ()))) : ℝ) :=
    sum_le_sum fun τ _ ↦ h_place τ
  have h_count : ∑ _τ : D.Φ, 3 * (D.logB + 2) = 3 * D.f * (D.logB + 2) := by
    simp [mul_left_comm, mul_assoc]
  simp only [sum_sub_distrib, sum_add_distrib, h_count] at h_sum
  linarith

/-- Let `p` be a prime that does not split in `ℚ(√-d)` and is at most `k = D.k = r + 1 - m` (the
rank of the source, for the ranks `m`, `r` of the data), and let `(τ, e τ)` be a near pair for each
`τ ∈ Φ₀`: `e τ < l₀ / 2`, with `l₀` the least power of `3` above `27 * D.towerExp`; `e τ` lies in
the set `I_p`; and `τ` and its partner `-p ^ e τ * τ` are `b`-places. Then `Φ₀` and `e` are a family
of couplings: the exponents are odd, and no other pair `(τ₁, e')` with `τ₁ ∈ Φ₀` and odd `e' ≤ e τ`
has the partner of `(τ, e τ)`. -/
lemma isCouplingFamily_of_isNearPair (D : Data P) {p : ℕ} [hp : Fact p.Prime]
    (h_nonsplit : chiK P.d p ≠ 1) (hk : p ≤ D.k) {Φ₀ : Finset D.Φ} {e : D.Φ → ℕ}
    (he : ∀ τ ∈ Φ₀, D.IsNearPair p τ (e τ)) :
    IsCouplingFamily (P.partner D.towerExp p) Φ₀ e := by
  refine ⟨fun τ hτ ↦ (he τ hτ).odd, fun τ hτ τ₁ hτ₁ e' he' h_odd h_end ↦ ?_⟩
  -- The pair `(τ₁, e')` is near, with the same end as `(τ, e τ)`.
  have h_pair : D.IsNearPair p τ₁ e' :=
    { exponent_mem := ⟨h_odd.pos, .inr ⟨(he τ hτ).inert, h_odd⟩⟩
      two_mul_lt := (Nat.mul_le_mul_left 2 he').trans_lt (he τ hτ).two_mul_lt
      start_mem := (he τ₁ hτ₁).start_mem
      end_mem := by simpa only [h_end] using (he τ hτ).end_mem }
  exact h_pair.eq_and_eq_of_partner_eq hp.out h_nonsplit hk (he τ hτ) h_end

/-- Let `p ≤ k = D.k` be a prime that does not split in `ℚ(√-d)` and `l` a degree between the
weights `κ(τ) = D.weight τ` and `κ(τ) + x ^ 42`, `x = D.x`. For each `τ ∈ Φ₀` let `(τ, e τ)` be a
near pair. Then the couplings `z_τ ^ p ^ e τ * z_(-p ^ e τ * τ)`, each used `j τ = ⌊l_τ / p ^ e τ⌋`
times, have total degree at most `l`; `powerDegree` and `partnerDegree` are the degrees of the first
and of the second factors. -/
lemma powerDegree_add_partnerDegree_le_of_isNearPair (D : Data P) {p : ℕ} [hp : Fact p.Prime]
    {l : D.Φ × Unit →₀ ℕ} (hl : D.IsNearWeights l) (h_nonsplit : chiK P.d p ≠ 1) (hk : p ≤ D.k)
    {Φ₀ : Finset D.Φ} {e j : D.Φ → ℕ} (he : ∀ τ ∈ Φ₀, D.IsNearPair p τ (e τ))
    (hj : ∀ τ ∈ Φ₀, j τ = l (τ, ()) / p ^ e τ) :
    powerDegree p Φ₀ e j + partnerDegree (P.partner D.towerExp p) Φ₀ e j ≤ l := by
  classical
  rintro ⟨t, ⟨⟩⟩
  rw [Finsupp.add_apply, partnerDegree_apply]
  set ends : Finset D.Φ := {τ ∈ Φ₀ | P.partner D.towerExp p (e τ) τ = t}
  by_cases ht : t ∈ Φ₀
  · -- A start is not an end.
    have h_zero : ∑ τ ∈ ends, j τ = 0 := sum_eq_zero fun τ hτ ↦
      absurd (mem_filter.1 hτ).2
        ((he τ (mem_filter.1 hτ).1).end_ne_start hp.out h_nonsplit hk (he t ht))
    simpa [powerDegree_apply_of_mem ht, hj t ht, h_zero] using mul_div_le _ _
  rw [powerDegree_apply_of_notMem ht, zero_add]
  rcases ends.eq_empty_or_nonempty with h_empty | ⟨τ, hτ⟩
  · simp [h_empty]
  -- At the end of the one near pair `(τ, e τ)` the degree is `j τ ≤ 2 b / p ^ e τ ≤ b ≤ l t`.
  obtain ⟨hτ₀, h_end⟩ := mem_filter.1 hτ
  have h_single : ∑ τ' ∈ ends, j τ' = j τ := by
    refine sum_eq_single_of_mem τ hτ fun τ' hτ' hne ↦ ?_
    obtain ⟨hτ'₀, h_end'⟩ := mem_filter.1 hτ'
    exact absurd ((he τ' hτ'₀).eq_and_eq_of_partner_eq hp.out h_nonsplit hk (he τ hτ₀)
      (h_end'.trans h_end.symm)).1 hne
  have h_pow : (2 : ℝ) ≤ p ^ e τ :=
    mod_cast hp.out.two_le.trans (le_self_pow (he τ hτ₀).pos.ne' p)
  have h_end_bPlace : t ∈ D.bPlaces := by simpa only [h_end] using (he τ hτ₀).end_mem
  rw [h_single, ← cast_le (α := ℝ)]
  calc (j τ : ℝ) ≤ 2 * D.b / 2 := by
        grw [hj τ hτ₀, cast_div_le, D.le_two_mul_b hl, cast_pow, ← h_pow]
    _ ≤ D.weight t := by linarith [D.b_le_weight h_end_bPlace]
    _ ≤ l (t, ()) := hl.weight_le t

/-- The map `τ ↦ -p ^ e * τ` from a place to its partner is a bijection. -/
lemma partner_bijective (D : Data P) (p e : ℕ) : Function.Bijective (P.partner D.towerExp p e) :=
  Group.mulLeft_bijective (P.placeOfInt D.towerExp (-p ^ e))

/-- Let `p` be a prime greater than `k = D.k`, and `l` a degree between the weights
`κ(τ) = D.weight τ` and `κ(τ) + x ^ 42`, `x = D.x`. The couplings `z_τ ^ p * z_(-p τ)` at all places
`τ` are used `j τ = min ⌊(l_τ - n♯)₊ / p⌋ l_(-p τ)` times each. Together they have total degree at
most `l`. -/
lemma powerDegree_add_partnerDegree_le_of_k_lt (D : Data P) {p : ℕ} [Fact p.Prime]
    {l : D.Φ × Unit →₀ ℕ} (hl : D.IsNearWeights l) (hk : D.k < p) {j : D.Φ → ℕ}
    (hj : ∀ τ : D.Φ, j τ = min ((l (τ, ()) - D.lossFactorCount) / p)
      (l (P.partner D.towerExp p 1 τ, ()))) :
    powerDegree p univ 1 j + partnerDegree (P.partner D.towerExp p) univ 1 j ≤ l := by
  classical
  -- At `t = -p τ` the two degrees add up to `p j_t + j_τ ≤ (l_t - n♯)₊ + min n♯ l_t = l_t`.
  rintro ⟨t, ⟨⟩⟩
  obtain ⟨τ, rfl⟩ := (D.partner_bijective p 1).surjective t
  have h_power : p * j (P.partner D.towerExp p 1 τ) ≤
      l (P.partner D.towerExp p 1 τ, ()) - D.lossFactorCount := by grw [hj, min_le_left, mul_div_le]
  have h_partner : j τ ≤ min D.lossFactorCount (l (P.partner D.towerExp p 1 τ, ())) := by
    grw [hj, D.div_le_lossFactorCount hl hk (τ, ())]
  have h_end : partnerDegree (P.partner D.towerExp p) univ 1 j (P.partner D.towerExp p 1 τ, ()) =
      j τ := by
    simp [partnerDegree_apply, (D.partner_bijective p 1).injective.eq_iff, filter_eq']
  rw [Finsupp.add_apply, powerDegree_apply_of_mem (mem_univ _), h_end, Pi.one_apply, pow_one]
  lia

/-- Let `D` be admissible data for the parameters `P`, `p` a prime that splits in `ℚ(√-d)`
(`d = P.d`), `w` vectors of `D.E` with multiplicities `c`, and suppose that the linear form of
`w i₀` has unit coefficients in `ℂ_p` at all places `τ ∈ D.Φ`. Then `v(l!) + val₁₂(l) ≤ S_p` for
every degree `l`, and `S_p = D.localPrimeSumTotal p` is zero. -/
lemma leastValLE_twelve_of_split (D : Data P) {p : ℕ} [Fact p.Prime] {l : D.Φ × Unit →₀ ℕ}
    [PadicPlace p] {J : Type} [Fintype J] {w : J → D.E} {c : J → ℕ}
    {i₀ : J} (h_unit : ∀ x : D.Φ × Unit, ‖(P.resolutionForms D.towerExp w i₀ x : ℂ_[p])‖ = 1)
    (h_split : chiK P.d p = 1) :
    P.cmCurve.LeastValLE (p := p) (P.resolutionForms D.towerExp w) c 12 l
      (D.localPrimeSumTotal p - ∑ x : D.Φ × Unit, (padicValNat p (l x)! : ℝ)) := by
  have hS : D.localPrimeSumTotal p = 0 := by
    simp [localPrimeSumTotal, localPrimeSum, positivePartnerExponents_of_split h_split]
  have h_six : P.cmCurve.LeastValLE (p := p) (P.resolutionForms D.towerExp w) c 6 l
      (0 - ∑ x : D.Φ × Unit, (padicValNat p (l x)! : ℝ)) := by
    simpa only [gammaPrime_of_split h_split, zero_mul] using
      P.cmCurve.leastValLE_of_unit_coefficients c h_unit l
  simpa only [hS, zero_add] using (leastValLE_zero (n := 6)).add h_six

/-- Let `D` be admissible data for the parameters `P` and `p` a prime above `k = D.k = r + 1 - m`
that is inert in `ℚ(√-d)`, `d = P.d`. Let `w` be a tight frame of length `M = D.M` with
multiplicities `c`, and `l` a degree between the weights `κ(τ) = D.weight τ` and `κ(τ) + x ^ 42`.
Then `v(l!) + val₁₂(l) ≤ S_p + 2 ∑ v(B_τ)`. -/
lemma leastValLE_twelve_of_lt (D : Data P) {p : ℕ} [hp : Fact p.Prime] {l : D.Φ × Unit →₀ ℕ}
    (hl : D.IsNearWeights l) [PadicPlace p] {J : Type} [Fintype J] {w : J → D.E} {c : J → ℕ}
    (hw : IsTightFrame w c D.M) (h_inert : chiK P.d p = -1) (hk : D.k < p) :
    P.cmCurve.LeastValLE (p := p) (P.resolutionForms D.towerExp w) c 12 l
      (D.localPrimeSumTotal p + 2 * ∑ x : D.Φ × Unit, (padicValNat p (D.lossProduct (l x)) : ℝ) -
        ∑ x : D.Φ × Unit, (padicValNat p (l x)! : ℝ)) := by
  have h13 : 13 ≤ p := P.thirteen_le_of_chiK_ne_one hp.out (by norm_num [h_inert])
  let j (τ : D.Φ) : ℕ := min ((l (τ, ()) - D.lossFactorCount) / p)
    (l (P.partner D.towerExp p 1 τ, ()))
  -- All places are coupled with `e_τ = 1`; this is allowed as `τ ↦ -p τ` is a bijection.
  have h_family : IsCouplingFamily (P.partner D.towerExp p) univ 1 := by
    refine ⟨fun _ _ ↦ odd_one, fun τ _ τ₁ _ e' he' h_odd h_end ↦ ?_⟩
    obtain rfl : e' = 1 := le_antisymm he' h_odd.pos
    exact ⟨(D.partner_bijective p 1).injective h_end, rfl⟩
  obtain ⟨η, h_decomp⟩ :=
    exists_add_of_le (D.powerDegree_add_partnerDegree_le_of_k_lt (j := j) hl hk fun _ ↦ rfl)
  obtain ⟨ϖ, lam, hϖ, h_lam_unit, h_normal⟩ :=
    D.exists_hasNormalForm_resolutionForms (p := p) hw h_inert
  have h_couple : P.cmCurve.LeastValLE (p := p) (P.resolutionForms D.towerExp w) c 6
      (powerDegree p univ 1 j + partnerDegree (P.partner D.towerExp p) univ 1 j)
        (-∑ τ : D.Φ, (j τ : ℝ)) :=
    (P.cmCurve.leastValLE_six_of_isCouplingFamily h_inert (by lia)
      (D.norm_resolutionForms_le_one hw) hϖ h_lam_unit h_normal h_family j).1
  -- The last six copies supply the remaining degree `η` at valuation at most `0`.
  have h_twelve : P.cmCurve.LeastValLE (p := p) (P.resolutionForms D.towerExp w) c 12 l
      (-∑ τ : D.Φ, (j τ : ℝ)) := by
    simpa only [h_decomp, add_zero] using
      h_couple.add (D.leastValLE_six_zero_of_inert hw h_inert η)
  refine h_twelve.mono ?_
  have h_sum : ∑ τ : D.Φ, (padicValNat p (l (τ, ()))! : ℝ) - ∑ τ : D.Φ, (j τ : ℝ) ≤
      D.localPrimeSumTotal p + 2 * ∑ τ : D.Φ, (padicValNat p (D.lossProduct (l (τ, ()))) : ℝ) := by
    rw [localPrimeSumTotal, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    exact sum_le_sum fun τ _ ↦ D.padicValNat_factorial_sub_min_le hl h_inert hk τ
  simp only [Fintype.sum_prod_type, Fintype.sum_unique]
  linarith

/-- For primes `p ≠ d`, the Legendre symbol `chiK d p = (p / d)` is `-1` unless it is `1`. -/
lemma _root_.New.chiK_eq_neg_one_of_ne {d : ℕ} [Fact d.Prime] {p : ℕ} [Fact p.Prime]
    (h_ne : p ≠ d) (h_nonsplit : chiK d p ≠ 1) : chiK d p = -1 := by
  simpa [h_ne, h_nonsplit] using chiK_cases d p

/-- Let `D` be admissible data for the parameters `P`, `p` a prime with `2 < p ≤ k = D.k` that does
not split in `ℚ(√-d)`, `w` a tight frame of length `M = D.M` with multiplicities `c`, and `(τ, e τ)`
a near pair for each `τ ∈ Φ₀`: `e τ` lies in `I_p`, `e τ < l₀ / 2` with `l₀` the least power of `3`
above `27 * D.towerExp`, and `τ` and its partner `-p ^ e τ * τ` lie in the set `D.bPlaces` of places
of weight `b`. Let `ν'`, `ν''` be the degrees of the two factors of the couplings
`z_τ ^ p ^ e τ * z_(-p ^ e τ * τ)`, used `j τ` times. Let `val₆(ν)` be the least valuation of a
coefficient of total degree `ν = ν' + ν''` in a product of six copies of series `H Θ`, with `Θ` the
theta product along the forms `P.resolutionForms D.towerExp w` and `H` integral. Then
`v(ν'! ν''!) + val₆(ν) ≤ γ_p |ν| - |j|`. -/
lemma leastValLE_six_of_isNearPair (D : Data P) {p : ℕ} [Fact p.Prime] [PadicPlace p]
    {J : Type} [Fintype J] {w : J → D.E} {c : J → ℕ} (hw : IsTightFrame w c D.M)
    (h_nonsplit : chiK P.d p ≠ 1) (hp2 : 2 < p) (hk : p ≤ D.k) {Φ₀ : Finset D.Φ} {e : D.Φ → ℕ}
    (he : ∀ τ ∈ Φ₀, D.IsNearPair p τ (e τ)) (j : D.Φ → ℕ) :
    P.cmCurve.LeastValLE (p := p) (P.resolutionForms D.towerExp w) c 6
      (powerDegree p Φ₀ e j + partnerDegree (P.partner D.towerExp p) Φ₀ e j)
      (gammaPrime P.d p *
          (powerDegree p Φ₀ e j + partnerDegree (P.partner D.towerExp p) Φ₀ e j).degree -
        ∑ τ ∈ Φ₀, (j τ : ℝ) - ∑ x : D.Φ × Unit, (padicValNat p (powerDegree p Φ₀ e j x)! : ℝ) -
        ∑ x : D.Φ × Unit,
          (padicValNat p (partnerDegree (P.partner D.towerExp p) Φ₀ e j x)! : ℝ)) := by
  rcases Φ₀.eq_empty_or_nonempty with rfl | ⟨τ, hτ⟩
  · -- Without near pairs, in particular for `p = d`, the degree is `0`.
    simpa [powerDegree, partnerDegree] using leastValLE_zero
  have h_inert : chiK P.d p = -1 := (he τ hτ).inert
  obtain ⟨ϖ, lam, hϖ, h_lam_unit, h_normal⟩ :=
    D.exists_hasNormalForm_resolutionForms (p := p) hw h_inert
  exact (P.cmCurve.leastValLE_six_of_isCouplingFamily h_inert hp2 (D.norm_resolutionForms_le_one hw)
    hϖ h_lam_unit h_normal (D.isCouplingFamily_of_isNearPair h_nonsplit hk he) j).2

/-- Let `D` be admissible data for the parameters `P`, with the CM field `E = D.E` and its places
`τ ∈ D.Φ`, and `p ≤ k = D.k` a prime that does not split in `ℚ(√-d)`, `d = P.d`, with `ℂ` read in
`ℂ_p` by the homomorphism `ιₚ` of `PadicPlace p`. Let `w` be a tight frame of length `M = D.M` with
multiplicities `c` such that the form of `w i₀` has unit coefficients, and `l` a degree between the
weights `κ(τ) = D.weight τ` and `κ(τ) + x ^ 42`. Then `v(l!) + val₁₂(l) ≤ S_p + ∑ v(B_τ)`. -/
lemma leastValLE_twelve_localPrimeSumTotal_of_le (D : Data P) {p : ℕ} [hp : Fact p.Prime]
    {l : D.Φ × Unit →₀ ℕ}
    (hl : D.IsNearWeights l) [PadicPlace p] {J : Type} [Fintype J] {w : J → D.E} {c : J → ℕ}
    (hw : IsTightFrame w c D.M)
    {i₀ : J} (h_unit : ∀ x : D.Φ × Unit, ‖(P.resolutionForms D.towerExp w i₀ x : ℂ_[p])‖ = 1)
    (h_nonsplit : chiK P.d p ≠ 1) (hk : p ≤ D.k) :
    P.cmCurve.LeastValLE (p := p) (P.resolutionForms D.towerExp w) c 12 l
      (D.localPrimeSumTotal p + ∑ x : D.Φ × Unit, (padicValNat p (D.lossProduct (l x)) : ℝ) -
        ∑ x : D.Φ × Unit, (padicValNat p (l x)! : ℝ)) := by
  classical
  have h13 : 13 ≤ p := P.thirteen_le_of_chiK_ne_one hp.out h_nonsplit
  -- `Φ₀` is the set of starts of near pairs `(τ, e τ)`; each is coupled `⌊l_τ / p ^ e τ⌋` times.
  let Φ₀ : Finset D.Φ := {τ | ∃ e : ℕ, D.IsNearPair p τ e}
  have h_start : ∀ τ ∈ Φ₀, ∃ e : ℕ, D.IsNearPair p τ e := fun τ hτ ↦ (mem_filter.1 hτ).2
  choose! e he using h_start
  let j (τ : D.Φ) : ℕ := if τ ∈ Φ₀ then l (τ, ()) / p ^ e τ else 0
  have hj_mem : ∀ τ ∈ Φ₀, j τ = l (τ, ()) / p ^ e τ := fun τ hτ ↦ ite_eq_left hτ
  have h_mem {τ : D.Φ} {e' : ℕ} (h_near : D.IsNearPair p τ e') : τ ∈ Φ₀ :=
    mem_filter.2 ⟨mem_univ τ, e', h_near⟩
  have h_exponent (τ : D.Φ) (e' : ℕ) (h_near : D.IsNearPair p τ e') : e' = e τ :=
    h_near.exponent_unique hp.out h_nonsplit hk (he τ (h_mem h_near))
  have h_floor (τ : D.Φ) (e' : ℕ) (h_near : D.IsNearPair p τ e') : j τ = l (τ, ()) / p ^ e' := by
    rw [h_exponent τ e' h_near, hj_mem τ (h_mem h_near)]
  set ν' : D.Φ × Unit →₀ ℕ := powerDegree p Φ₀ e j
  set ν'' : D.Φ × Unit →₀ ℕ := partnerDegree (P.partner D.towerExp p) Φ₀ e j
  obtain ⟨η, h_decomp⟩ :=
    exists_add_of_le (D.powerDegree_add_partnerDegree_le_of_isNearPair hl h_nonsplit hk he hj_mem)
  set γ : ℝ := gammaPrime P.d p
  let v (ν : D.Φ × Unit →₀ ℕ) : ℝ := ∑ x : D.Φ × Unit, (padicValNat p (ν x)! : ℝ)
  have h_couple : P.cmCurve.LeastValLE (p := p) (P.resolutionForms D.towerExp w) c 6 (ν' + ν'')
      (γ * (ν' + ν'').degree - ∑ τ ∈ Φ₀, (j τ : ℝ) - v ν' - v ν'') :=
    D.leastValLE_six_of_isNearPair hw h_nonsplit (by lia) hk he j
  -- The last six copies supply the remaining degree `η` at the rate `γ`.
  have h_twelve : P.cmCurve.LeastValLE (p := p) (P.resolutionForms D.towerExp w) c 12 l
      (γ * l.degree - ∑ τ : D.Φ, (j τ : ℝ) - v ν' - v ν'' - v η) := by
    have h_j : ∑ τ ∈ Φ₀, (j τ : ℝ) = ∑ τ : D.Φ, (j τ : ℝ) :=
      sum_subset (subset_univ _) fun τ _ hτ ↦ cast_eq_zero.2 (ite_eq_right hτ)
    rw [← h_j, h_decomp]
    refine (h_couple.add (P.cmCurve.leastValLE_of_unit_coefficients c h_unit η)).mono (le_of_eq ?_)
    rw [map_add _ _ η, cast_add]
    ring
  -- Replace `l!` by `ν'! ν''! η!`.
  have h_legendre : v l ≤ v ν' + v ν'' + v η + 3 * D.f * (D.logB + 2) :=
    D.sum_padicValNat_factorial_le_add hl (by lia) h_decomp
  have h_compare : γ * l.degree - ∑ τ : D.Φ, (j τ : ℝ) + 3 * D.f * (D.logB + 2) ≤
      D.localPrimeSumTotal p + ∑ x : D.Φ × Unit, (padicValNat p (D.lossProduct (l x)) : ℝ) := by
    simpa [Fintype.sum_prod_type] using
      D.gammaPrime_mul_degree_sub_le_localPrimeSumTotal_add hl hk h_exponent h_floor
  exact h_twelve.mono (by linarith)

/-- Let `w` be a tight frame of length `M = D.M` with multiplicities `c` such that the form of
`w i₀` has unit coefficients, and let `l` be a degree between the weights `κ(τ) = D.weight τ` and
`κ(τ) + x ^ 42`. Then `v(l!) + val₁₂(l) ≤ S_p + 2 ∑ v(B_τ)`. -/
lemma leastValLE_twelve (D : Data P) {p : ℕ} [Fact p.Prime] {l : D.Φ × Unit →₀ ℕ}
    (hl : D.IsNearWeights l) [PadicPlace p] {J : Type} [Fintype J] {w : J → D.E} {c : J → ℕ}
    (hw : IsTightFrame w c D.M)
    {i₀ : J} (h_unit : ∀ x : D.Φ × Unit, ‖(P.resolutionForms D.towerExp w i₀ x : ℂ_[p])‖ = 1) :
    P.cmCurve.LeastValLE (p := p) (P.resolutionForms D.towerExp w) c 12 l
      (D.localPrimeSumTotal p + 2 * ∑ x : D.Φ × Unit, (padicValNat p (D.lossProduct (l x)) : ℝ) -
        ∑ x : D.Φ × Unit, (padicValNat p (l x)! : ℝ)) := by
  have h_nonneg : 0 ≤ ∑ x : D.Φ × Unit, (padicValNat p (D.lossProduct (l x)) : ℝ) := by positivity
  by_cases h_split : chiK P.d p = 1
  · exact (D.leastValLE_twelve_of_split h_unit h_split).mono (by linarith)
  rcases lt_or_ge D.k p with hk | hk
  · -- As `d ≤ k`, a non-split prime `p > k` is inert.
    have hd : P.d < p := D.nat_le_of_hasLogBound.trans_lt hk
    exact D.leastValLE_twelve_of_lt hl hw (chiK_eq_neg_one_of_ne hd.ne' h_split) hk
  · exact (D.leastValLE_twelve_localPrimeSumTotal_of_le hl hw h_unit h_split hk).mono (by linarith)

end New.Data

end SharpnessCases
