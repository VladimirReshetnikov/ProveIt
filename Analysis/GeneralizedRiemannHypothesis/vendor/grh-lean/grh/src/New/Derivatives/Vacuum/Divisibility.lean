import New.Derivatives.Divisibility.Count
import New.Derivatives.Vacuum.Scale
import New.Derivatives.Vacuum.StandardDataProducts

/-!
# Integrality and divisibility of the derivatives of standard data

This file bounds the valuations of the derivatives of the Taylor series of standard data along
homogeneous integral polynomials.

* Standard data of level `δ` at `p` (`standardData`): the span over the `p`-integral complex numbers
  (`embValRing`) of the translates of the integral vacuum by the points `x` for which `δ * x` is
  integral above `p`.
* `V.jetSeries a f`: the Taylor series at `0` of the theta function of `f`, with the variables
  scaled by `a`; the scale `P.jetScale s` is `periodFactor * areaScale / cmPeriod`.
* `jet R Q F`: the derivative `Q(∂) F` at `0`.
* The normal form (`HasNormalForm`): after scaling the variables by `ϖ`, an integral series times
  the exponential of a multiple of the coupling series of the pairs of partner places.
* `ιₚ`: the embedding of `ℂ` into `ℂ_[p]` that comes with `PadicPlace p`.

## Main definitions and results

* `New.Parameters.norm_jet_jetSeries_le_pow`: a lower bound for the valuations of the derivatives of
  the Taylor series of standard data along homogeneous integral polynomials.
* `New.Parameters.exists_hasNormalForm_jetSeries`: at a non-split prime the Taylor series of
  standard data of level one has the normal form.
* `New.Parameters.norm_jet_minorProd_jetSeries_le`: so its derivatives along products of minors have
  the predicted divisibility up to a loss of `card (P.Φ s) * N ^ 3 * (1 + Real.logb p (max (boxes κ
  N) 1))`, where `N = card n'`.
* `New.Parameters.norm_schurJet_jetSeries_le_of_charges`: the bound with removed columns and charges
  for the derivatives along the entries of the Schur matrices.
-/

/-!
## Integrality of the derivatives of standard data at all primes

The theta function of standard data of level `δ`, taken at `conj δ * (areaScale / cmPeriod) * z`, is
a power of the product of copies of `θ` along a resolution of the identity times an integral series
in copies of the parameter.
-/

section JetIntegrality

open NumberField ComplexConjugate

namespace New.Parameters

/-- **Integrality of the derivatives.** Let `E = P.E s` be the cyclotomic extension at level `s` of
`K = P.K = ℚ(√-d)`, and `V` a hermitian space over `E` with all signs `+1` and the identity matrix
as adelic point (`IsStd`). Standard data of level `δ ≠ 0` at `p` (`standardData`) are the
combinations, with coefficients in the ring `embValRing` of complex numbers that are integral in
`ℂ_[p]`, of the translates of the integral vacuum in `𝒮 V` by the adelic points `x` such that
`δ * x` is integral above `p`. Let `f` be such data and let `F` be the Taylor series at `0` of the
theta function of `f` at `conj δ * d * jetScale * z`. For a polynomial `Q` with coefficients in
`embValRing`, in variables indexed by (infinite place of `E`, coordinate), the derivative `Q(∂) F`
at `0` (`jet`) has norm at most one in `ℂ_[p]`. -/
lemma norm_jet_jetSeries_le_one {P : Parameters} {s : ℕ} {n : Type} [Fintype n] [DecidableEq n]
    {ε : n → ℤˣ} {V : Space (E P s) n ε} [V.IsStd] {p : ℕ} [Fact p.Prime] [PadicPlace p]
    {δ : 𝓞 P.K} (hδ : δ ≠ 0) {f : 𝒮 V} (hf : f ∈ standardData V δ)
    (Q : MvPolynomial (InfinitePlace (P.E s) × n) embValRing) :
    ‖ιₚ (jet ℂ (Q.map embValRing.subtype)
      (V.jetSeries (star (δ : ℂ) * P.d * P.jetScale s) f))‖ ≤ 1 := by
  -- The theta function at `conj δ * (areaScale / cmPeriod) * z` is a power of the product of copies
  -- of `θ` along a resolution `u` times an integral series `H` in the parameters. Scaling `z` by
  -- `a = d * periodFactor` turns the forms `u† z` into `d` times integral forms `ν`. The exponent
  -- is `N = δ δ̄`, the degree of multiplication by `δ` on the curve.
  obtain ⟨N, -, h_area_mul⟩ := exists_isIsogeny_of_mul_mem_lattice
    (P.cmCurve.mul_mem_of_quadInt (a := δ) ⟨δ, rfl⟩)
  have hN : δ * conj (δ : ℂ) = N :=
    mul_right_cancel₀ (Complex.ofReal_ne_zero.2 (area_pos _).ne') h_area_mul
  obtain ⟨J, _, u, m, -, hu, H, hH, h_series⟩ := exists_jetSeries_map_eq_thetaProd_pow_mul hδ hN hf
  let a : ℂ := P.d * P.periodFactor s
  let ν : J → InfinitePlace (P.E s) × n → ℂ_[p] := ιₚ (P.periodFactor s) • daggerForms u
  let H' : MvPowerSeries (InfinitePlace (P.E s) × n) ℂ_[p] := H.rescale fun _ ↦ ιₚ a
  have hν (j : J) (x : InfinitePlace (P.E s) × n) : ‖ν j x‖ ≤ 1 :=
    norm_periodFactor_mul_daggerForms_le_one (hu j) x
  have h_forms : ιₚ a • daggerForms u = (P.d : ℂ_[p]) • ν := by rw [map_mul, map_natCast, mul_smul]
  have hH' : H' ∈ P.cmCurve.multiSeriesRing ((P.d : ℂ_[p]) • ν) := by
    simpa only [h_forms] using P.cmCurve.rescale_mem_multiSeriesRing (ιₚ a) hH
  have h_scale : star (δ : ℂ) * P.d * P.jetScale s =
      a * (conj (δ : ℂ) * (P.areaScale / P.cmPeriod)) := by
    simp only [a, jetScale, starRingEnd_apply]
    ring
  have h_scaled : (V.jetSeries (star (δ : ℂ) * P.d * P.jetScale s) f).map ιₚ =
      P.cmCurve.thetaProd ((P.d : ℂ_[p]) • ν) m ^ N * H' :=
    calc _ = (P.cmCurve.thetaProd (daggerForms u) m ^ N * H).rescale fun _ ↦ ιₚ a := by
          rw [h_scale, V.jetSeries_mul_eq_rescale, map_rescale, h_series]
      _ = _ := by rw [map_mul, map_pow, CMLattice.rescale_thetaProd, h_forms]
  rw [map_jet, h_scaled, MvPolynomial.map_map]
  exact P.cmCurve.norm_jet_thetaProd_pow_mul_le_one hν m N hH' (fun x : embValRing ↦ x.property) Q

/-- **Integrality at all primes.** Let `V` be a standard hermitian space over `E = P.E s`, and let
`f` be standard data of level `δ ≠ 0` at `p` on it (`standardData V δ`): a `p`-integral combination
of the translates of the integral vacuum by the points that `δ` makes integral above `p`. Let
`jetScale = periodFactor * √(2π / √d) / Ω₀`, where `P.K = ℚ(√-d)`, `Ω₀ 𝓞_K` is the lattice of its CM
curve and `periodFactor` is a normalising constant attached to `E`. Let `Q` be a homogeneous
polynomial of degree `l` with `p`-integral coefficients (in `embValRing`). Then the derivative
`Q(∂)` at `0` (`jet`) of the Taylor series (`jetSeries`) of the theta function of `f` at
`c * jetScale * z` has valuation in `ℂ_[p]` at least `l` times that of `c / (conj δ * d)`. -/
theorem norm_jet_jetSeries_le_pow {P : Parameters} {s : ℕ} {n : Type} [Fintype n] [DecidableEq n]
    {ε : n → ℤˣ} {V : Space (E P s) n ε} [V.IsStd] {p : ℕ} [Fact p.Prime] [PadicPlace p]
    {δ : 𝓞 P.K} (hδ : δ ≠ 0) {f : 𝒮 V} (hf : f ∈ standardData V δ) (c : ℂ)
    {Q : MvPolynomial (InfinitePlace (P.E s) × n) embValRing} {l : ℕ} (hQ : Q.IsHomogeneous l) :
    ‖ιₚ (jet ℂ (Q.map embValRing.subtype) (V.jetSeries (c * P.jetScale s) f))‖ ≤
      ‖ιₚ (c / (star (δ : ℂ) * P.d))‖ ^ l := by
  -- Scaling the variables by `c / (conj δ * d)` multiplies the derivative by the `l`-th power.
  have h_ne : star (δ : ℂ) * P.d ≠ 0 := mul_ne_zero (star_ne_zero.2 (mod_cast hδ)) (NeZero.ne _)
  have h_scale : c * P.jetScale s =
      c / (star (δ : ℂ) * P.d) * (star (δ : ℂ) * P.d * P.jetScale s) := by
    rw [← mul_assoc, div_mul_cancel₀ _ h_ne]
  rw [h_scale, V.jetSeries_mul_eq_rescale, jet_rescale (hQ.map _), map_mul, map_pow, norm_mul,
    norm_pow]
  exact mul_le_of_le_one_right (by positivity) (norm_jet_jetSeries_le_one hδ hf Q)

end New.Parameters

end JetIntegrality

/-!
## The normal form and the divisibility of standard data

At a non-split prime, which is automatically prime to `q₁`, the Taylor series of standard data of
level one is a product of copies of `θ` along a resolution of the identity that is integral above
the prime, times an integral series, so it has the normal form. Scaling by an integral number keeps
the normal form, and the count of the divisibility of series in normal form applies to it.
-/

section StandardDataNormalForm

open NumberField ComplexConjugate Finset Fintype

namespace New.Parameters
variable {P : Parameters} {s : ℕ} {n : Type} {p : ℕ} [Fact p.Prime]

/-- Let `α = P.α s` be the finite idele of `E = P.E s` that makes the integral adeles self-dual in
the construction of the Weil representation; the product of `α` and the integer `P.q₁ s` is integral
at every place. Let `p` be a prime that does not divide `P.q₁ s`, and `y` a vector over `E`. If all
coordinates of the adelic vector `finiteImage y = α⁻¹ y` are integral at the places above `p`, then
so are all coordinates of `y`. -/
lemma isIntegralAbove_of_finiteImage_mem (hp_not_dvd : ¬p ∣ P.q₁ s) {y : n → P.E s}
    (hy : finiteImage y ∈ integralAfter (1 : 𝓞 P.K) fun w : FinPlace (P.E s) ↦ ↑p ∈ w.asIdeal)
    (i : n) : IsIntegralAbove p (y i) := by
  intro w hw
  have h_unit : Valued.v (P.q₁ s : LocField w) = 1 := by
    simpa using v_algebraMap_eq_one (w.2.notMem_of_isCoprime_of_mem
      ((Fact.out : p.Prime).coprime_iff_not_dvd.2 hp_not_dvd).cast hw)
  have hα : Valued.v ((P.α s).1 w) ≤ 1 := by
    have h_int : Valued.v ((P.q₁ s : LocField w) * (P.α s).1 w) ≤ 1 := mem_Ô.1 q₁_mul_alpha_mem w
    rwa [map_mul, h_unit, one_mul] at h_int
  have h_global : algebraMap (P.E s) (𝔸f (P.E s)) (y i) = (P.α s).1 * finiteImage y i := by
    simp [finiteImage, WeilData.α]
  calc w.valuation (P.E s) (y i) = Valued.v ((P.α s).1 w) * Valued.v (finiteImage y i w) := by
        simpa using congrArg (fun x : 𝔸f (P.E s) ↦ Valued.v (x w)) h_global
    _ ≤ 1 := mul_le_one' hα (by simpa using hy i w hw)

/-- **Normal form at a non-split prime.** Let `V` be a standard hermitian space over the cyclotomic
extension `E = P.E s` of `ℚ(√-d)` (`IsStd`: all signs are `+1` and the adelic point is the identity
matrix), and let `p` be non-split: the character `chiK` of `ℚ(√-d)` is not `1` at `p`. Let `f` be
standard data of level one, a `p`-integral combination of the translates of the integral vacuum by
points integral above `p`, and let `c` be `p`-integral. With
`jetScale = periodFactor * √(2π / √d) / Ω₀` (`Ω₀` the CM period, `periodFactor` a normalising
constant), let `F` be the Taylor series in `ℂ_[p]` of the theta function of `f` at
`c * jetScale * z`, in the variables `z_(τ,i)` (place, coordinate). Then `F` has the normal form
(`HasNormalForm`) `F(ϖ z) = W exp (ϖ ^ (p + 1) / p * ∑_e ∑_j l e j * Γ_e ^ p ^ j)`: the series `W`
has coefficients in the valuation ring `valRingCp p` of `ℂ_[p]`, as are all `l e j`. Here `e` runs
over `partnerExponents P.d p` (`e` odd, or any `e` if `p = d`), the coupling `Γ_e` is the sum of all
`z_(τ,i) ^ p ^ e * z_(τ',i)` with `τ' = P.partner s p e τ` the place `τ` moved by the class of
`-p ^ e`, and `ϖ` has valuation `varpiValuation P.d p`, which is `1 / (p² - 1)` if `p` is inert and
`1 / (2 p - 2)` if `p = d`. -/
theorem exists_hasNormalForm_jetSeries [Fintype n] [DecidableEq n] {ε : n → ℤˣ}
    {V : Space (E P s) n ε} [V.IsStd] [PadicPlace p] (hp_nonsplit : chiK P.d p ≠ 1) {f : 𝒮 V}
    (hf : f ∈ standardData V 1) {c : ℂ} (hc : ‖ιₚ c‖ ≤ 1) :
    ∃ (ϖ : ℂ_[p]) (l : ℕ → ℕ → valRingCp p), ‖ϖ‖ = p ^ (-varpiValuation P.d p) ∧
      HasNormalForm (partnerExponents P.d p) (P.partner s p) ϖ l
        ((V.jetSeries (c * P.jetScale s) f).map ιₚ) := by
  -- A resolution writes the series as a theta product times an integral series; such series have
  -- the normal form, and scaling by a `p`-integral number keeps it.
  have hp_not_dvd : ¬p ∣ P.q₁ s := fun h_dvd ↦
    hp_nonsplit (P.chiK_eq_one_of_dvd Fact.out h_dvd)
  obtain ⟨ϖ, l, hϖ, -, h_normalForm_thetaProd⟩ := P.exists_hasNormalForm s hp_nonsplit
  obtain ⟨J, _, u, m, h_resolution, hu, H, hH, h_theta⟩ :=
    exists_jetSeries_map_eq_thetaProd_pow_mul (N := 1) one_ne_zero (by simp) hf
  have h_integral (j : J) : ∀ i : n, IsIntegralAbove p (u j i) :=
    isIntegralAbove_of_finiteImage_mem hp_not_dvd (hu j)
  have h_series : (V.jetSeries (P.areaScale / P.cmPeriod) f).map ιₚ =
      P.cmCurve.thetaProd (daggerForms u) m * H := by simpa using h_theta
  have h_scale : ‖ιₚ (c * P.periodFactor s)‖ ≤ 1 := by
    rwa [map_mul, norm_mul, P.norm_iota_periodFactor_eq_one s hp_not_dvd, mul_one]
  have h_factor : c * P.jetScale s = c * P.periodFactor s * (P.areaScale / P.cmPeriod) := by
    rw [jetScale, mul_assoc, mul_div_assoc]
  rw [h_factor, V.jetSeries_mul_eq_rescale, map_rescale, h_series]
  exact ⟨ϖ, _, hϖ,
    (h_normalForm_thetaProd u m h_resolution h_integral H hH).rescale ⟨_, h_scale⟩⟩

variable [Fintype n] [DecidableEq n] [PadicPlace p] {n' : Type} [Fintype n'] [DecidableEq n']
  {κ : P.Φ s → ℕ → ℕ}

/-- **Divisibility at non-split primes.** Let `f` be standard data of level one on the space of
`n' × n` matrices (`hom` of the spaces `stdSpace`, whose forms are sums of norms of coordinates).
Let `c` be `p`-integral and `F` the Taylor series in `ℂ_[p]` of the theta function of `f` at
`c * jetScale * z`, where `jetScale = periodFactor * √(2π / √d) / Ω₀` (`Ω₀` the CM period,
`periodFactor` a normalising constant); its variable `(τ, b, a)` is the entry `(b, a)` of the matrix
`z_τ`. Let `κ τ h` be the number of columns of height `h` of a diagram at the place `τ`, let `i'` be
standard fillings of these diagrams by elements of `n'` (`WeylIndex`) and `y τ` integral matrices
with rows indexed by `n`. For a column of height `h < N = card n'`, take the minor of `z_τ y_τ` on
the rows that `i'` puts into the column and on the first `h` columns of `y_τ`; `minorProd i' y` is
the product of these minors. The derivative of `F` along it has valuation at least `D` less
`f₀ * N ^ 3 * (1 + log_p max (B, 1))`, where `f₀` is the number of infinite places and
`B = boxes κ N` the number of boxes in columns of height below `N`. Here `D = predictedDivisibility`
is `v ∑_e ∑_τ ((a_τ / p ^ e - a_τ' - a'_τ')⁺ + (l_τ / p ^ e - l_τ')⁺ - a'_τ / p ^ e)`: among the
heights below `N`, `a_τ` counts the columns of height one at `τ`, `a'_τ` the others and `l_τ` their
boxes; `τ'` is the place `-p ^ e τ`, `v = piPrimeValuation P.d p`, and `e` runs over the odd numbers
(all `e ≥ 1` if `p = d`). If `p = d`, half of `∑_τ (min (a_τ, a_τ' + a'_τ') + a'_τ + min (l_τ,
l_τ'))`, with `e = 0`, is subtracted from it. -/
theorem norm_jet_minorProd_jetSeries_le
    {f : 𝒮 ((stdSpace (E P s) n).hom (stdSpace (E P s) n'))} {c : ℂ} (hp_nonsplit : chiK P.d p ≠ 1)
    (hf : f ∈ standardData ((stdSpace (E P s) n).hom (stdSpace (E P s) n')) 1) (hc : ‖ιₚ c‖ ≤ 1)
    (i' : WeylIndex n' κ) (y : P.Φ s → n → ℕ → valRingCp p) :
    let N : ℕ := card n'
    ‖jet ℂ_[p] (minorProd i' fun (τ : P.Φ s) (a : n) (k : ℕ) ↦ (y τ a k : ℂ_[p]))
        ((((stdSpace (E P s) n).hom (stdSpace (E P s) n')).jetSeries
          (c * P.jetScale s) f).map ιₚ)‖ ≤
      p ^ (-(predictedDivisibility P.d p (P.partner s p) κ N -
        card (P.Φ s) * N ^ 3 * (1 + Real.logb p (max (boxes κ N) 1 : ℕ))) : ℝ) := by
  obtain ⟨ϖ, l, hϖ, h_form⟩ := exists_hasNormalForm_jetSeries hp_nonsplit hf hc
  exact P.norm_jet_minorProd_le_of_hasNormalForm s hp_nonsplit hϖ h_form i' y

/-- **Divisibility of Schur entries at a non-split prime `p`.** Let `f` be standard data of level
one on the space `Hom(stdSpace n, stdSpace n')` of `n' × n` matrices, and `c` a `p`-integral number.
Let `F` be the Taylor series of the theta function of `f` at `c * jetScale * z`, where
`jetScale = periodFactor * √(2π / √d) / Ω₀` (`Ω₀` the CM period, `periodFactor` a normalising
constant); its variable `(τ, b, a)` is the entry `(b, a)` of the matrix `z_τ`. The Schur matrix of
the diagrams `κ` is the matrix of the map of Weyl modules of shape `κ` that the family `z` induces,
in the bases of chosen standard fillings; `schurJet κ F i' i` is the derivative at `0` of `F` along
the polynomial at its entry `(i', i)`. Let `κ` fit the ranks.

Remove the columns of height one at the places of `erasedPlaces`, and give charges
`p ^ chargeExp τ h b` (place, height, row) such that, for each `e` in `partnerExponents P.d p` with
partner `τ' = -p ^ e τ` of `τ`, each row `b` and each height `h`: if `τ ∈ erasedPlaces`, or `h = 1`
and `τ' ∈ erasedPlaces`, then `chargeExp τ 1 b` or `chargeExp τ' h b` is nonzero
(`IsChargeExponent`). Let `N = card n'` and `B` the number of boxes of `κ` in columns of height
below `N`. Then the sum `fillingCharge chargeExp i'` of the exponents over the boxes of the filling
`i'`, plus the valuation of the derivative, is at least the predicted divisibility of the remaining
diagrams, plus the gain `gammaPrime P.d p` for each removed box among these `B`, less
`f₀ * N ^ 3 * (1 + log_p max (B, 1))`, where `f₀` is the number of infinite places. -/
theorem norm_schurJet_jetSeries_le_of_charges
    {f : 𝒮 ((stdSpace (E P s) n).hom (stdSpace (E P s) n'))} {c : ℂ}
    (hp_nonsplit : chiK P.d p ≠ 1) (hκ : FitsRanks (fun _ : P.Φ s ↦ n) (fun _ : P.Φ s ↦ n') κ)
    (hf : f ∈ standardData ((stdSpace (E P s) n).hom (stdSpace (E P s) n')) 1) (hc : ‖ιₚ c‖ ≤ 1)
    (erasedPlaces : Finset (P.Φ s)) (chargeExp : P.Φ s → ℕ → n' → ℕ)
    (h_charge : ∀ e ∈ partnerExponents P.d p,
      IsChargeExponent (P.partner s p e) erasedPlaces chargeExp)
    (i' : WeylIndex n' κ) (i : WeylIndex n κ) :
    let N : ℕ := card n'
    let B : ℕ := boxes κ N
    ‖ιₚ (schurJet κ (((stdSpace (E P s) n).hom (stdSpace (E P s) n')).jetSeries
        (c * P.jetScale s) f) i' i)‖ ≤
      p ^ (fillingCharge chargeExp i' -
        (predictedDivisibility P.d p (P.partner s p) (eraseHeightOne κ erasedPlaces) N +
          gammaPrime P.d p * (B - boxes (eraseHeightOne κ erasedPlaces) N) -
          card (P.Φ s) * N ^ 3 * (1 + Real.logb p (max B 1 : ℕ))) : ℝ) := by
  -- Bound the Schur entry by a derivative along a product of minors, then use the normal form.
  obtain ⟨ϖ, l, hϖ, h_form⟩ := exists_hasNormalForm_jetSeries hp_nonsplit hf hc
  set F : MvPowerSeries (P.Φ s × n' × n) ℂ :=
    ((stdSpace (E P s) n).hom (stdSpace (E P s) n')).jetSeries (c * P.jetScale s) f
  obtain ⟨y, h_le_minorProd⟩ :=
    exists_norm_schurJet_le_norm_jet_minorProd hκ (F.map ιₚ) i' i
  rw [show ιₚ (schurJet κ F i' i) = schurJet κ (F.map ιₚ) i' i by
    simp [schurJet, map_jet, map_schur hκ]]
  exact h_le_minorProd.trans (P.norm_jet_minorProd_le_of_charges s hp_nonsplit hϖ h_form
    erasedPlaces chargeExp (fun e he τ h b _ _ ↦ h_charge e he τ h b) i' y)

end New.Parameters

end StandardDataNormalForm
