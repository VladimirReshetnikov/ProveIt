import Lib.ClassField.HeckeL.EulerProduct
import Lib.ClassField.HeckeL.IdelicThetaSum
import Lib.General.Analysis.HolomorphicIntegrals

/-!
# Analyticity at 1 of L-functions of nontrivial Hecke characters

This file proves that partial Hecke `L`-functions `New.eulerProd (heckeCoeff ψ S)` of nontrivial
characters extend analytically to `s = 1`. Here `ψ` satisfies `New.IsHeckeOfType ψ n`, `S` is a
finite set of primes, and only real `s ≥ 1` is treated. The file combines the theta-sum estimate
of `Lib.ClassField.HeckeL.IdelicThetaSum` with the finite-place half of Tate's thesis. This yields
three results: analyticity at `1`, a prime density statement and, for `ψ ^ 2 ≠ 1`, nonvanishing
on `[1, ∞)`. Valuations are multiplicative: `v x ≤ 1` means integral.

## Main definitions and results

* `New.IsHeckeOfType.integral_mul_finIdeleAbs_rpow_eq_eulerProd_mul`: the integral of `f ψ |·| ^ s`
  over the finite ideles is the partial `L`-function of `ψ` times a volume;
  `New.IsHeckeOfType.tate_integral` adds that this volume is nonzero.
* `New.IsHeckeOfType.exists_analyticAt_one_eulerProd`: for `ψ ≠ 1` the partial `L`-function extends
  analytically to a neighbourhood of `1`.
* `New.IsHeckeOfType.exists_hasPrimeDensity`: for `ψ ≠ 1` the partial `L`-function is continuous on
  `[1, ∞)`, and the values of `ψ` have mean `-m` over the primes of degree one, for some natural
  number `m`.
* `New.IsHeckeOfType.eulerProd_ne_zero`: for `ψ ^ 2 ≠ 1` the partial `L`-function has no zero on
  `[1, ∞)`.

Notions from other files:
* `New.finIdeleAbs`: The module |x| of a finite idele x: the adelic absolute value of the idele with
  finite part x and component 1 at infinity. `New.ZetaIntegral.ideleModule`: the module of an idele.
* `New.Ô`: The subring Ô of finite adeles of K that are integral at every finite place.
  `New.ZetaIntegral.adelicTent r d`: a tent of radius `r` at `1` times the indicator of
  `d * (x - 1) ∈ Ô`.
* `New.eulerProd`: The Euler product `∏ (1 - a v * q ^ (-s))⁻¹` over the primes `v` of `K`, with
  `q = v.q` the norm of `v`, as a function of real `s > 1`; at `s = 1` it is the limit from the
  right, if that exists.
* `New.IsHeckeOfType ψ n`: the character `ψ` of the finite ideles is the finite part of a Hecke
  character of type `n`: its kernel is open and `ψ x * ∏_w (Φ_w x / |Φ_w x|) ^ (n w) = 1` on `Kˣ`.
* `New.heckeCoeff ψ S`: the function on finite places sending `v ∉ S` to the value of `ψ` at the
  local idele of the chosen uniformiser at `v`, and `v ∈ S` to `0`.

## Relation to the literature

Known result: Hecke L-functions with Euler product, continuation to s = 1, non-vanishing and prime
densities. Only real s is treated, and a non-trivial character of integral angular type is continued
to a neighbourhood of 1 from Tate's integral by a Riemann sum instead of Poisson summation.
Non-vanishing is proved only when the square of the character is non-trivial, and densities are
taken over primes of degree one, with bounded error. Source: J. Tate, Fourier analysis in number
fields and Hecke's zeta-functions, 1950, in Cassels–Fröhlich ch. XV, §4.4–4.5; J. Milne, Class Field
Theory, VI 4.8–4.9 (finite order); S. Lang, Algebraic Number Theory (non-vanishing); Titchmarsh,
Theory of the Riemann zeta-function, §2.11 (the Riemann-sum continuation is Müntz's formula over ℚ).
-/

noncomputable section

section HeckeContinuation

open NumberField Complex MeasureTheory Valued Function IsDedekindDomain

namespace New

variable {K : Type*} [Field K] [NumberField K] {ψ : (𝔸f K)ˣ →* ℂˣ}

/-- If `ψ` is unramified at `w`, its value at the local idele of `x` is its value at the uniformiser
raised to the order `-log (v x)` of `x`. -/
lemma CharUnramifiedAt.apply_locIdele_eq_zpow {w : FinPlace K} (hψ : CharUnramifiedAt ψ w)
    (x : (LocField w)ˣ) :
    ψ (locIdele w x) = ψ (locIdele w (uniformizer w)) ^ (-(v x.val).log) := by
  have h_unit : v (x * uniformizer w ^ (v x.val).log).val = 1 := by
    simp [-WithZero.inv_exp, WithZero.exp_neg]
  simpa [← div_eq_one] using hψ (x * uniformizer w ^ (v x.val).log) h_unit

/-- For a Haar measure `μ` and an open set `V` containing `1`, the volume of `Ô^× ∩ V` is nonzero.
Here `Ô^× = idelesUnitOff ∅` is the group of unit ideles. -/
lemma measureReal_idelesUnitOff_empty_inter_ne_zero (μ : Measure (𝔸f K)ˣ) [μ.IsHaarMeasure]
    {V : Set (𝔸f K)ˣ} (hV : IsOpen V) (hV_one : 1 ∈ V) :
    μ.real ((idelesUnitOff ∅ : Subgroup (𝔸f K)ˣ) ∩ V) ≠ 0 := by
  -- The set is open, nonempty and inside a compact set, so its measure is finite and nonzero.
  rw [measureReal_ne_zero_iff
    (measure_inter_ne_top_of_left_ne_top isCompact_idelesUnitOff_empty.measure_ne_top)]
  exact ((isOpen_idelesUnitOff ∅).inter hV).measure_ne_zero μ ⟨1, one_mem _, hV_one⟩

/-- Let `μ` be a left-invariant measure on a group `G`, and `W` a measurable set with
`μ.real W ≠ 0`. If `c` has sum `a` over a countable type `ι`, then for all `t : ι → G` the function
`x ↦ ∑' i, c i * W.indicator 1 (t i * x)` has integral `a * μ.real W`: every translate of the
indicator of `W` has integral `μ.real W`. -/
theorem _root_.MeasureTheory.integral_tsum_mul_indicator_mul_left_of_hasSum {G ι : Type*}
    [Group G] [MeasurableSpace G] [MeasurableMul G] (μ : Measure G) [μ.IsMulLeftInvariant]
    [Countable ι] {W : Set G} (hW : MeasurableSet W) (hW_vol : μ.real W ≠ 0) {c : ι → ℂ} {a : ℂ}
    (hc : HasSum c a) (t : ι → G) :
    ∫ x : G, ∑' i : ι, c i * W.indicator 1 (t i * x) ∂μ = a * μ.real W := by
  have h_translate (i : ι) : ∫ x, W.indicator (1 : G → ℂ) (t i * x) ∂μ = μ.real W := by
    simp [hW, integral_mul_left_eq_self, Pi.one_def]
  have h_int (i : ι) : Integrable (fun x ↦ c i * W.indicator (1 : G → ℂ) (t i * x)) μ :=
    .const_mul (.of_integral_ne_zero (by simp [h_translate, hW_vol])) (c i)
  have h_sum : Summable fun i ↦ ∫ x, ‖c i * W.indicator (1 : G → ℂ) (t i * x)‖ ∂μ := by
    simpa [hW, integral_const_mul, integral_mul_left_eq_self, Pi.one_def,
      norm_indicator_eq_indicator_norm] using hc.summable.norm.mul_right (μ.real W)
  rw [← integral_tsum_of_summable_integral_norm h_int h_sum]
  simp [integral_const_mul, h_translate, hc.tsum_eq, tsum_mul_right]

open scoped Classical in
open Real HeightOneSpectrum Set in
/-- Let `f` vanish unless `x` is integral outside `S` and a unit at `S`, let `f` take equal values
at integral ideles with the same components at `S`, and let `χ` take the value `heckeCoeff ψ S w` at
each prime `w`. Then multiplying an integral `x` by the uniformiser at `w` (keeping it integral)
multiplies `f x * ψ x * |x| ^ s` by `χ w * w.q ^ (-s)`. -/
private lemma mul_finIdeleAbs_rpow_locIdele_uniformizer_mul {S : Set (FinPlace K)} {f : (𝔸f K)ˣ → ℂ}
    (h_supp : ∀ x : (𝔸f K)ˣ, f x ≠ 0 →
      (∀ w : FinPlace K, w ∉ S → v (x.val w) ≤ 1) ∧ ∀ w : FinPlace K, w ∈ S → v (x.val w) = 1)
    (h_local : ∀ x y : (𝔸f K)ˣ, x.val ∈ Ô K → y.val ∈ Ô K →
      (∀ w : FinPlace K, w ∈ S → y.val w = x.val w) → f y = f x)
    {χ : Ideal (𝓞 K) →* ℂ} (hχ_prime : ∀ w : FinPlace K, χ w.asIdeal = heckeCoeff ψ S w)
    (s : ℝ) (w : FinPlace K) {x : (𝔸f K)ˣ} (hx : x.val ∈ Ô K)
    (hx_unif : (locIdele w (uniformizer w) * x).val ∈ Ô K) :
    f (locIdele w (uniformizer w) * x) * ψ (locIdele w (uniformizer w) * x) *
        (finIdeleAbs (locIdele w (uniformizer w) * x) ^ s : ℝ) =
      χ w.asIdeal * w.q ^ (-s : ℂ) * (f x * ψ x * (finIdeleAbs x ^ s : ℝ)) := by
  by_cases hw : w ∈ S
  · -- At `w ∈ S` both sides vanish: `locIdele w (uniformizer w) * x` is not a unit at `w`, and
    -- `χ w = 0`.
    have h_lt : v ((locIdele w (uniformizer w) * x).val w) < 1 := by
      -- `↓` applies the lemma before simp computes `v (uniformizer w * _)` as a product.
      simpa [↓← v_uniformizer_inv_mul_le_one_iff] using mem_Ô.mp hx w
    have h_zero : f (locIdele w (uniformizer w) * x) = 0 := by
      by_contra h_ne
      exact h_lt.ne ((h_supp _ h_ne).right w hw)
    simp [h_zero, hχ_prime, heckeCoeff, hw]
  · -- At `w ∉ S` the value of `f` does not change, and `|locIdele w (uniformizer w)| = w.q⁻¹`.
    have h_same : f (locIdele w (uniformizer w) * x) = f x :=
      h_local x _ hx hx_unif fun u hu ↦ by simp [ne_of_mem_of_not_mem hu hw]
    have h_abs : finIdeleAbs (locIdele w (uniformizer w)) = (w.q : ℝ)⁻¹ := by
      simp [norm_locField_eq_q_zpow]
    have h_abs_rpow : finIdeleAbs (locIdele w (uniformizer w) * x) ^ s =
        (w.q : ℝ) ^ (-s) * finIdeleAbs x ^ s := by
      rw [map_mul, h_abs, mul_rpow (by positivity) (by simp [finIdeleAbs]),
        inv_rpow (by positivity), ← rpow_neg (by positivity)]
    have h_coeff : χ w.asIdeal = ψ (locIdele w (uniformizer w)) := by
      simp [hχ_prime, heckeCoeff, hw]
    rw [h_same, h_abs_rpow, h_coeff, map_mul, ofReal_mul, ofReal_cpow (by positivity)]
    push_cast
    ring

open HeightOneSpectrum FractionalIdeal in
/-- A nonzero fractional ideal `J` of `𝓞 K` whose exponent `count K w J` is nonnegative at every
prime `w` is an integral ideal. -/
private lemma exists_eq_coeIdeal_of_count_nonneg {J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K}
    (hJ : J ≠ 0) (h_count : ∀ w : FinPlace K, 0 ≤ count K w J) :
    ∃ I : Ideal (𝓞 K), J = I := by
  -- `J` is the product of the powers `w ^ count K w J`, all with natural exponents.
  refine ⟨∏ᶠ w : FinPlace K, w.asIdeal ^ (count K w J).toNat, ?_⟩
  calc J = ∏ᶠ w : FinPlace K,
          (w.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ ((count K w J).toNat : ℤ) := by
        simp only [Int.toNat_of_nonneg (h_count _), finprod_heightOneSpectrum_factorization' K hJ]
    _ = _ := by
      -- `↓` turns `x ^ (n : ℤ)` into `x ^ n` before simp rewrites the cast of `toNat` as `max · 0`.
      simp [↓zpow_natCast, ← coeIdeal_pow, ← coeIdeal_finprod]

/-- Let `K` be a number field and `d` a homomorphism from the finite ideles `(𝔸f K)ˣ` to the group
of nonzero fractional ideals of `𝓞 K`. Suppose that an idele `a` is integral at a finite place `w`
exactly when the exponent `count K w (d a)` of the prime `w` in `d a` is nonnegative. Let `S` be a
set of finite places and `x` an idele that is integral at each `w ∉ S` and a unit at each `w ∈ S`.
Then the fractional ideal `d x` is an ideal of `𝓞 K`. Here `a.val w` is the component of `a` in the
completion of `K` at `w`, and the valuation `Valued.v` is multiplicative: `≤ 1` means integral and
`= 1` means a unit. -/
private lemma exists_divisor_eq_coeIdeal_of_supp {K : Type*} [Field K] [NumberField K]
    {d : (𝔸f K)ˣ →* (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ}
    (hd_count : ∀ (a : (𝔸f K)ˣ) (w : FinPlace K),
      Valued.v (a.val w) ≤ 1 ↔ 0 ≤ FractionalIdeal.count K w (d a).val)
    {S : Set (FinPlace K)} {x : (𝔸f K)ˣ}
    (hx_integral : ∀ w : FinPlace K, w ∉ S → Valued.v (x.val w) ≤ 1)
    (hx_unit : ∀ w : FinPlace K, w ∈ S → Valued.v (x.val w) = 1) :
    ∃ I : Ideal (𝓞 K), (d x).val = (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
  -- A unit is integral, so `x` is integral at every place and all exponents of `d x` are `≥ 0`.
  have h_integral (w : FinPlace K) : Valued.v (x.val w) ≤ 1 := by
    by_cases hw : w ∈ S
    · exact (hx_unit w hw).le
    · exact hx_integral w hw
  have h_count (w : FinPlace K) : 0 ≤ FractionalIdeal.count K w (d x).val :=
    (hd_count x w).mp (h_integral w)
  exact exists_eq_coeIdeal_of_count_nonneg (d x).ne_zero h_count

namespace IsHeckeOfType

variable [PlaceEmbedding K] {n : InfinitePlace K → ℤ} {S : Set (FinPlace K)}
  (h : IsHeckeOfType ψ n) (hS : S.Finite)

attribute [local fun_prop] Continuous.rpow_const

private lemma isOpen_ker (hψ : IsHeckeOfType ψ n) : ψ.ker.IsOpen := hψ.left

/-- The defining identity of `IsHeckeOfType ψ n` at `x ∈ Kˣ`. -/
private lemma apply_principalIdele_mul_prod_eq_one (hψ : IsHeckeOfType ψ n) (x : Kˣ) :
    (ψ (principalIdele x) : ℂ) * ∏ w : InfinitePlace K, (Φ w x.val / ‖Φ w x‖) ^ n w = 1 :=
  hψ.right x

/-- Let `ψ` satisfy `IsHeckeOfType ψ n`: its kernel is open, and
`ψ x * ∏ w, (Φ w x / ‖Φ w x‖) ^ n w = 1` for `x ∈ Kˣ`. Then `ψ x` has absolute value one for
every finite idele `x`. -/
lemma norm_eq_one (hψ : IsHeckeOfType ψ n) (x : (𝔸f K)ˣ) : ‖(ψ x).val‖ = 1 := by
  -- The kernel `H` of `|ψ|` is open and contains `K^×`, so has finite index
  -- (`finiteIndex_idele_subgroup_of_isOpen`): `|ψ x|` is a nonnegative real root of unity.
  let H : Subgroup (𝔸f K)ˣ := (normHom.toMonoidHom.comp (Units.coeHom ℂ)).ker.comap ψ
  have h_ker_le : ψ.ker ≤ H := fun y hy ↦ by simp [H, MonoidHom.mem_ker.mp hy]
  have h_principal (y : Kˣ) : principalIdele y ∈ H := by
    -- Take norms in the defining identity; each factor `Φ w y / ‖Φ w y‖` has norm one.
    simpa [H] using congrArg norm (hψ.apply_principalIdele_mul_prod_eq_one y)
  have h_index : H.FiniteIndex := finiteIndex_idele_subgroup_of_isOpen H
    (ψ.ker.isOpen_mono h_ker_le hψ.isOpen_ker) fun y _ ↦ h_principal y
  have h_pow : ‖(ψ x : ℂ)‖ ^ H.index = 1 := by simpa [H] using H.pow_index_mem x
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) h_index.index_ne_zero).mp h_pow

lemma norm_heckeCoeff_le (hψ : IsHeckeOfType ψ n) (v : FinPlace K) : ‖heckeCoeff ψ S v‖ ≤ 1 := by
  rw [← hψ.norm_eq_one (locIdele v (uniformizer v))]
  exact norm_indicator_le_norm_self (fun w : FinPlace K ↦ (ψ (locIdele w (uniformizer w)) : ℂ)) v

/-- The `d`-th power of a Hecke character of type `n` is a Hecke character of type `d • n`. -/
lemma pow (hψ : IsHeckeOfType ψ n) (d : ℕ) : IsHeckeOfType (ψ ^ d) (d • n) := by
  have h_ker_le : ψ.ker ≤ (ψ ^ d).ker := fun y hy ↦ by simp [MonoidHom.mem_ker.mp hy]
  refine ⟨Subgroup.isOpen_mono h_ker_le hψ.isOpen_ker, fun x ↦ ?_⟩
  -- Raise the defining identity of `ψ` to the power `d`.
  simpa [Finset.prod_pow, zpow_mul', ← mul_pow] using
    congrArg (· ^ d) (hψ.apply_principalIdele_mul_prod_eq_one x)

/-- Over a CM field, a Hecke character of nonzero type `n` is nontrivial. -/
lemma ne_one (hψ : IsHeckeOfType ψ n) [IsCMField K] (hn : n ≠ 0) : ψ ≠ 1 := by
  -- If `ψ = 1`, the function `F y = ∏ (y u / ‖y u‖) ^ n u` on `∏ ℂ` is `1` on the dense set of
  -- nonzero elements of `K`, so also at a point `y₀` of continuity; but we can arrange `F y₀ = -1`.
  rintro rfl
  obtain ⟨w, hw⟩ : ∃ w : InfinitePlace K, n w ≠ 0 := Function.ne_iff.mp hn
  let F (y : InfinitePlace K → ℂ) : ℂ := ∏ u, (y u / ‖y u‖ : ℂ) ^ n u
  -- The point `y₀` has component `exp (π i / n w)` at `w` and `1` elsewhere.
  let y₀ : InfinitePlace K → ℂ := exp ∘ Pi.single w (log (-1) / n w)
  have h_cont : ContinuousAt F y₀ := by fun_prop (disch := simp [y₀])
  have h_one : ∀ y ∈ Set.range (RingHom.pi Φ : K →+* InfinitePlace K → ℂ) \ {0}, F y = 1 := by
    rintro _ ⟨⟨x, rfl⟩, hx_ne⟩
    have hx : x ≠ 0 := (map_ne_zero_iff _ (RingHom.injective _)).mp hx_ne
    simpa [F] using hψ.apply_principalIdele_mul_prod_eq_one (.mk0 x hx)
  have h_val_one : F y₀ = 1 :=
    h_cont.continuousWithinAt.eq_const_of_mem_closure (denseRange_Φ.sdiff_singleton 0 _) h_one
  have h_val_neg : F y₀ = -1 := calc
    F y₀ = (y₀ w / ‖y₀ w‖ : ℂ) ^ n w := Fintype.prod_eq_single w fun u hu ↦ by simp [y₀, hu]
    -- The factor at `w` is `exp (π i / n w) ^ n w = exp (π i) = -1`.
    _ = -1 := by simp [y₀, log, norm_exp, ← exp_int_mul, mul_div_cancel₀, hw]
  norm_num [h_val_one] at h_val_neg

open HeightOneSpectrum UniqueFactorizationMonoid in
/-- Let `ψ` satisfy `IsHeckeOfType ψ n`. The values `heckeCoeff ψ S` at the primes extend to a
completely multiplicative function `χ` on the ideals of `𝓞 K` with `χ ⊥ = 0` and `‖χ I‖ ≤ 1`. -/
lemma exists_monoidHom_asIdeal_eq_heckeCoeff (hψ : IsHeckeOfType ψ n) (S : Set (FinPlace K)) :
    ∃ χ : Ideal (𝓞 K) →* ℂ, χ ⊥ = 0 ∧
      (∀ w : FinPlace K, χ w.asIdeal = heckeCoeff ψ S w) ∧ ∀ I : Ideal (𝓞 K), ‖χ I‖ ≤ 1 := by
  let χ : Ideal (𝓞 K) →* ℂ :=
    { toFun I :=
        if I = 0 then 0 else ((normalizedFactors I).map (asIdeal.extend (heckeCoeff ψ S) 0)).prod
      map_one' := by
        -- `↓` applies `normalizedFactors_one` before simp rewrites the ideal `1` as `⊤`.
        simp [↓normalizedFactors_one]
      map_mul' := by aesop (add simp normalizedFactors_mul) }
  have hχ_prime (w : FinPlace K) : χ w.asIdeal = heckeCoeff ψ S w := by
    simp [χ, ne_bot, asIdeal_injective, normalizedFactors_irreducible, irreducible]
  refine ⟨χ, by simp [χ], hχ_prime, fun I ↦ ?_⟩
  -- The bound `‖χ I‖ ≤ 1` holds on the primes, so on all ideals by multiplicativity.
  induction I using induction_on_prime with
  | h₁ => simp [χ]
  | h₂ u hu => rw [hu.eq_one, map_one, norm_one]
  | h₃ J p hJ_ne hp hJ =>
    obtain ⟨w, rfl⟩ : ∃ w : FinPlace K, w.asIdeal = p := ⟨ofPrime hp, rfl⟩
    grw [map_mul, norm_mul, hJ, mul_one, hχ_prime, hψ.norm_heckeCoeff_le]

open scoped Classical in
open Real HeightOneSpectrum UniqueFactorizationMonoid FractionalIdeal Set in
/-- Tate's zeta integral over the finite ideles. Let `ψ` be the finite part of a Hecke character of
type `n`, `μ` a Haar measure on the finite ideles, and `V ∋ 1` open. Let `f` be supported on the
ideles integral outside `S` and units at `S`, with `f ψ` the indicator of `V` on the unit ideles
`Ô^× = idelesUnitOff ∅`, and with `f` depending only on the components at `S` of integral ideles.
Then for real `s > 1` the function `f x * ψ x * |x| ^ s` is integrable, with integral
`eulerProd (heckeCoeff ψ S) s * μ (Ô^× ∩ V)`, where `|x| = finIdeleAbs x` and
`eulerProd (heckeCoeff ψ S) s` is the partial Euler product `∏_{v ∉ S} (1 - ψ(ϖ_v) q_v^(-s))⁻¹`,
with `ϖ_v` the chosen uniformiser and `q_v` the norm of `v`. -/
lemma integral_mul_finIdeleAbs_rpow_eq_eulerProd_mul (hψ : IsHeckeOfType ψ n)
    (S : Set (FinPlace K)) (f : (𝔸f K)ˣ → ℂ) (V : Set (𝔸f K)ˣ) (μ : Measure (𝔸f K)ˣ)
    [μ.IsHaarMeasure] (hV : IsOpen V) (hV_one : 1 ∈ V)
    (h_supp : ∀ x : (𝔸f K)ˣ, f x ≠ 0 →
      (∀ w : FinPlace K, w ∉ S → v (x.val w) ≤ 1) ∧ ∀ w : FinPlace K, w ∈ S → v (x.val w) = 1)
    (h_units : ∀ u : (𝔸f K)ˣ, u ∈ idelesUnitOff ∅ → f u * ψ u = if u ∈ V then 1 else 0)
    (h_local : ∀ x y : (𝔸f K)ˣ, x.val ∈ Ô K → y.val ∈ Ô K →
      (∀ w : FinPlace K, w ∈ S → y.val w = x.val w) → f y = f x) :
    ∀ s : ℝ, 1 < s →
      Integrable (fun x : (𝔸f K)ˣ ↦ f x * ψ x * (finIdeleAbs x ^ s : ℝ)) μ ∧
        ∫ x : (𝔸f K)ˣ, f x * ψ x * (finIdeleAbs x ^ s : ℝ) ∂μ =
          eulerProd (heckeCoeff ψ S) s * μ.real ((idelesUnitOff ∅ : Subgroup (𝔸f K)ˣ) ∩ V) := by
  -- Split the ideles by their divisor `d x`. The integrand vanishes unless `d x` is an integral
  -- ideal `I`, and on the ideles of divisor `I` it is `χ I * N I ^ (-s)` times a translate of the
  -- indicator of `W = Ô^× ∩ V`. Summing the integrals over `I` gives the Euler product times the
  -- volume of `W`.
  obtain ⟨χ, hχ_zero, hχ_prime, hχ_norm⟩ := hψ.exists_monoidHom_asIdeal_eq_heckeCoeff S
  -- The divisor map `d`: `x` is integral at `w` exactly when the exponent of `w` in `d x` is
  -- nonnegative, the kernel is `Ô^×`, and a uniformiser at `w` goes to the prime `w`.
  obtain ⟨d, hd_count, hd_ker, hd_unif, -⟩ := exists_idele_divisor_hom (K := K)
  have h_integral {x : (𝔸f K)ˣ} {I : Ideal (𝓞 K)} (hx : (d x).val = I) : x.val ∈ Ô K :=
    mem_Ô.mpr fun w ↦ (hd_count x w).mpr (by simp [hx, count_coe_nonneg])
  set W : Set (𝔸f K)ˣ := (idelesUnitOff ∅ : Subgroup (𝔸f K)ˣ) ∩ V with hW
  have hW_vol : μ.real W ≠ 0 := measureReal_idelesUnitOff_empty_inter_ne_zero μ hV hV_one
  intro s hs
  let Z (x : (𝔸f K)ˣ) : ℂ := f x * ψ x * (finIdeleAbs x ^ s : ℝ)
  change Integrable Z μ ∧ ∫ x, Z x ∂μ = eulerProd (heckeCoeff ψ S) s * μ.real W
  -- On an idele of integral divisor, a uniformiser at `w` multiplies `Z` by `χ w * N w ^ (-s)`.
  have h_unif (w : FinPlace K) {x : (𝔸f K)ˣ} {I : Ideal (𝓞 K)} (hx : (d x).val = I) :
      Z (locIdele w (uniformizer w) * x) = χ w.asIdeal * w.q ^ (-s : ℂ) * Z x :=
    mul_finIdeleAbs_rpow_locIdele_uniformizer_mul h_supp h_local hχ_prime s w (h_integral hx)
      (h_integral (I := w.asIdeal * I) (by simp [hd_unif w, hx]))
  -- The part of `Z` of divisor `I`, by induction on the prime factorisation of `I`.
  have h_part (I : Ideal (𝓞 K)) : ∃ t : (𝔸f K)ˣ, ∀ x : (𝔸f K)ˣ,
      (if (d x).val = I then Z x else 0) = χ I * I.absNorm ^ (-s : ℂ) * W.indicator 1 (t * x) := by
    induction I using induction_on_prime with
    | h₁ => simp [hχ_zero]
    | h₂ u hu =>
      -- Divisor `1` means `x` is a unit idele; there `|x| = 1` and `f ψ` is the indicator of `V`.
      refine ⟨1, fun x ↦ ?_⟩
      rw [hu.eq_one]
      have h_div_one : d x = 1 ↔ x ∈ idelesUnitOff ∅ := by rw [← MonoidHom.mem_ker, hd_ker]
      have h_abs_one (hx : x ∈ idelesUnitOff ∅) : finIdeleAbs x = 1 := by
        simp [finIdeleAbs, ideleAbs_eq_prod_of_v_eq_one, mem_idelesUnitOff.mp hx]
      by_cases hx : x ∈ idelesUnitOff ∅
      · -- `↓` applies `map_one` before simp rewrites the ideal `1` as `⊤`.
        simp [Z, h_div_one.mpr hx, h_abs_one hx, h_units x hx, hW, hx, indicator, ↓map_one]
      · simp [h_div_one, hx, hW, indicator]
    | h₃ J p hJ_ne hp ih =>
      obtain ⟨t, ht⟩ := ih
      obtain ⟨w, rfl⟩ : ∃ w : FinPlace K, w.asIdeal = p := ⟨ofPrime hp, rfl⟩
      -- Write a general idele as `u * x` with `u = locIdele w (uniformizer w)`.
      refine ⟨t / locIdele w (uniformizer w), fun y ↦ ?_⟩
      obtain ⟨x, rfl⟩ := mul_left_surjective (locIdele w (uniformizer w)) y
      have h_coeff : χ (w.asIdeal * J) * ((w.asIdeal * J).absNorm : ℂ) ^ (-s : ℂ) =
          χ w.asIdeal * (w.asIdeal.absNorm : ℂ) ^ (-s : ℂ) * (χ J * J.absNorm ^ (-s : ℂ)) := by
        rw [map_mul, map_mul, Nat.cast_mul, natCast_mul_natCast_cpow, mul_mul_mul_comm]
      -- With `u = locIdele w (uniformizer w)`, the divisor of `u * x` is `w` times that of `x`, and
      -- `(t / u) * (u * x) = t * x`; so `ht` gives the part of divisor `J` on the right, and
      -- `h_unif` compares the two sides.
      rw [map_mul, hd_unif w, ← mul_assoc, div_mul_cancel, h_coeff, mul_assoc, ← ht]
      by_cases hx : (d x).val = J
      · simp [hx, h_unif w hx]
      · simp [ne_bot, hx]
  choose t ht using h_part
  -- Where `f x ≠ 0` the divisor `d x` is an integral ideal, so `Z` is the sum of its parts.
  have h_Z (x : (𝔸f K)ˣ) :
      Z x = ∑' I : Ideal (𝓞 K), χ I * I.absNorm ^ (-s : ℂ) * W.indicator 1 (t I * x) := by
    rw [← tsum_congr fun I ↦ ht I x]
    by_cases hf : f x = 0
    · simp [Z, hf]
    obtain ⟨hx_integral, hx_unit⟩ := h_supp x hf
    obtain ⟨I, hI⟩ : ∃ I : Ideal (𝓞 K), (d x).val = I :=
      exists_divisor_eq_coeIdeal_of_supp hd_count hx_integral hx_unit
    simp [hI, coeIdeal_inj]
  have h_countable : Countable (Ideal (𝓞 K)) :=
    .of_preimage_singleton fun N ↦ (Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 K) N).countable
  -- Integrate term by term; the coefficients `χ I * N I ^ (-s)` sum to the Euler product.
  have h_value : ∫ x, Z x ∂μ = eulerProd (heckeCoeff ψ S) s * μ.real W := by
    simp only [h_Z]
    rw [integral_tsum_mul_indicator_mul_left_of_hasSum μ
      ((isOpen_idelesUnitOff ∅).inter hV).measurableSet hW_vol (hasSum_eulerProd χ hχ_norm hs) t,
      funext hχ_prime]
  -- A function with nonzero integral is integrable, and the Euler product is an exponential.
  refine ⟨.of_integral_ne_zero ?_, h_value⟩
  simp [h_value, hW_vol, eulerProd_eq_exp hψ.norm_heckeCoeff_le hs]

open scoped Classical in
/-- Tate's zeta integral with the volume. Let `ψ` satisfy `IsHeckeOfType ψ n`, let `μ` be a Haar
measure on the finite ideles, and let `V` be an open set containing `1`. Let `f` satisfy three
conditions: it vanishes unless `x` is integral outside `S` and a unit at the places of `S`;
`f u * ψ u` is the indicator of `V` on the unit ideles `Ô^× = idelesUnitOff ∅`; and its value on
integral ideles depends only on their components at `S`. Then `μ (Ô^× ∩ V) ≠ 0`, and for every real
`s > 1` the function `f x * ψ x * |x| ^ s` is `μ`-integrable with integral
`eulerProd (heckeCoeff ψ S) s * μ (Ô^× ∩ V)`. -/
lemma tate_integral (hψ : IsHeckeOfType ψ n) (S : Set (FinPlace K)) (f : (𝔸f K)ˣ → ℂ)
    (V : Set (𝔸f K)ˣ) (μ : Measure (𝔸f K)ˣ) [μ.IsHaarMeasure] (hV : IsOpen V) (hV_one : 1 ∈ V)
    (h_supp : ∀ x : (𝔸f K)ˣ, f x ≠ 0 →
      (∀ w : FinPlace K, w ∉ S → v (x.val w) ≤ 1) ∧ ∀ w : FinPlace K, w ∈ S → v (x.val w) = 1)
    (h_units : ∀ u : (𝔸f K)ˣ, u ∈ idelesUnitOff ∅ → f u * ψ u = if u ∈ V then 1 else 0)
    (h_local : ∀ x y : (𝔸f K)ˣ, x.val ∈ Ô K → y.val ∈ Ô K →
      (∀ w : FinPlace K, w ∈ S → y.val w = x.val w) → f y = f x) :
    μ.real ((idelesUnitOff ∅ : Subgroup (𝔸f K)ˣ) ∩ V) ≠ 0 ∧
      ∀ s : ℝ, 1 < s →
        Integrable (fun x : (𝔸f K)ˣ ↦ f x * ψ x * (finIdeleAbs x ^ s : ℝ)) μ ∧
          ∫ x : (𝔸f K)ˣ, f x * ψ x * (finIdeleAbs x ^ s : ℝ) ∂μ =
            eulerProd (heckeCoeff ψ S) s * μ.real ((idelesUnitOff ∅ : Subgroup (𝔸f K)ˣ) ∩ V) :=
  ⟨measureReal_idelesUnitOff_empty_inter_ne_zero μ hV hV_one,
    hψ.integral_mul_finIdeleAbs_rpow_eq_eulerProd_mul S f V μ hV hV_one h_supp h_units h_local⟩

open InfinitePlace Pi in
/-- The embedding `Φ w : K →+* ℂ` that `PlaceEmbedding K` chooses at the infinite place `w` extends
to a continuous `ℝ`-algebra map `p` on `K ⊗ ℝ = mixedEmbedding.mixedSpace K`:
`p (mixedEmbedding K x) = Φ w x` for `x : K`. -/
lemma exists_continuousAlgHom_mixedEmbedding_eq (w : InfinitePlace K) :
    ∃ p : mixedEmbedding.mixedSpace K →A[ℝ] ℂ, ∀ x : K, p (mixedEmbedding K x) = Φ w x := by
  classical
  -- Take the coordinate at `w`, conjugated if `Φ w` is not `w.embedding`.
  let coord : mixedEmbedding.mixedSpace K →ₐ[ℝ] ℂ :=
    if hw : w.IsReal then ofRealAm.comp ((evalAlgHom _ _ ⟨w, hw⟩).comp (AlgHom.fst ℝ _ _))
    else (evalAlgHom _ _ ⟨w, not_isReal_iff_isComplex.mp hw⟩).comp (AlgHom.snd ℝ _ _)
  have h_coord (x : K) : coord (mixedEmbedding K x) = w.embedding x := by aesop
  let p : mixedEmbedding.mixedSpace K →ₐ[ℝ] ℂ :=
    .comp (if w.embedding = Φ w then AlgHom.id ℝ ℂ else conjAe) coord
  refine ⟨⟨p, p.toLinearMap.continuous_of_finiteDimensional⟩, fun x ↦ ?_⟩
  by_cases h_eq : w.embedding = Φ w
  · simp [p, h_eq, h_coord]
  · -- `w.embedding` is `Φ w` or its conjugate, since `Φ w` induces the place `w`.
    have h_conj : w.embedding = ComplexEmbedding.conjugate (Φ w) := by
      simpa [mk_Φ, h_eq] using embedding_mk_eq (Φ w)
    simp only [p, ite_eq_right h_eq]
    simp [h_coord, h_conj]

open Units in
/-- Let `ψ` satisfy `IsHeckeOfType ψ n`. There is a finite idele `d`, a level of `ψ`, such that
every idele `y` with `d * (y - 1) ∈ Ô K` is integral (`Ô K`: the finite adeles that are integral
everywhere) and, if `y` is a unit idele (`y ∈ idelesUnitOff ∅`), satisfies `ψ y = 1`. -/
lemma exists_level (hψ : IsHeckeOfType ψ n) :
    ∃ d : (𝔸f K)ˣ, ∀ y : (𝔸f K)ˣ, d * (y.val - 1) ∈ Ô K →
      y.val ∈ Ô K ∧ (y ∈ idelesUnitOff ∅ → ψ y = 1) := by
  -- The unit ideles outside the open kernel of `ψ` form a compact set that misses `1`, so its
  -- complement in `Ô` contains `1 + M Ô` for some integer `M ≠ 0`.
  let U : Set (𝔸f K) :=
    SetLike.coe (Ô K) \ val '' (SetLike.coe (idelesUnitOff ∅) \ (ψ.ker : Set (𝔸f K)ˣ))
  have h_closed : IsClosed (val '' (SetLike.coe (idelesUnitOff ∅) \ (ψ.ker : Set (𝔸f K)ˣ))) :=
    ((isCompact_idelesUnitOff_empty.diff hψ.isOpen_ker).image continuous_val).isClosed
  have hU : U ∈ nhds 1 := (isOpen_Ô.sdiff h_closed).mem_nhds (by simp)
  obtain ⟨M, hM, h_nhds⟩ : ∃ M : ℕ, M ≠ 0 ∧ ∀ x ∈ Ô K, M * x + 1 ∈ U :=
    mem_nhds_zero_finAdele_iff.mp ((map_add_right_nhds_zero 1).le hU)
  let d : (𝔸f K)ˣ := (isUnit_natCast_finAdele (E := K) hM).unit⁻¹
  refine ⟨d, fun y hy ↦ ?_⟩
  -- With `d = M⁻¹`, the point `M * (d * (y - 1)) + 1` of `U` is `y` itself.
  have h_mem : y.val ∈ U := by simpa [d, ← mul_assoc] using h_nhds (d * (y.val - 1)) hy
  simpa [U, val_inj] using h_mem

open InfinitePlace Units Real ZetaIntegral Module DFunLike in
/-- Let `ψ ≠ 1` be the finite part of a Hecke character of type `n` (`IsHeckeOfType ψ n`): its
kernel is open, and `ψ x * ∏ w, (Φ w x / ‖Φ w x‖) ^ n w = 1` for `x ∈ Kˣ`. Then `ψ` extends to a
homomorphism `X` to `ℂ` from the idele group `(K ⊗ ℝ)ˣ × (𝔸f K)ˣ` with four properties. `X` is
trivial on the principal ideles `principalIdeles K` (the diagonal image of `Kˣ`),
`X (t, a) = X (t, 1) * ψ a`, `X` is continuous in the infinite component, and `X c ≠ 1` for some
idele `c` with `ideleModule c = 1`. -/
lemma exists_idele_character (hψ : IsHeckeOfType ψ n) (hψ_ne : ψ ≠ 1) :
    ∃ X : (mixedEmbedding.mixedSpace K)ˣ × (𝔸f K)ˣ →* ℂ,
      (∀ γ : principalIdeles K, X γ = 1) ∧
      (∀ (t : (mixedEmbedding.mixedSpace K)ˣ) (a : (𝔸f K)ˣ), X (t, a) = X (t, 1) * ψ a) ∧
      Continuous (fun t : (mixedEmbedding.mixedSpace K)ˣ ↦ X (t, 1)) ∧
      ∃ c : (mixedEmbedding.mixedSpace K)ˣ × (𝔸f K)ˣ, ideleModule c = 1 ∧ X c ≠ 1 := by
  -- Take `X (t, a) = ∏ w, (p w t / ‖p w t‖) ^ n w * ψ a`, with `p w` the extension of `Φ w`.
  choose p hp using exists_continuousAlgHom_mixedEmbedding_eq (K := K)
  -- The homomorphism `arg` is `z ↦ z / ‖z‖`.
  let arg : ℂˣ →* ℂˣ := .id ℂˣ / map (ofRealHom.toMonoidHom.comp normHom.toMonoidHom)
  have h_arg (z : ℂˣ) : (arg z : ℂ) = z / ‖z.val‖ := by simp [arg]
  let X : (mixedEmbedding.mixedSpace K)ˣ × (𝔸f K)ˣ →* ℂ := (coeHom ℂ).comp <|
    .coprod (∏ w, (arg.comp (map (p w).toAlgHom.toRingHom.toMonoidHom)) ^ n w) ψ
  have hX_apply (t : (mixedEmbedding.mixedSpace K)ˣ) (a : (𝔸f K)ˣ) :
      X (t, a) = (∏ w : InfinitePlace K, (p w t.val / (‖p w t.val‖ : ℂ)) ^ n w) * ψ a := by
    simp [X, h_arg]
  refine ⟨X, ?_, fun t a ↦ by simp [hX_apply], ?_, ?_⟩
  · -- On the principal idele of `x`, `X` is the left side of the defining identity of `ψ`.
    rintro ⟨_, x, rfl⟩
    simpa [hX_apply, hp, mul_comm] using hψ.apply_principalIdele_mul_prod_eq_one x
  · -- At infinity `X` is a product of powers of the continuous maps `t ↦ p w t / ‖p w t‖`.
    simp only [hX_apply]
    -- `↓` applies `IsUnit.map` to `p w t` before simp unfolds the unit `t`.
    fun_prop (disch := simp [IsUnit.ne_zero, ↓IsUnit.map])
  · -- Take `a` with `ψ a ≠ 1` and rescale it to module one by a positive real at infinity.
    obtain ⟨a, ha⟩ : ∃ a : (𝔸f K)ˣ, ψ a ≠ 1 := exists_ne hψ_ne
    have h_pos : 0 < ideleModule (1, a⁻¹) ^ (finrank ℚ K : ℝ)⁻¹ :=
      rpow_pos_of_pos (ideleModule_pos _) _
    refine ⟨(map (algebraMap ℝ _).toMonoidHom (mk0 _ h_pos.ne'), a), ?_, ?_⟩
    · -- The norm of the real number `r` at infinity is `r ^ [K : ℚ] = |a|⁻¹`, so the module is one.
      -- `↓` uses `mixedEmbedding.finrank` before simp splits the dimension over the real and
      -- complex places.
      simp [ideleModule, finIdeleAbs, ↓mixedEmbedding.finrank, rpow_inv_natCast_pow,
        finrank_pos.ne', abs_of_nonneg, -Prod.algebraMap_apply]
    · -- A positive real number at infinity does not change `X`, so `X (r, a) = ψ a`.
      simpa [X, arg, abs_of_pos h_pos, h_pos.ne', -Prod.algebraMap_apply] using ha

open scoped Classical in
omit [PlaceEmbedding K] in
open Units Real ZetaIntegral in
/-- The zeta integral at infinity. Let `χ` be a continuous function on the units of `K ⊗ ℝ` (the
mixed space) with `χ 1 = 1`, and integrate `χ t * |t| ^ s` against the tent `max (ρ - dist t 1) 0`,
where `|t| = ideleModule (t, 1)` is the absolute value of the norm of `t`. There is `0 < r < 1` such
that for every `ρ ≤ r` the integrand is integrable for all real `s`, and for `0 < ρ ≤ r` the
integral does not vanish at `s = 1`. -/
lemma exists_radius_tent_integral_ne_zero {χ : (mixedEmbedding.mixedSpace K)ˣ → ℂ}
    (hχ_cont : Continuous χ) (hχ_one : χ 1 = 1) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∀ ρ ≤ r,
      (∀ s : ℝ, Integrable (fun t : (mixedEmbedding.mixedSpace K)ˣ ↦
        max (ρ - dist t.val 1) 0 * χ t * (ideleModule (t, 1) ^ s : ℝ)) .haar) ∧
      (0 < ρ → ∫ t : (mixedEmbedding.mixedSpace K)ˣ,
        max (ρ - dist t.val 1) 0 * χ t * (ideleModule (t, 1) ^ (1 : ℝ) : ℝ) ∂.haar ≠ 0) := by
  let A (ρ s : ℝ) (t : (mixedEmbedding.mixedSpace K)ˣ) : ℂ :=
    max (ρ - dist t.val 1) 0 * χ t * (ideleModule (t, 1) ^ s : ℝ)
  have hA_cont (ρ s : ℝ) : Continuous (A ρ s) := by fun_prop (disch := simp [ne_of_gt])
  -- On a closed ball of radius `r` at `1` all points are units and `χ` has positive real part.
  have h_nhds : val '' (χ ⁻¹' {z : ℂ | 0 < z.re}) ∈ nhds (1 : mixedEmbedding.mixedSpace K) :=
    isOpenMap_val.image_mem_nhds
      (hχ_cont.tendsto 1 ((isOpen_re_gt 0).mem_nhds (by simp [hχ_one])))
  obtain ⟨r, hr, h_ball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp h_nhds
  -- As `0` is not a unit, it is not in the ball, so `r < 1`.
  have hr_one : r < 1 := by
    by_contra! h_le
    obtain ⟨u, -, hu⟩ := h_ball (a := 0) (by simpa using h_le)
    exact u.ne_zero hu
  refine ⟨r, hr, hr_one, fun ρ hρ ↦ ?_⟩
  -- The tent of radius `ρ` is supported in the ball, which is compact in the units.
  have h_compact : IsCompact (val ⁻¹' Metric.closedBall (1 : mixedEmbedding.mixedSpace K) r) :=
    isOpenEmbedding_val.isCompact_preimage' (isCompact_closedBall 1 r)
      (h_ball.trans (Set.image_subset_range _ _))
  have hA_int (s : ℝ) : Integrable (A ρ s) .haar := by
    refine (hA_cont ρ s).integrable_of_hasCompactSupport (.intro h_compact fun t ht ↦ ?_)
    have h_le : ρ ≤ dist t.val 1 := hρ.trans (not_le.mp ht).le
    simp [A, h_le]
  refine ⟨hA_int, fun hρ_pos ↦ ?_⟩
  -- The real part of the integrand is nonnegative, and positive at `1`.
  have h_nonneg (t : (mixedEmbedding.mixedSpace K)ˣ) : 0 ≤ (A ρ 1 t).re := by
    by_cases! ht : ρ ≤ dist t.val 1
    · simp [A, ht]
    have hχ_pos : 0 < (χ t).re := by simpa [val_inj] using h_ball (ht.le.trans hρ)
    calc 0 ≤ max (ρ - dist t.val 1) 0 * (χ t).re * ideleModule (t, 1) := by
          positivity [ideleModule_pos (t, 1)]
      _ = (A ρ 1 t).re := by simp [A]
  have h_pos : 0 < ∫ t, (A ρ 1 t).re ∂.haar :=
    integral_pos_of_integrable_nonneg_nonzero (x := 1) (by fun_prop) (hA_int 1).re h_nonneg
      (by simpa [A, hχ_one, Prod.mk_one_one, hρ_pos.le] using hρ_pos.ne')
  exact ne_zero_of_re_pos (h_pos.trans_eq (integral_re (hA_int 1)))

open NumberField.mixedEmbedding (mixedSpace)

/-- Let `v` be a valuation and `a`, `x` elements with `1 < v a` and `v a * v (x - 1) ≤ 1`. Then
`v x = 1`, because the second hypothesis forces `v (x - 1) < 1`. -/
private theorem _root_.Valuation.map_eq_one_of_one_lt_of_mul_map_sub_one_le {R Γ₀ : Type*}
    [Ring R] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation R Γ₀) {a x : R} (ha : 1 < v a)
    (h_mul : v a * v (x - 1) ≤ 1) : v x = 1 := by
  have h_sub : v (x - 1) < v 1 := by
    rw [map_one]
    by_contra! h_ge
    exact (ha.trans_le (le_mul_of_one_le_right' h_ge)).not_ge h_mul
  rw [← sub_add_cancel x 1, v.map_add_eq_of_lt_right h_sub, map_one]

/-- Let `v` be a valuation and `a`, `x` elements with `v a ≤ 1` and `v x ≤ 1`. Then
`v a * v (x - 1) ≤ 1`. -/
private theorem _root_.Valuation.mul_map_sub_one_le_one_of_map_le_one {R Γ₀ : Type*} [Ring R]
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation R Γ₀) {a x : R} (ha : v a ≤ 1)
    (hx : v x ≤ 1) : v a * v (x - 1) ≤ 1 :=
  mul_le_one' ha (v.map_sub_le hx (map_one v).le)

open Valuation ZetaIntegral in
/-- The zeta integral at the finite places. Let `ψ` be the finite part of a Hecke character of type
`n` (`IsHeckeOfType ψ n`). There are a level `d`, a finite set `T` of finite places and a constant
`κ ≠ 0` such that, for real `s > 1`, the function `ψ x * |x| ^ s` times the indicator
`adelicTent 1 d (1, x)` of `1 + d⁻¹ Ô` is integrable on the finite ideles, and its integral is `κ`
times the Euler product `eulerProd (heckeCoeff ψ T) s` over the places outside `T`. Here
`|x| = finIdeleAbs x` is the module of `x`. -/
lemma exists_level_tate_integral (h : IsHeckeOfType ψ n) :
    ∃ (d : (𝔸f K)ˣ) (T : Finset (FinPlace K)) (κ : ℂ), κ ≠ 0 ∧ ∀ s : ℝ, 1 < s →
      Integrable (fun x : (𝔸f K)ˣ ↦
        (adelicTent 1 d (1, x.val) : ℂ) * ψ x * (finIdeleAbs x ^ s : ℝ)) .haar ∧
      ∫ x : (𝔸f K)ˣ, (adelicTent 1 d (1, x.val) : ℂ) * ψ x * (finIdeleAbs x ^ s : ℝ) ∂.haar =
        eulerProd (heckeCoeff ψ T) s * κ := by
  classical
  -- Elements of `1 + d⁻¹ Ô` are integral, and `ψ = 1` on the units among them. Apply
  -- `tate_integral` with `T` the places where `d` is not integral.
  obtain ⟨d, h_level⟩ := h.exists_level
  have h_fin : {w : FinPlace K | ¬v (d.val w) ≤ 1}.Finite :=
    Filter.eventually_cofinite.mp (d.val.property.mono fun w hw ↦
      (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K w).mp hw)
  obtain ⟨T, hT⟩ : ∃ T : Finset (FinPlace K), ∀ w : FinPlace K, w ∈ T ↔ ¬v (d.val w) ≤ 1 :=
    h_fin.exists_finset
  let f (x : (𝔸f K)ˣ) : ℂ := adelicTent 1 d (1, x.val)
  have h_mem (x : 𝔸f K) : d.val * (x - 1) ∈ Ô K ↔ ∀ w, v (d.val w) * v (x w - 1) ≤ 1 := by
    simp only [mem_Ô, finAdele_mul_apply, finAdele_sub_apply, finAdele_one_apply, map_mul]
  have h_supp (x : (𝔸f K)ˣ) (hx : f x ≠ 0) :
      (∀ w : FinPlace K, w ∉ T → v (x.val w) ≤ 1) ∧ ∀ w : FinPlace K, w ∈ T → v (x.val w) = 1 := by
    have hx_mem : d.val * (x.val - 1) ∈ Ô K := by
      by_contra hx_not
      simp [f, hx_not] at hx
    refine ⟨fun w _ ↦ mem_Ô.mp (h_level x hx_mem).1 w, fun w hw ↦ ?_⟩
    -- At `w ∈ T`, `1 < v (d w)` and `v (d w) * v (x w - 1) ≤ 1` give `v (x w) = 1`.
    have hd : 1 < v (d.val w) := not_le.mp ((hT w).mp hw)
    exact Valuation.map_eq_one_of_one_lt_of_mul_map_sub_one_le Valued.v hd
      ((h_mem x).mp hx_mem w)
  -- On a unit `u` with `d (u - 1) ∈ Ô` the tent is `1` and `ψ u = 1` (`h_level`); else it is `0`.
  have h_units : ∀ u : (𝔸f K)ˣ, u ∈ idelesUnitOff ∅ →
      f u * ψ u = if u ∈ {y : (𝔸f K)ˣ | d * (y.val - 1) ∈ Ô K} then 1 else 0 := by
    simp +contextual [f, h_level, apply_ite ofReal]
  have h_local (x y : (𝔸f K)ˣ) (hx : x.val ∈ Ô K) (hy : y.val ∈ Ô K)
      (h_eq : ∀ w : FinPlace K, w ∈ T → y.val w = x.val w) : f y = f x := by
    -- Outside `T` the condition `v (d w) * v (x w - 1) ≤ 1` holds for every integral `x`.
    have h_off {z : 𝔸f K} (hz : z ∈ Ô K) {w : FinPlace K} (hw : w ∉ T) :
        v (d.val w) * v (z w - 1) ≤ 1 :=
      Valued.v.mul_map_sub_one_le_one_of_map_le_one (by simpa [hT] using hw) (mem_Ô.mp hz w)
    have h_cond : d.val * (y.val - 1) ∈ Ô K ↔ d.val * (x.val - 1) ∈ Ô K := by
      rw [h_mem, h_mem]
      refine forall_congr' fun w ↦ ?_
      by_cases hw : w ∈ T
      · rw [h_eq w hw]
      · exact iff_of_true (h_off hy hw) (h_off hx hw)
    simp [f, h_cond]
  -- `κ` is the volume of the unit ideles in `1 + d⁻¹ Ô`.
  obtain ⟨h_vol, h_tate⟩ := h.tate_integral T f {y | d * (y.val - 1) ∈ Ô K} .haar
    isOpen_Ô.preimage_of_continuous (by simp) h_supp h_units h_local
  exact ⟨d, T, _, ofReal_ne_zero.mpr h_vol, h_tate⟩

omit [PlaceEmbedding K] in
open Units ZetaIntegral in
/-- Unfolding. Let `X` be a character of the ideles `a = (t, x)` (`t` at infinity, `x` at the
finite places) that is trivial on the principal ideles, and suppose that `X a` times the tent
`adelicTent ρ d a` times `|a| ^ s` is `A t * B x`, with `A` and `B` integrable. Here
`|a| = ideleModule a` is the module of `a`. Translate by an idele `g` of module one.
Then `X g * X a` times the theta sum `∑' γ, adelicTent ρ d (γ * g * a)` over the principal ideles
`γ` times `|a| ^ s` is integrable on the idele classes (the quotient of the Haar measure), with
integral `(∫ A) * ∫ B`. -/
lemma integral_tsum_adelicTent_eq_mul [DiscreteTopology (principalIdeles K)]
    {X : (mixedSpace K)ˣ × (𝔸f K)ˣ →* ℂ} (hX_principal : ∀ γ : principalIdeles K, X γ = 1)
    {ρ s : ℝ} {d : (𝔸f K)ˣ} {A : (mixedSpace K)ˣ → ℂ} {B : (𝔸f K)ˣ → ℂ}
    (hA : Integrable A .haar) (hB : Integrable B .haar)
    (h_split : ∀ a : (mixedSpace K)ˣ × (𝔸f K)ˣ,
      A a.fst * B a.snd = X a * adelicTent ρ d (a.map val val) * (ideleModule a ^ s : ℝ))
    {g : (mixedSpace K)ˣ × (𝔸f K)ˣ} (hg : ideleModule g = 1) :
    Integrable (fun a : (mixedSpace K)ˣ × (𝔸f K)ˣ ↦ X g * X a *
        (∑' γ : principalIdeles K, adelicTent ρ d ((γ.val * (g * a)).map val val) : ℝ) *
        (ideleModule a ^ s : ℝ)) ((principalIdeles K).quotMeasure (Measure.haar.prod .haar)) ∧
      ∫ a : (mixedSpace K)ˣ × (𝔸f K)ˣ, X g * X a *
        (∑' γ : principalIdeles K, adelicTent ρ d ((γ.val * (g * a)).map val val) : ℝ) *
        (ideleModule a ^ s : ℝ) ∂(principalIdeles K).quotMeasure (Measure.haar.prod .haar) =
      (∫ t : (mixedSpace K)ˣ, A t ∂.haar) * ∫ x : (𝔸f K)ˣ, B x ∂.haar := by
  -- Apply Weil's formula for the principal ideles to `a ↦ A t * B x` at `g * a`.
  obtain ⟨h_weil_int, h_weil_eq⟩ :=
    integral_quotMeasure_tsum (principalIdeles K) ((hA.mul_prod hB).comp_mul_left g)
  -- As `X γ = 1` and `|γ| = 1` for principal `γ` and `|g| = 1`, the integrand is the sum of
  -- `A t * B x` over the translates `g * γ * a`.
  have h_integrand (a : (mixedSpace K)ˣ × (𝔸f K)ˣ) : X g * X a *
      (∑' γ : principalIdeles K, adelicTent ρ d ((γ.val * (g * a)).map val val) : ℝ) *
      (ideleModule a ^ s : ℝ) =
      ∑' γ : principalIdeles K, A (g * (γ.val * a)).fst * B (g * (γ.val * a)).snd := by
    simp only [h_split, mul_left_comm g, map_mul X, map_mul ideleModule, hX_principal, hg,
      ideleModule_principal_eq_one, one_mul, tsum_mul_left, tsum_mul_right, ← ofReal_tsum]
  simp only [h_integrand]
  refine ⟨h_weil_int, h_weil_eq.trans ?_⟩
  rw [integral_mul_left_eq_self (fun a ↦ A a.fst * B a.snd) g, integral_prod_mul]

open scoped Classical in
omit [PlaceEmbedding K] in
open Units Real ZetaIntegral in
/-- Unfolding for the tent of radius `ρ` at infinity and the level tent at the finite places. Let
`X` be trivial on the principal ideles with `X (t, x) = X (t, 1) * ψ x`, `g` of module one, and the
integrands at infinity and at the finite places integrable. Then `X g * X a` times the theta sum
`∑' γ, adelicTent ρ d (γ * g * a)` times `|a| ^ s` is integrable on the idele classes, and its
integral is the integral at infinity times the integral `I` at the finite places. -/
private lemma integral_tsum_adelicTent_eq_integral_mul [DiscreteTopology (principalIdeles K)]
    {X : (mixedSpace K)ˣ × (𝔸f K)ˣ →* ℂ} (hX_principal : ∀ γ : principalIdeles K, X γ = 1)
    (hX_split : ∀ (t : (mixedSpace K)ˣ) (x : (𝔸f K)ˣ), X (t, x) = X (t, 1) * ψ x)
    {ρ s : ℝ} {d : (𝔸f K)ˣ} {I : ℂ}
    (hA : Integrable (fun t : (mixedSpace K)ˣ ↦
      max (ρ - dist t.val 1) 0 * X (t, 1) * (ideleModule (t, 1) ^ s : ℝ)) .haar)
    (hB : Integrable (fun x : (𝔸f K)ˣ ↦
      (adelicTent 1 d (1, x.val) : ℂ) * ψ x * (finIdeleAbs x ^ s : ℝ)) .haar)
    (hB_eq : ∫ x : (𝔸f K)ˣ, (adelicTent 1 d (1, x.val) : ℂ) * ψ x * (finIdeleAbs x ^ s : ℝ)
      ∂.haar = I)
    {g : (mixedSpace K)ˣ × (𝔸f K)ˣ} (hg : ideleModule g = 1) :
    Integrable (fun a : (mixedSpace K)ˣ × (𝔸f K)ˣ ↦ X g * X a *
        (∑' γ : principalIdeles K, adelicTent ρ d ((γ.val * (g * a)).map val val) : ℝ) *
        (ideleModule a ^ s : ℝ)) ((principalIdeles K).quotMeasure (Measure.haar.prod .haar)) ∧
      ∫ a : (mixedSpace K)ˣ × (𝔸f K)ˣ, X g * X a *
        (∑' γ : principalIdeles K, adelicTent ρ d ((γ.val * (g * a)).map val val) : ℝ) *
        (ideleModule a ^ s : ℝ) ∂(principalIdeles K).quotMeasure (Measure.haar.prod .haar) =
      (∫ t : (mixedSpace K)ˣ,
        max (ρ - dist t.val 1) 0 * X (t, 1) * (ideleModule (t, 1) ^ s : ℝ) ∂.haar) * I := by
  -- The integrand factors as the integrand at infinity times the integrand at the finite places.
  have h_split (a : (mixedSpace K)ˣ × (𝔸f K)ˣ) :
      max (ρ - dist a.fst.val 1) 0 * X (a.fst, 1) * (ideleModule (a.fst, 1) ^ s : ℝ) *
        ((adelicTent 1 d (1, a.snd.val) : ℂ) * ψ a.snd * (finIdeleAbs a.snd ^ s : ℝ)) =
      X a * adelicTent ρ d (a.map val val) * (ideleModule a ^ s : ℝ) := by
    by_cases ha : d * (a.snd.val - 1) ∈ Ô K
    · -- Split the module of `a` into its two factors; the sides then differ only in the order.
      simp [ha, hX_split a.fst a.snd, ideleModule, mul_rpow, finIdeleAbs]
      ring
    · simp [ha]
  rw [← hB_eq]
  exact integral_tsum_adelicTent_eq_mul hX_principal hA hB h_split hg

/-- Finite integral of a difference, for a Mellin-type integrand. Let `N > 0` and suppose that
`|θ₁ a - θ₂ a| ≤ C * N a ^ δ * (|φ₁ a| + |φ₂ a|)` for all `a`, and that `u * φ₁ * N ^ (σ + δ)` and
`u * φ₂ * N ^ (σ + δ)` are integrable. Then `u * (θ₁ - θ₂) * N ^ σ` has finite integral. -/
private theorem _root_.MeasureTheory.hasFiniteIntegral_mul_sub_mul_rpow_of_abs_sub_le
    {G : Type*} [MeasurableSpace G] {μ : Measure G} {N : G → ℝ} (hN_pos : ∀ a : G, 0 < N a)
    {u : G → ℂ} {θ₁ θ₂ φ₁ φ₂ : G → ℝ} {C δ σ : ℝ}
    (h₁ : Integrable (fun a : G ↦ u a * φ₁ a * (N a ^ (σ + δ) : ℝ)) μ)
    (h₂ : Integrable (fun a : G ↦ u a * φ₂ a * (N a ^ (σ + δ) : ℝ)) μ)
    (h_le : ∀ a : G, |θ₁ a - θ₂ a| ≤ C * N a ^ δ * (|φ₁ a| + |φ₂ a|)) :
    HasFiniteIntegral (fun a : G ↦ u a * ((θ₁ a : ℂ) - θ₂ a) * (N a ^ σ : ℝ)) μ := by
  refine ((h₁.norm.add h₂.norm).const_mul C).hasFiniteIntegral.mono' (.of_forall fun a ↦ ?_)
  have h_norm (x τ : ℝ) : ‖u a * x * (N a ^ τ : ℝ)‖ = ‖u a‖ * |x| * N a ^ τ := by
    simp [abs_of_pos (Real.rpow_pos_of_pos (hN_pos a) τ)]
  calc ‖u a * ((θ₁ a : ℂ) - θ₂ a) * (N a ^ σ : ℝ)‖
      = ‖u a‖ * |θ₁ a - θ₂ a| * N a ^ σ := by rw [← Complex.ofReal_sub, h_norm]
    _ ≤ ‖u a‖ * (C * N a ^ δ * (|φ₁ a| + |φ₂ a|)) * N a ^ σ := by
        gcongr
        exacts [Real.rpow_nonneg (hN_pos a).le σ, h_le a]
    _ = C * (‖u a * φ₁ a * (N a ^ (σ + δ) : ℝ)‖ + ‖u a * φ₂ a * (N a ^ (σ + δ) : ℝ)‖) := by
        rw [h_norm, h_norm, Real.rpow_add (hN_pos a)]
        ring

/-- Comparison through a common approximation. Suppose that for every `l > 0` some number `i` is
within `C * l ^ δ * |φ b|` of `θ b` for all `b` with `N b = l`. If `0 < N a` and `N b = N a`, then
`|θ a - θ b| ≤ C * N a ^ δ * (|φ a| + |φ b|)`. -/
private theorem _root_.abs_sub_le_mul_rpow_of_forall_exists_abs_sub_le {G : Type*}
    {N θ φ : G → ℝ} {C δ : ℝ}
    (h_approx : ∀ l > (0 : ℝ), ∃ i : ℝ, ∀ b : G, N b = l → |i - θ b| ≤ C * l ^ δ * |φ b|)
    {a b : G} (ha_pos : 0 < N a) (h_eq : N b = N a) :
    |θ a - θ b| ≤ C * N a ^ δ * (|φ a| + |φ b|) := by
  obtain ⟨i, hi⟩ := h_approx (N a) ha_pos
  calc |θ a - θ b| ≤ |i - θ a| + |i - θ b| := by
        rw [abs_sub_comm i (θ a)]
        exact abs_sub_le (θ a) i (θ b)
    _ ≤ C * N a ^ δ * |φ a| + C * N a ^ δ * |φ b| := add_le_add (hi a rfl) (hi b h_eq)
    _ = C * N a ^ δ * (|φ a| + |φ b|) := by ring

open Units Real ZetaIntegral in
/-- Let `ψ ≠ 1` be the finite part of a Hecke character of type `n` (`IsHeckeOfType ψ n`). There
are a finite set `T` of finite places and functions `F G : ℝ → ℂ`, both analytic at `1`, with
`G 1 ≠ 0` and `F s = G s * eulerProd (heckeCoeff ψ T) s` for real `s > 1`, where
`eulerProd (heckeCoeff ψ T)` is the Euler product of `ψ` over the places outside `T`. -/
lemma exists_analyticAt_one_mul_eulerProd (h : IsHeckeOfType ψ n) (hψ_ne : ψ ≠ 1) :
    ∃ (T : Finset (FinPlace K)) (F G : ℝ → ℂ), AnalyticAt ℝ F 1 ∧ AnalyticAt ℝ G 1 ∧ G 1 ≠ 0 ∧
      ∀ s : ℝ, 1 < s → F s = G s * eulerProd (heckeCoeff ψ T) s := by
  classical
  -- Unfold the zeta integral over the idele classes into an integral of a theta sum. The
  -- difference of two translates converges a little to the left of `1`, so is analytic at `1`.
  -- We translate by an idele `c` of module one with `X c ≠ 1`, for `X` the idele character.
  obtain ⟨X, hX_principal, hX_split, hX_cont, c, hc_mod, hc⟩ := h.exists_idele_character hψ_ne
  -- The integrand `A` at infinity, for a tent of radius `ρ` at `1`.
  let A (ρ s : ℝ) (t : (mixedSpace K)ˣ) : ℂ :=
    max (ρ - dist t.val 1) 0 * X (t, 1) * (ideleModule (t, 1) ^ s : ℝ)
  obtain ⟨r, hr, hr_one, h_tent⟩ : ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∀ ρ ≤ r,
      (∀ s : ℝ, Integrable (A ρ s) .haar) ∧ (0 < ρ → ∫ t, A ρ 1 t ∂.haar ≠ 0) :=
    exists_radius_tent_integral_ne_zero hX_cont (map_one X)
  have h_third : r / 3 ≤ r := div_le_self hr.le (by norm_num)
  obtain ⟨hA_int, hA_ne⟩ := h_tent (r / 3) h_third
  -- The integral at the finite places is the Euler product outside `T` times `κ ≠ 0`.
  obtain ⟨d, T, κ, hκ, h_tate⟩ := h.exists_level_tate_integral
  -- The theta sum of radius `r / 3` at an idele of module `l` is a number `i` depending only on
  -- `l`, up to an error of `C * l ^ δ` times the theta sum of radius `r`.
  let Θ (ρ : ℝ) (a : (mixedSpace K)ˣ × (𝔸f K)ˣ) : ℝ :=
    ∑' γ : principalIdeles K, adelicTent ρ d ((γ.val * a).map val val)
  obtain ⟨h_discrete, δ, hδ, C, h_approx⟩ : DiscreteTopology (principalIdeles K) ∧
      ∃ δ > (0 : ℝ), ∃ C : ℝ, ∀ l > (0 : ℝ), ∃ i : ℝ,
        ∀ a, ideleModule a = l → |i - Θ (r / 3) a| ≤ C * l ^ δ * |Θ r a| :=
    exists_abs_sub_thetaSum_le r d hr hr_one
  -- As `a` and `c * a` have the same module, the main terms cancel in the difference.
  have h_diff (a : (mixedSpace K)ˣ × (𝔸f K)ˣ) : |Θ (r / 3) a - Θ (r / 3) (c * a)| ≤
      C * ideleModule a ^ δ * (|Θ r a| + |Θ r (c * a)|) :=
    abs_sub_le_mul_rpow_of_forall_exists_abs_sub_le h_approx (ideleModule_pos a) (by simp [hc_mod])
  -- Unfolding: the integral of `X Θ ideleModule ^ s` over the idele classes, also after a
  -- translation by an idele `g` of module one, is the product of the infinite and the finite part.
  let μ : Measure ((mixedSpace K)ˣ × (𝔸f K)ˣ) :=
    (principalIdeles K).quotMeasure (Measure.haar.prod .haar)
  have h_unfold {ρ : ℝ} (hρ : ρ ≤ r) {g : (mixedSpace K)ˣ × (𝔸f K)ˣ} (hg : ideleModule g = 1)
      {s : ℝ} (hs : 1 < s) :
      Integrable (fun a ↦ X g * X a * Θ ρ (g * a) * (ideleModule a ^ s : ℝ)) μ ∧
      ∫ a, X g * X a * Θ ρ (g * a) * (ideleModule a ^ s : ℝ) ∂μ =
        (∫ t, A ρ s t ∂.haar) * (eulerProd (heckeCoeff ψ T) s * κ) := by
    obtain ⟨hB_int, hB_eq⟩ := h_tate s hs
    exact integral_tsum_adelicTent_eq_integral_mul hX_principal hX_split ((h_tent ρ hρ).1 s)
      hB_int hB_eq hg
  have h_one {ρ : ℝ} (hρ : ρ ≤ r) {s : ℝ} (hs : 1 < s) :
      Integrable (fun a ↦ X a * Θ ρ a * (ideleModule a ^ s : ℝ)) μ ∧
      ∫ a, X a * Θ ρ a * (ideleModule a ^ s : ℝ) ∂μ =
        (∫ t, A ρ s t ∂.haar) * (eulerProd (heckeCoeff ψ T) s * κ) := by
    simpa only [map_one, one_mul] using h_unfold hρ (map_one ideleModule) hs
  -- Compare the translates by `1` and `c`: the difference `D` has integral `(X c - 1)` times the
  -- product above.
  let D (s : ℝ) (a : (mixedSpace K)ˣ × (𝔸f K)ˣ) : ℂ :=
    X c * X a * (Θ (r / 3) a - Θ (r / 3) (c * a)) * (ideleModule a ^ s : ℝ)
  have hD {s : ℝ} (hs : 1 < s) : Integrable (D s) μ ∧ ∫ a, D s a ∂μ =
      (X c - 1) * κ * (∫ t, A (r / 3) s t ∂.haar) * eulerProd (heckeCoeff ψ T) s := by
    obtain ⟨h_int_one, h_val_one⟩ := h_one h_third hs
    obtain ⟨h_int_c, h_val_c⟩ := h_unfold h_third hc_mod hs
    have h_eq : D s = fun a ↦ X c * (X a * Θ (r / 3) a * (ideleModule a ^ s : ℝ)) -
        X c * X a * Θ (r / 3) (c * a) * (ideleModule a ^ s : ℝ) :=
      funext fun a ↦ by ring
    rw [h_eq, integral_sub (h_int_one.const_mul _) h_int_c, integral_const_mul, h_val_one, h_val_c]
    exact ⟨(h_int_one.const_mul _).sub h_int_c, by ring⟩
  -- Thanks to the gain `ideleModule a ^ δ` in `h_diff`, the integral of `D σ` converges for some
  -- `σ < 1`.
  obtain ⟨σ, hσ, hσ_one⟩ : ∃ σ : ℝ, 1 - δ < σ ∧ σ < 1 := exists_between (sub_lt_self 1 hδ)
  have hD_fin : HasFiniteIntegral (D σ) μ := by
    have hs : 1 < σ + δ := by linarith
    refine hasFiniteIntegral_mul_sub_mul_rpow_of_abs_sub_le (u := fun a ↦ X c * X a)
      ideleModule_pos ?_ (h_unfold le_rfl hc_mod hs).1 h_diff
    simpa only [mul_assoc] using (h_one le_rfl hs).1.const_mul (X c)
  -- A Mellin integral that converges at two points is analytic between them.
  have hD_an : AnalyticAt ℝ (fun s ↦ ∫ a, D s a ∂μ) 1 := by
    obtain ⟨-, -, h_an⟩ :=
      analyticOnNhd_integral_mul_rpow ideleModule_pos (by fun_prop) hD_fin (hD one_lt_two).1
    exact h_an 1 ⟨hσ_one, one_lt_two⟩
  have hA_an : AnalyticAt ℝ (fun s ↦ ∫ t, A (r / 3) s t ∂.haar) 1 := by
    obtain ⟨-, -, h_an⟩ := analyticOnNhd_integral_mul_rpow (fun t ↦ ideleModule_pos (t, 1))
      (by fun_prop) (hA_int 0).hasFiniteIntegral (hA_int 2)
    exact h_an 1 ⟨one_pos, one_lt_two⟩
  -- Take for `F` the integral of `D` and for `G` the factor of the Euler product in `hD`.
  refine ⟨T, fun s ↦ ∫ a, D s a ∂μ, fun s ↦ (X c - 1) * κ * ∫ t, A (r / 3) s t ∂.haar, hD_an,
    analyticAt_const.fun_mul hA_an, ?_, fun s hs ↦ (hD hs).2⟩
  have h_const_ne : (X c - 1) * κ ≠ 0 := mul_ne_zero (sub_ne_zero.mpr hc) hκ
  exact mul_ne_zero h_const_ne (hA_ne (by positivity))

/-- Hecke's theorem at `s = 1`: let `ψ ≠ 1` be the finite part of a Hecke character of type `n`
(`IsHeckeOfType ψ n`) and `S` a finite set of finite places. Some function `F` of a real variable,
analytic at `1`, agrees with the partial `L`-function `eulerProd (heckeCoeff ψ S)` at all real
`s > 1` near `1`. -/
lemma exists_analyticAt_one_eulerProd (h : IsHeckeOfType ψ n) (hS : S.Finite) (hψ_ne : ψ ≠ 1) :
    ∃ F : ℝ → ℂ, AnalyticAt ℝ F 1 ∧
      ∀ᶠ s : ℝ in nhds 1, 1 < s → F s = eulerProd (heckeCoeff ψ S) s := by
  obtain ⟨S, rfl⟩ := hS.exists_finset_coe
  obtain ⟨T, F, G, hF, hG, hG_ne, h_eq⟩ := h.exists_analyticAt_one_mul_eulerProd hψ_ne
  -- Exchange the Euler factors at `T` for those at `S` and divide. With `P Q s` the product of
  -- `1 - ψ(ϖ_w) q_w ^ (-s)` over `w ∈ Q` (analytic and nonzero at `1` by `eulerProd_erase`), the
  -- function is `F s * P S s / (G s * P T s)`.
  let P (Q : Finset (FinPlace K)) (s : ℂ) : ℂ :=
    ∏ w ∈ Q, (1 - ψ (locIdele w (uniformizer w)) * w.q ^ (-s))
  choose hP_an hP_ne hP using
    eulerProd_erase fun w ↦ (h.norm_eq_one (locIdele w (uniformizer w))).le
  have h_den_an : AnalyticAt ℝ (fun s : ℝ ↦ G s * P T s) 1 := hG.fun_mul (hP_an T)
  have h_den_ne : G 1 * P T (1 : ℝ) ≠ 0 := mul_ne_zero hG_ne (hP_ne T)
  refine ⟨fun s ↦ F s * P S s / (G s * P T s),
    (hF.fun_mul (hP_an S)).fun_div h_den_an h_den_ne, ?_⟩
  filter_upwards [h_den_an.continuousAt.eventually_ne h_den_ne] with s h_den hs
  refine div_eq_of_eq_mul h_den ?_
  rw [h_eq s hs, heckeCoeff, heckeCoeff, hP T s hs, hP S s hs]
  ring

/-- Let `ψ ≠ 1` be the finite part of a Hecke character of type `n` (`IsHeckeOfType ψ n`: `ψ` has
open kernel and `ψ x * ∏ w, (Φ w x / ‖Φ w x‖) ^ n w = 1` for `x ∈ Kˣ`), and let `S` be a finite set
of finite places. The partial `L`-function `eulerProd (heckeCoeff ψ S)` is the Euler product
`∏ (1 - ψ(ϖ_v) * q_v ^ (-s))⁻¹` over `v ∉ S`, with `ϖ_v = uniformizer v`; its value at each `s ≥ 1`
is the limit of the product as `s' → s` with `s' > 1`. This function is continuous on `s ≥ 1`. -/
lemma continuousOn_eulerProd (h : IsHeckeOfType ψ n) (hS : S.Finite) (hψ_ne : ψ ≠ 1) :
    ContinuousOn (eulerProd (heckeCoeff ψ S)) (Set.Ici 1) := by
  -- `eulerProd` is the extension by continuity of `E`, which has a limit at every `s ≥ 1`: at
  -- `s = 1` because it agrees, to the right of `1`, with a function `F` analytic at `1`.
  obtain ⟨F, hF, hF_eq⟩ := h.exists_analyticAt_one_eulerProd hS hψ_ne
  let E (s : ℝ) : ℂ := exp (-∑' v : FinPlace K, log (1 + -(heckeCoeff ψ S v * v.q ^ (-s : ℂ))))
  have hE_eq {s : ℝ} (hs : 1 < s) : eulerProd (heckeCoeff ψ S) s = E s :=
    (eulerProd_eq_exp h.norm_heckeCoeff_le hs).1
  have hE_cont {s : ℝ} (hs : 1 < s) : ContinuousAt E s := by
    obtain ⟨-, -, h_log⟩ := eulerProd_eq_exp (h.norm_heckeCoeff_le (S := S)) hs
    exact h_log.cexp
  have hE_lim : Filter.Tendsto E (nhdsWithin 1 (Set.Ioi 1)) (nhds (F 1)) := by
    refine hF.continuousAt.continuousWithinAt.congr' (eventually_nhdsWithin_iff.mpr ?_)
    filter_upwards [hF_eq] with s h_eq hs
    rw [h_eq hs, hE_eq hs]
  refine continuousOn_extendFrom (by simp) fun s hs ↦ ?_
  obtain rfl | hs := (Set.mem_Ici.mp hs).eq_or_lt
  · exact ⟨F 1, hE_lim⟩
  · exact ⟨E s, (hE_cont hs).continuousWithinAt⟩

/-- Let `ψ ≠ 1` be the finite part of a Hecke character of type `n` (`IsHeckeOfType ψ n`), and let
`S` be a finite set of finite places. For some natural number `m`, the coefficients `heckeCoeff ψ S`
(the values of `ψ` at uniformisers) have mean `-m` over the primes of degree one outside `S`
(`HasPrimeDensity`: for `s → 1⁺`, `∑ heckeCoeff ψ S v * q ^ (-s) = -m * log (1 / (s - 1)) + O(1)`).
If `m = 0`, the partial `L`-function `eulerProd (heckeCoeff ψ S)` has no zero on real `s ≥ 1`, where
its value at `s = 1` is the limit of the Euler product as `s → 1⁺`. In the proof, `m` is the order
of vanishing at `1` of a function analytic at `1` that agrees with the `L`-function for `s > 1` near
`1`. -/
lemma exists_hasPrimeDensity_neg_natCast (h : IsHeckeOfType ψ n) (hS : S.Finite) (hψ_ne : ψ ≠ 1) :
    ∃ m : ℕ, (m = 0 → ∀ s : ℝ, 1 ≤ s → eulerProd (heckeCoeff ψ S) s ≠ 0) ∧
      HasPrimeDensity (heckeCoeff ψ S) (-m) := by
  -- By Hecke's theorem the `L`-function agrees, to the right of `1`, with a function `F` analytic
  -- at `1`. Write `F s = (s - 1) ^ m * f s` with `f 1 ≠ 0`.
  obtain ⟨F, hF, hF_eq⟩ := h.exists_analyticAt_one_eulerProd hS hψ_ne
  -- For `s > 1` the Euler product is an exponential, so `F` does not vanish identically near `1`.
  have h_ne_zero {s : ℝ} (hs : 1 < s) : eulerProd (heckeCoeff ψ S) s ≠ 0 := by
    rw [(eulerProd_eq_exp h.norm_heckeCoeff_le hs).1]
    exact exp_ne_zero _
  have hF_ne : ¬∀ᶠ s in nhds 1, F s = 0 := by
    intro h_zero
    obtain ⟨s, hs, h_eq, hs_zero⟩ :=
      ((frequently_gt_nhds (1 : ℝ)).and_eventually (hF_eq.and h_zero)).exists
    exact h_ne_zero hs ((h_eq hs).symm.trans hs_zero)
  obtain ⟨m, f, hf, hf_ne, hF_fac⟩ : ∃ (m : ℕ) (f : ℝ → ℂ), AnalyticAt ℝ f 1 ∧ f 1 ≠ 0 ∧
      ∀ᶠ s : ℝ in nhds 1, F s = (s - 1) ^ m • f s :=
    hF.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hF_ne
  -- The mean is `-m` once `(s - 1) ^ (-m)` times the `L`-function has a nonzero limit at `1⁺`.
  refine ⟨m, ?_, hasPrimeDensity_of_tendsto h.norm_heckeCoeff_le hf_ne ?_⟩
  · rintro rfl s hs
    obtain rfl | hs := hs.eq_or_lt
    · -- The `L`-function and `F` are continuous at `1` from the right, so agree at `1`.
      have h_one : F 1 = eulerProd (heckeCoeff ψ S) 1 :=
        tendsto_nhds_unique_of_eventuallyEq hF.continuousAt.continuousWithinAt
          ((h.continuousOn_eulerProd hS hψ_ne 1 Set.self_mem_Ici).mono Set.Ioi_subset_Ici_self)
          (eventually_nhdsWithin_iff.mpr hF_eq)
      have hF_one : F 1 = f 1 := by simpa using hF_fac.self_of_nhds
      rwa [← h_one, hF_one]
    · exact h_ne_zero hs
  · -- Just to the right of `1` that product is `f`.
    refine hf.continuousAt.continuousWithinAt.congr' (eventually_nhdsWithin_iff.mpr ?_)
    filter_upwards [hF_eq, hF_fac] with s h_eq h_fac hs
    have hs_ne : (s : ℂ) - 1 ≠ 0 := mod_cast sub_ne_zero.mpr (Set.mem_Ioi.mp hs).ne'
    rw [← h_eq hs, h_fac]
    simp [cpow_neg, hs_ne]

/-- Let `ψ ≠ 1` be the finite part of a Hecke character of type `n` (`IsHeckeOfType ψ n`) and `S` a
finite set of finite places. The partial `L`-function `eulerProd (heckeCoeff ψ S)` is continuous on
`s ≥ 1`, and for some natural number `m` the values of `ψ` at the primes of degree one outside `S`
have mean `-m` (`HasPrimeDensity`), with no zero of the `L`-function on `s ≥ 1` if `m = 0`. -/
lemma exists_hasPrimeDensity (h : IsHeckeOfType ψ n) (hS : S.Finite) (hψ_ne : ψ ≠ 1) :
    ContinuousOn (eulerProd (heckeCoeff ψ S)) (Set.Ici 1) ∧
      ∃ m : ℕ, (m = 0 → ∀ s : ℝ, 1 ≤ s → eulerProd (heckeCoeff ψ S) s ≠ 0) ∧
        HasPrimeDensity (heckeCoeff ψ S) (-m) :=
  ⟨h.continuousOn_eulerProd hS hψ_ne, h.exists_hasPrimeDensity_neg_natCast hS hψ_ne⟩

/-- Let `ψ` be the finite part of a Hecke character of type `n` (`IsHeckeOfType ψ n`) with
`ψ ^ 2 ≠ 1`, and let `S` be a finite set of finite places. The partial `L`-function
`eulerProd (heckeCoeff ψ S)` has no zero at real `s ≥ 1`, where its value at `s = 1` is the limit of
the Euler product as `s → 1⁺`.

A special case of the non-vanishing of Hecke L-functions. Only real s is covered, and ψ² ≠ 1 is
assumed even for s > 1. -/
lemma eulerProd_ne_zero (h : IsHeckeOfType ψ n) (hS : S.Finite) (hψ_sq : ψ ^ 2 ≠ 1) {s : ℝ}
    (hs : 1 ≤ s) : eulerProd (heckeCoeff ψ S) s ≠ 0 := by
  -- Let `-m₁` and `-m₂` be the means of `ψ` and `ψ ^ 2` over the primes of degree one. The
  -- inequality `3 + 4 cos θ + cos 2θ ≥ 0` gives `4 * m₁ + m₂ ≤ 3`, so `m₁ = 0`.
  have hψ_ne : ψ ≠ 1 := fun h_one ↦ hψ_sq (by rw [h_one, one_pow])
  obtain ⟨m₁, h_nonvanishing, h_dens₁⟩ := h.exists_hasPrimeDensity_neg_natCast hS hψ_ne
  obtain ⟨m₂, -, h_dens₂⟩ := (h.pow 2).exists_hasPrimeDensity_neg_natCast hS hψ_sq
  -- The two densities, as a family indexed by `Fin 2` for `HasPrimeDensity.sum`.
  let a : Fin 2 → FinPlace K → ℂ := ![heckeCoeff ψ S, heckeCoeff (ψ ^ 2) S]
  have h_dens : ∀ i : Fin 2, HasPrimeDensity (a i) (![-(m₁ : ℂ), -(m₂ : ℂ)] i) := by
    simpa [a, Fin.forall_fin_two] using ⟨h_dens₁, h_dens₂⟩
  have h_re_sum_ge (v : FinPlace K) (hv : v ∉ S) :
      (-3 : ℂ).re ≤ (∑ i : Fin 2, ![4, 1] i * a i v).re := by
    -- With `z = x + i y` of norm one, `3 + 4 x + (x ^ 2 - y ^ 2) = 2 * (x + 1) ^ 2`.
    let z : ℂ := ψ (locIdele v (uniformizer v))
    have h_unit : 1 ^ 2 - z.re ^ 2 = z.im ^ 2 := by rw [← sq_norm_sub_sq_re, h.norm_eq_one]
    have h_sum_re : (∑ i : Fin 2, ![4, 1] i * a i v).re = 4 * z.re + (z.re ^ 2 - z.im ^ 2) := by
      simp [a, sq, heckeCoeff, hv, z]
    rw [h_sum_re, show (-3 : ℂ).re = -3 by norm_num]
    nlinarith [sq_nonneg (z.re + 1)]
  -- An inequality at almost all primes passes to the means.
  have h_mean_re : (-3 : ℂ).re ≤ (∑ i : Fin 2, ![4, 1] i * ![-(m₁ : ℂ), -(m₂ : ℂ)] i).re :=
    (hasPrimeDensity_const (-3)).re_le_re (.sum ![4, 1] h_dens)
      (.mono hS.compl_mem_cofinite fun v hv _ ↦ h_re_sum_ge v hv)
  have h_mean : (m₂ + 4 * m₁ : ℝ) ≤ 3 := by simpa using h_mean_re
  norm_cast at h_mean
  exact h_nonvanishing (by lia) s hs

end IsHeckeOfType

end New

end HeckeContinuation

end
