import New.Spanning.MainTerm.Frequencies
import New.Spanning.RemainingTerms.Box
import New.Spanning.Unfolding.BesselLevelStructure

/-!
# One-sided Poisson summation, sums over frequencies, and the sieve over all places

The sieve over the infinite places of the CM field `E` and a finite set `T` of finite places, which
bounds the main term.

* `New.Filling.charOnPlaces`, `New.Filling.globalChar`: the character of the product of the
  completions at `T`, and its product with the characters at the infinite places.
* `New.Filling.sum_ratPoint_le_mul_add_integral_of_fourier_le`: one-sided Poisson summation over the
  infinite places and `T`, at rational points integral off `T`.
* `New.Filling.entryDensity`, `New.Filling.densitySum`: the sum of densities at a common next entry,
  and the sums of densities in which the first `i` entries are summed over `A`.
* `New.Filling.densitySum_succ_le_mul_densitySum_add`: each sum of densities is bounded by the one
  before plus an error, up to the constant of Poisson summation (`New.Filling.poissonConst`).
* `New.Filling.densitySum_le`: the bound after all entries are removed in turn.
* `New.Filling.sieve`: the sieve for the product of one system for each infinite place and one
  system at `T`, read at rational points (`New.Filling.ratPoint`).

Conventions: `𝔰.k` and `𝔰.n = 𝔰.ϱ + 1` are parameters of the shape `𝔰`; in
`New.Filling.frequency_term_le` and `New.Filling.sum_frequencies_le`, `k` is any natural number.
`Φ v` is the chosen embedding of `E` at the infinite place `v`.

Notions from other files:
* `New.Filling`: the data `S`, among them the size parameter `b = S.b`, the level `M = S.M`, the
  prime `N = S.N` and a generator `ϖ = S.deltaE` of the different of `E`.
* `New.Filling.IsAdmissible`: the standing hypotheses on `S`, among them `1 ≤ |S.realM v| ≤ b ^ 23`
  and `N ≤ b ^ (60 n)`.
* `New.ψf E`, written `ψ_f`: the character of the finite adeles with `ψ_f(x) = exp (2πi Tr a)` for
  any `a ∈ E` with `x - a` integral. `New.stdAddChar E` is the standard character of the adeles, and
  `New.Filling.selfDualChar` is `x ↦ ψ_f(-x / ϖ)`.
* `New.LocProd T`: the product of the completions at `T`, with integers `New.SemilocalField.O`;
  `New.evalPlaces T` and `New.ratToPlaces T` map the finite adeles and `E` to it.
* `New.integralOff T`, `New.Filling.ratIntegralOff T`: the finite adeles and the elements of `E`
  (the `T`-integers) that are integral at every finite place outside `T`.
* `New.genIndex a`, `New.denomIndex O a`: the generalised index `[O : a O]` and the denominator
  `[O : O ∩ a⁻¹ O]`.
* `New.SieveSystem`: the axioms of the sieve for a family of forms `J i` on pairs of heads, at a
  place or a product of places.

## Relation to the literature

A system of positive kernels, of one kind at archimedean and finite places, has each kernel the
integral of the next over a common last entry. Systems multiply over places, and one-sided Poisson
summation, entry by entry, bounds the sum over rational points by the mass times a factor near 1, up
to the constants of summation and a small error, as the main term of the second moment requires.
Inductive Fourier transforms of Kloosterman integrals and spectral large sieves losing a constant or
X^ε are known in the literature. Related work: Jacquet, Smooth transfer of Kloosterman integrals,
2003; Jacquet, Kloosterman identities over a quadratic extension, 2004; Blomer–Buttcane, Global
decomposition of GL(3) Kloosterman sums and the spectral large sieve, 2015; Deshouillers–Iwaniec,
Kloosterman sums and Fourier coefficients of cusp forms, 1982.
-/

namespace New.Filling

open NumberField ENNReal Finset Fintype MeasureTheory Measure Real AddSubgroup Matrix ComplexOrder
  SemilocalField Complex

/-- The character `S.selfDualChar` is `x ↦ ψ_f(-x / ϖ)`, where `ψ_f = ψf E` is the standard
character of the finite adeles and `ϖ = S.deltaE` generates the different of `E`. -/
lemma selfDualChar_apply {E : Type} [Field E] [CMType E] {𝔰 : Shape} (S : Filling E 𝔰)
    (x : 𝔸f E) : S.selfDualChar x = ψf E (algebraMap E (𝔸f E) (-(S.deltaE : E)⁻¹) * x) := rfl

variable {E : Type} [Field E] [CMType E] [WeilData E] {𝔰 : Shape} (S : Filling E 𝔰)
  (T : Finset (FinPlace E)) [T.StarStable]

/-- The character `S.selfDualChar` of the finite adeles, `x ↦ ψ_f(-x / ϖ)`, read on the product of
the completions at `T` through extension by zero (`adeleOfLocal`). Here `ψ_f = ψf E` is the standard
character of the finite adeles, and `ϖ = S.deltaE` generates the different of `E`. -/
noncomputable def charOnPlaces : AddChar (LocProd T) ℂ :=
  S.selfDualChar.compAddMonoidHom (adeleOfLocal T)

section

omit [WeilData E] [T.StarStable]

/-- At a finite adele that is integral off `T`, the character `S.selfDualChar` depends only on the
components at `T`: it equals `S.charOnPlaces T` there. -/
lemma charOnPlaces_evalPlaces {x : 𝔸f E} (hx : x ∈ integralOff T) :
    S.charOnPlaces T (evalPlaces T x) = S.selfDualChar x := by
  refine (eq_of_div_eq_one ?_).symm
  rw [charOnPlaces, AddChar.compAddMonoidHom_apply, ← S.selfDualChar.map_sub_eq_div]
  exact S.selfDualChar_eq_one_of_mem _ ((sub_adeleOfLocal_mem_iff T).2 hx)

lemma continuous_charOnPlaces : Continuous (S.charOnPlaces T) :=
  continuous_ψf.subtype_val.comp ((continuous_adeleOfLocal T).const_mul _)

/-- The character of the product of the infinite places and the completions at `T`: the product of
the characters `wave c = exp (c - conj c)` at the infinite places and of `S.charOnPlaces T`. -/
noncomputable def globalChar (x : (InfinitePlace E → ℂ) × LocProd T) : ℂ :=
  (∏ v : InfinitePlace E, wave (x.1 v)) * S.charOnPlaces T x.2

lemma continuous_globalChar : Continuous (S.globalChar T) :=
  .mul (by fun_prop [wave]) ((S.continuous_charOnPlaces T).comp continuous_snd)

/-- The decay factor at the places of `T` for a transform at the frequency `ξ`: the number
`[O : ξ O] ^ ((k - n⁷) / 2) / [O : O ∩ ξ⁻¹ O] ^ 3 * b ^ (n⁹ f)`, with `f` the number of infinite
places of `E`. -/
noncomputable def frequencyDecay (ξ : LocProd T) : ℝ :=
  √(genIndex ξ) ^ (𝔰.k - 𝔰.n ^ 7) / denomIndex O ξ ^ 3 * S.b ^ (𝔰.n ^ 9 * numInfPlaces E)

/-- The number `t`, read at the infinite places with the scales `l v` and at `T`: the point with
components `l v * Φ v t` and the image of `t` in the product of the completions at `T`. -/
noncomputable def ratPoint (l : InfinitePlace E → ℂ) (t : E) : (InfinitePlace E → ℂ) × LocProd T :=
  (fun v : InfinitePlace E ↦ l v * Φ v t, ratToPlaces T t)

/-- For `y` integral off `T`, the norm of the denominator ideal `{a ∈ 𝓞 E | a y ∈ 𝓞 E}` is at most
the index `[O : O ∩ y⁻¹ O]`, where `O` is the ring of integers of the completions at `T`. -/
lemma absNorm_denominator_le {y : E} (hy : y ∈ ratIntegralOff T) :
    Ideal.absNorm (denominator y) ≤ denomIndex O (ratToPlaces T y) := by
  -- The denominator of `y` is the preimage of the local one under `𝓞 E → O`.
  let f : 𝓞 E →+ LocProd T := ((ratToPlaces T).comp (algebraMap (𝓞 E) E)).toAddMonoidHom
  let D : AddSubgroup (LocProd T) := O.toAddSubgroup.comap (.mulLeft (ratToPlaces T y))
  have h_integral (a : 𝓞 E) : algebraMap E (𝔸f E) (algebraMap (𝓞 E) E a) ∈ Ô E :=
    algebraMap_mem_Ô.2 a.isIntegral_coe
  have h_comap : (denominator y).toAddSubgroup = D.comap f := by
    ext a
    have h_off : algebraMap E (𝔸f E) (algebraMap (𝓞 E) E a * y) ∈ integralOff T := by
      rw [map_mul]
      exact mul_mem ((mem_Ô_iff T).1 (h_integral a)).right hy
    rw [Submodule.mem_toAddSubgroup, mem_denominator, ← algebraMap_mem_Ô, mem_Ô_iff T,
      and_iff_left h_off]
    simp [D, f, mul_comm]
  have h_range : f.range ≤ O.toAddSubgroup := by
    rintro _ ⟨a, rfl⟩
    exact ((mem_Ô_iff T).1 (h_integral a)).left
  calc
    _ = (denominator y).toAddSubgroup.index := rfl
    _ = D.relIndex f.range := by rw [h_comap, index_comap]
    _ ≤ _ := relIndex_le_of_le_right h_range (denomIndex_ne_zero T _)

/-- Let `y ≠ 0` be integral off `T`, and let `‖c v‖⁻¹ ≤ |x v| ≤ B` with `1 ≤ B`. Take the product of
the decay factors of `y` at the infinite places (`dampedPower k r = r ^ k * min 1 r ^ 6` at
`r = ‖c v * Φ v y‖⁻¹`, `Φ v` the embedding at `v`) and at `T`. It is at most
`∏ v, |x v| ^ k * B ^ 6` times the inverse cube of the height of `y`, whose finite part is the norm
of the denominator ideal. -/
lemma frequency_term_le {B : ℝ} (k : ℕ) {c : InfinitePlace E → ℂ} {x : InfinitePlace E → ℝ}
    (hB : 1 ≤ B) (h_lower : ∀ v : InfinitePlace E, ‖c v‖⁻¹ ≤ |x v|)
    (h_upper : ∀ v : InfinitePlace E, |x v| ≤ B) {y : E} (hy₀ : y ≠ 0)
    (hyT : y ∈ ratIntegralOff T) :
    (∏ v : InfinitePlace E, dampedPower k ‖c v * Φ v y‖⁻¹) *
        (√(genIndex (ratToPlaces T y)) ^ k / denomIndex O (ratToPlaces T y) ^ 3) ≤
      (∏ v : InfinitePlace E, |x v| ^ k * B ^ 6) *
        ((∏ v : InfinitePlace E, (max 1 ‖Φ v y‖)⁻¹ ^ 6) *
          (Ideal.absNorm (denominator y) : ℝ)⁻¹ ^ 3) := by
  have h_inf (v : InfinitePlace E) : dampedPower k ‖c v * Φ v y‖⁻¹ * ‖Φ v y‖ ^ k ≤
      |x v| ^ k * B ^ 6 * (max 1 ‖Φ v y‖)⁻¹ ^ 6 := by
    have h_min : min 1 (‖c v‖⁻¹ * ‖Φ v y‖⁻¹) ≤ B * (max 1 ‖Φ v y‖)⁻¹ := by
      rcases le_total 1 ‖Φ v y‖ with h_ge | h_le
      · grw [min_le_right, h_lower v, h_upper v, max_eq_right h_ge]
      · grw [min_le_left, max_eq_left h_le, inv_one, mul_one, hB]
    have h_cancel : (‖c v‖⁻¹ * ‖Φ v y‖⁻¹) ^ k * ‖Φ v y‖ ^ k = ‖c v‖⁻¹ ^ k := by
      rw [← mul_pow, inv_mul_cancel_right₀ (by simpa using hy₀)]
    rw [dampedPower, norm_mul, mul_inv, mul_right_comm, h_cancel, mul_assoc, ← mul_pow]
    gcongr
    exact h_lower v
  set d : ℝ := (Ideal.absNorm (denominator y) : ℝ)
  have h_one_le : 1 ≤ d := by
    simpa [d, Nat.one_le_iff_ne_zero, Ideal.absNorm_eq_zero_iff] using denominator_ne_bot y
  have h_finite : ((denomIndex O (ratToPlaces T y) : ℝ) ^ 3)⁻¹ ≤ d⁻¹ ^ 3 := by
    grw [← absNorm_denominator_le T hyT, inv_pow]
  unfold dampedPower at h_inf ⊢
  calc
    _ ≤ (∏ v, ‖c v * Φ v y‖⁻¹ ^ k * min 1 ‖c v * Φ v y‖⁻¹ ^ 6) *
        ((∏ v, ‖Φ v y‖) ^ k * d⁻¹ ^ 3) := by
      grw [div_eq_mul_inv, h_finite, sqrt_genIndex_le_prod_norm T hy₀ hyT]
    _ = (∏ v, ‖c v * Φ v y‖⁻¹ ^ k * min 1 ‖c v * Φ v y‖⁻¹ ^ 6 * ‖Φ v y‖ ^ k) * d⁻¹ ^ 3 := by
      rw [← mul_assoc, ← prod_pow, ← prod_mul_distrib]
    _ ≤ _ := by grw [h_inf, prod_mul_distrib, mul_assoc]

/-- Let `X` be a finite set of nonzero elements of `E` that are integral off `T`, and let
`‖c v‖⁻¹ ≤ |x v| ≤ B` with `1 ≤ B`. The sum over `y ∈ X` of the product of the decay factors at the
infinite places and at `T` is at most `∏ v, (|x v| ^ k * (b B²)³)`. -/
theorem sum_frequencies_le (B : ℝ) (k : ℕ) (X : Finset E) (c : InfinitePlace E → ℂ)
    (x : InfinitePlace E → ℝ) (hB : 1 ≤ B) (h_lower : ∀ v : InfinitePlace E, ‖c v‖⁻¹ ≤ |x v|)
    (h_upper : ∀ v : InfinitePlace E, |x v| ≤ B) (hX₀ : ∀ y ∈ X, y ≠ 0)
    (hXT : ∀ y ∈ X, y ∈ ratIntegralOff T) :
    ∑ y ∈ X, (∏ v : InfinitePlace E, dampedPower k ‖c v * Φ v y‖⁻¹) *
        (√(genIndex (ratToPlaces T y)) ^ k / denomIndex O (ratToPlaces T y) ^ 3) ≤
      ∏ v : InfinitePlace E, |x v| ^ k * (S.b * B ^ 2) ^ 3 := by
  -- The inverse cubes of the heights have sum at most `64 * 38 * exp 4` per infinite place.
  have h_const : 64 * 38 * Real.exp 4 ≤ S.b ^ 3 := by
    have h_exp : Real.exp 4 = Real.exp 1 ^ 4 := by simp [← Real.exp_nat_mul]
    grw [h_exp, Real.exp_one_lt_three.le, ← S.thousand_le_b]
    norm_num
  calc
    _ ≤ ∑ y ∈ X, (∏ v, |x v| ^ k * B ^ 6) *
        ((∏ v, (max 1 ‖Φ v y‖)⁻¹ ^ 6) * (Ideal.absNorm (denominator y) : ℝ)⁻¹ ^ 3) :=
      sum_le_sum fun y hy ↦ frequency_term_le T k hB h_lower h_upper (hX₀ y hy) (hXT y hy)
    _ ≤ (∏ v, |x v| ^ k * B ^ 6) * (64 * 38 * Real.exp 4) ^ numInfPlaces E := by
      grw [← mul_sum, sum_height_inv_cube_le]
    _ ≤ ∏ v, |x v| ^ k * B ^ 6 * S.b ^ 3 := by
      grw [h_const, prod_mul_distrib (g := fun _ ↦ S.b ^ 3), prod_const, card_univ]
    _ = _ := prod_congr rfl fun v _ ↦ by ring

/-- Scaling by `r > 0` at the infinite places and projecting to `T` maps the measure on the adeles
that are integral off `T` to `volÔ E / ∏ v, r v ^ 2` times the product measure, where `volÔ E` is
the volume of the integral finite adeles. -/
lemma measurePreserving_scale_evalPlaces {r : InfinitePlace E → ℝ}
    (hr : ∀ v : InfinitePlace E, 0 < r v) :
    MeasurePreserving (fun z : 𝔸 E ↦ (fun v : InfinitePlace E ↦ r v * z.1 v, evalPlaces T z.2))
      (volume.restrict (Set.univ ×ˢ (integralOff T : Set (𝔸f E))))
      (ENNReal.ofReal (volÔ E / ∏ v : InfinitePlace E, r v ^ 2) • volume) := by
  -- Scaling by `r` has determinant `∏ v, r v ^ 2`.
  let L : (InfinitePlace E → ℂ) →ₗ[ℝ] InfinitePlace E → ℂ :=
    .pi fun v ↦ (r v • (1 : ℂ →ₗ[ℝ] ℂ)).comp (.proj v)
  have h_det : LinearMap.det L = ∏ v, r v ^ 2 := by simp [L, LinearMap.det_pi]
  have h_pos : 0 < ∏ v, r v ^ 2 := prod_pos fun v _ ↦ pow_pos (hr v) 2
  have h_inf : MeasurePreserving L volume (ENNReal.ofReal (∏ v, r v ^ 2)⁻¹ • volume) :=
    ⟨by fun_prop, by rw [map_linearMap_addHaar_eq_smul_addHaar _ (h_det.trans_ne h_pos.ne'), h_det,
      abs_of_pos (inv_pos.2 h_pos)]⟩
  have h_fin : MeasurePreserving (evalPlaces T) (volume.restrict (integralOff T))
      (volÔ E • volume) := ⟨by fun_prop, map_evalPlaces_restrict_volume T⟩
  have h_map : (fun z : 𝔸 E ↦ (fun v ↦ r v * z.1 v, evalPlaces T z.2)) =
      Prod.map L (evalPlaces T) := by ext <;> simp [L]
  rw [h_map]
  simpa [volume_eq_prod, ← prod_restrict, prod_smul_left, prod_smul_right, div_eq_mul_inv,
    mul_smul] using h_inf.prod h_fin

end

/-- The standard character of the adeles at `x` is `exp (-2πi ∑ v, 2 Re x_v)`, with `x_v = x.1 v`
the components at the infinite places, times the standard character `ψf E` of the finite adeles at
the finite part `x.2`. -/
lemma coe_stdAddChar_apply {E : Type*} [Field E] [NumberField E] (x : 𝔸 E) :
    (New.stdAddChar E x : ℂ) = fourierChar (-∑ v : InfinitePlace E, 2 * (x.1 v).re) * ψf E x.2 :=
  Circle.coe_mul _ _

/-- The character `wave c = exp (c - conj c)` at `c = 2πi w` is `exp (2πi * 2 Re w)`. -/
lemma wave_two_pi_I_mul (w : ℂ) : wave (2 * π * .I * w) = fourierChar (2 * w.re) := by
  have h_im : (2 * π * .I * w : ℂ).im = 2 * π * w.re := by simp
  rw [wave, sub_conj, h_im, fourierChar_apply, mul_left_comm (2 * π)]

omit [WeilData E] [T.StarStable] in
/-- Let `ϖ = S.deltaE` be the generator of the different of `E` in the filling data `S`. For `y ∈ E`
and an adele `z`, both integral off `T`, the standard adelic character at `-y z / ϖ` is the product
of the characters `wave c = exp (c - conj c)` at the infinite places and of `S.charOnPlaces T`, the
character `x ↦ ψ_f(-x / ϖ)` on the product of the completions at `T`. -/
lemma stdAddChar_div_deltaE {y : E} (hy : y ∈ ratIntegralOff T) {z : 𝔸 E}
    (hz : z.2 ∈ integralOff T) :
    (New.stdAddChar E (toAdele (y / S.deltaE) * -z) : ℂ) =
      (∏ v : InfinitePlace E, wave (2 * π * .I / Φ v S.deltaE * Φ v y * z.1 v)) *
        S.charOnPlaces T (ratToPlaces T y * evalPlaces T z.2) := by
  let w (v : InfinitePlace E) : ℂ := Φ v y / Φ v S.deltaE * z.1 v
  have h_inf : (fourierChar (-∑ v, 2 * ((toAdele (y / S.deltaE) * -z).1 v).re) : ℂ) =
      ∏ v : InfinitePlace E, wave (2 * π * .I / Φ v S.deltaE * Φ v y * z.1 v) := by
    have h_arg (v : InfinitePlace E) : (toAdele (y / S.deltaE) * -z).1 v = -w v := by simp [w]
    have h_wave (v : InfinitePlace E) :
        2 * π * .I / Φ v S.deltaE * Φ v y * z.1 v = 2 * π * .I * w v := by ring
    calc
      _ = (fourierChar (∑ v, 2 * (w v).re) : ℂ) := by
        simp_rw [h_arg, neg_re, mul_neg, sum_neg_distrib, neg_neg]
      _ = ∏ v, (fourierChar (2 * (w v).re) : ℂ) := by
        simp only [fourierChar_apply, mul_sum, ofReal_sum, sum_mul, Complex.exp_sum]
      _ = _ := by simp only [h_wave, wave_two_pi_I_mul]
  have h_fin : (ψf E (toAdele (y / S.deltaE) * -z).2 : ℂ) =
      S.charOnPlaces T (evalPlaces T (algebraMap E (𝔸f E) y * z.2)) := by
    rw [S.charOnPlaces_evalPlaces T (mul_mem hy hz), selfDualChar_apply]
    simp [div_eq_mul_inv, mul_assoc, mul_left_comm]
  rw [coe_stdAddChar_apply, h_inf, h_fin, map_mul (evalPlaces T), ratToPlaces, RingHom.comp_apply]

omit [WeilData E] [T.StarStable] in
/-- Let `G` be a function on the adeles that is invariant under the integral finite adeles that
vanish at `T`, written `a - adeleOfLocal T (evalPlaces T a)` (`a ∈ Ô E` integral, with its
components at `T` removed). If the Fourier transform of `G` at `y / ϖ` is not zero, then `y` is
integral off `T`. -/
lemma mem_ratIntegralOff_of_transform_ne_zero {G : 𝔸 E → ℂ}
    (hG : ∀ a ∈ Ô E, ∀ z : 𝔸 E, G ((0, a - adeleOfLocal T (evalPlaces T a)) + z) = G z) {y : E}
    (hy : ∫ z : 𝔸 E, New.stdAddChar E (toAdele (y / S.deltaE) * -z) * G z ≠ 0) :
    y ∈ ratIntegralOff T := by
  -- Translation multiplies the transform by a value of the character, so these values are `1`;
  -- and `Ô E` is its own dual.
  rw [ratIntegralOff, Subring.mem_comap, ← sub_adeleOfLocal_mem_iff,
    ← S.forall_selfDualChar_mul_eq_one_iff]
  rintro ⟨a, ha⟩
  let a' : 𝔸 E := (0, a - adeleOfLocal T (evalPlaces T a))
  have h_shift : ∫ z, New.stdAddChar E (toAdele (y / S.deltaE) * -z) * G z =
      New.stdAddChar E (toAdele (y / S.deltaE) * -a') *
        ∫ z, New.stdAddChar E (toAdele (y / S.deltaE) * -z) * G z := by
    rw [← integral_const_mul, ← integral_add_left_eq_self _ a']
    congr with z
    rw [hG a ha, neg_add, mul_add, AddChar.map_add_eq_mul, Circle.coe_mul, mul_assoc]
  -- The factor is a value of the finite character: removing the components at `T` is
  -- multiplication by an idempotent, which can be moved from `a` to `y`.
  have h_arg :
      algebraMap E (𝔸f E) (-(S.deltaE : E)⁻¹) * (a * (y - adeleOfLocal T (evalPlaces T y))) =
        (toAdele (y / S.deltaE) * -a').2 := by
    simp only [a', adeleOfLocal_evalPlaces, Prod.snd_mul, Prod.snd_neg, toAdele_apply_snd,
      div_eq_mul_inv, map_mul, map_neg]
    ring
  rw [selfDualChar_apply, h_arg, ← (mul_eq_right₀ hy).1 h_shift.symm]
  simp [New.stdAddChar, a']

/-- The function on the adeles that reads `F` after scaling by `r` at the infinite places and
projecting to `T`, on the adeles that are integral off `T`, and is zero elsewhere. -/
noncomputable def extendToAdeles (r : InfinitePlace E → ℝ)
    (F : (InfinitePlace E → ℂ) × LocProd T → ℝ) : 𝔸 E → ℝ :=
  (Set.univ ×ˢ (integralOff T : Set (𝔸f E))).indicator fun z : 𝔸 E ↦
    F (fun v : InfinitePlace E ↦ r v * z.1 v, evalPlaces T z.2)

section ExtendToAdeles

variable {r : InfinitePlace E → ℝ} {F : (InfinitePlace E → ℂ) × LocProd T → ℝ}

section

omit [WeilData E] [T.StarStable]

lemma extendToAdeles_of_mem {z : 𝔸 E} (hz : z.2 ∈ integralOff T) :
    extendToAdeles T r F z = F (fun v : InfinitePlace E ↦ r v * z.1 v, evalPlaces T z.2) := by
  simp [extendToAdeles, hz]

lemma extendToAdeles_of_notMem {z : 𝔸 E} (hz : z.2 ∉ integralOff T) :
    extendToAdeles T r F z = 0 := by simp [extendToAdeles, hz]

/-- At the diagonal image `toAdele y` of a number `y` that is integral off `T`, the extension of `F`
is the value of `F` at the point with components `r v * Φ v y` and the image of `y` at `T`. -/
lemma extendToAdeles_toAdele {y : E} (hy : y ∈ ratIntegralOff T) :
    extendToAdeles T r F (toAdele y) = F (ratPoint T (fun v : InfinitePlace E ↦ (r v : ℂ)) y) :=
  extendToAdeles_of_mem T hy

/-- Let `F` be a real function on the product of the infinite places and the completions at `T`, and
let `r v` be real scales. The extension `extendToAdeles T r F` reads `F` after scaling by `r` at
infinity and projecting to `T`, and is zero at adeles that are not integral off `T`. It is invariant
under the integral finite adeles that vanish at `T`, written `a - adeleOfLocal T (evalPlaces T a)`
with `a ∈ Ô E` integral. -/
lemma extendToAdeles_sub_adeleOfLocal_add {a : 𝔸f E} (ha : a ∈ Ô E) (z : 𝔸 E) :
    extendToAdeles T r F ((0, a - adeleOfLocal T (evalPlaces T a)) + z) =
      extendToAdeles T r F z := by
  obtain ⟨-, ha_off⟩ := (mem_Ô_iff T).1 ha
  have h_int : a - adeleOfLocal T (evalPlaces T a) ∈ Ô E := (sub_adeleOfLocal_mem_iff T).2 ha_off
  have h_off : a - adeleOfLocal T (evalPlaces T a) ∈ integralOff T :=
    ((mem_Ô_iff T).1 h_int).right
  by_cases hz : z.2 ∈ integralOff T
  · rw [extendToAdeles_of_mem T hz, extendToAdeles_of_mem T (add_mem h_off hz)]
    simp
  · rw [extendToAdeles_of_notMem T hz,
      extendToAdeles_of_notMem T (mt (add_mem_cancel_left h_off).1 hz)]

/-- For positive scales `r`, the extension of an integrable function to the adeles is integrable. -/
lemma integrable_extendToAdeles (hr : ∀ v : InfinitePlace E, 0 < r v) (hF : Integrable F) :
    Integrable (extendToAdeles T r F) :=
  (integrable_indicator_iff (isOpen_univ.prod (isOpen_integralOff T)).measurableSet).2
    ((measurePreserving_scale_evalPlaces T hr).integrable_comp_of_integrable
      (hF.smul_measure ofReal_ne_top))

/-- Let `F` be a real function on the product of the infinite places and the completions at `T`, let
`r v` be real scales, and let `y ∈ E` be integral off `T`. Suppose `F` is lower semicontinuous at
the point (`ratPoint`) with components `r v * Φ v y` and the image of `y` at `T`. Then the extension
of `F` to the adeles is lower semicontinuous at the diagonal image `toAdele y`. -/
lemma lowerSemicontinuousAt_extendToAdeles {y : E} (hy : y ∈ ratIntegralOff T)
    (hF : LowerSemicontinuousAt F (ratPoint T (fun v : InfinitePlace E ↦ (r v : ℂ)) y)) :
    LowerSemicontinuousAt (extendToAdeles T r F) (toAdele y) := by
  have h_comp : LowerSemicontinuousAt
      (F ∘ fun z : 𝔸 E ↦ (fun v ↦ r v * z.1 v, evalPlaces T z.2)) (toAdele y) :=
    .comp hF (by fun_prop)
  intro s hs
  filter_upwards [((isOpen_integralOff T).preimage continuous_snd).mem_nhds hy,
    h_comp s (hs.trans_eq (extendToAdeles_toAdele T hy))] with z hz_mem hz_lt
  rwa [extendToAdeles_of_mem T hz_mem]

/-- Let `T` be a finite set of finite places of `E`, let `r > 0`, let `F` be integrable and let `y`
be integral off `T`. Extend `F` to the adeles. The Fourier transform of the extension at `y / ϖ`,
with `ϖ = S.deltaE` the generator of the different, is `volÔ E / ∏ v, r v ^ 2` times the transform
of `F` at the point `ξ` given by `y` and the scales `2πi / (Φ v ϖ * r v)`. -/
lemma integral_stdAddChar_mul_extendToAdeles (hr : ∀ v : InfinitePlace E, 0 < r v)
    (hF : Integrable F) {y : E} (hy : y ∈ ratIntegralOff T) {ξ : (InfinitePlace E → ℂ) × LocProd T}
    (hξ : ξ = ratPoint T (fun v : InfinitePlace E ↦ 2 * π * .I / Φ v S.deltaE / r v) y) :
    ∫ z : 𝔸 E, New.stdAddChar E (toAdele (y / S.deltaE) * -z) * (extendToAdeles T r F z : ℂ) =
      (volÔ E / ∏ v : InfinitePlace E, r v ^ 2 : ℝ) •
        ∫ x : (InfinitePlace E → ℂ) × LocProd T, S.globalChar T (ξ * x) * F x := by
  -- Pull the right side back along `m` to an integral over `U`, and compare the integrands.
  let U : Set (𝔸 E) := Set.univ ×ˢ (integralOff T : Set (𝔸f E))
  let m (z : 𝔸 E) : (InfinitePlace E → ℂ) × LocProd T := (fun v ↦ r v * z.1 v, evalPlaces T z.2)
  let ψ (x : (InfinitePlace E → ℂ) × LocProd T) : ℂ := S.globalChar T (ξ * x)
  set c : ℝ := volÔ E / ∏ v, r v ^ 2
  have hU : MeasurableSet U := (isOpen_univ.prod (isOpen_integralOff T)).measurableSet
  have hm : MeasurePreserving m (volume.restrict U) (ENNReal.ofReal c • volume) :=
    measurePreserving_scale_evalPlaces T hr
  have hψ_cont : Continuous ψ := (S.continuous_globalChar T).comp (continuous_const_mul ξ)
  have h_char {z : 𝔸 E} (hz : z.2 ∈ integralOff T) :
      New.stdAddChar E (toAdele (y / S.deltaE) * -z) = ψ (m z) := by
    have h_arg (v : InfinitePlace E) :
        (ξ * m z).1 v = 2 * π * .I / Φ v S.deltaE * Φ v y * z.1 v := by
      have h_ne : (r v : ℂ) ≠ 0 := ofReal_ne_zero.2 (hr v).ne'
      simp [hξ, m, ratPoint, field]
    have h_snd : (ξ * m z).2 = ratToPlaces T y * evalPlaces T z.2 := by simp [hξ, m, ratPoint]
    simp only [ψ, globalChar, h_arg, h_snd, S.stdAddChar_div_deltaE T hy hz]
  calc
    _ = ∫ z in U, ψ (m z) * F (m z) := by
      rw [← integral_indicator hU]
      congr with z
      by_cases hz : z.2 ∈ integralOff T
      · rw [h_char hz, extendToAdeles_of_mem T hz]
        simp [U, m, hz]
      · simp [extendToAdeles_of_notMem T hz, U, hz]
    _ = ∫ x, ψ x * F x ∂(ENNReal.ofReal c • volume) := hm.hasLaw.integral_comp
      ((hψ_cont.aestronglyMeasurable.mul hF.ofReal.aestronglyMeasurable).smul_measure _)
    _ = c • ∫ x, ψ x * F x := by rw [integral_smul_measure, toReal_ofReal (by positivity)]

end

end ExtendToAdeles

omit [WeilData E] [T.StarStable] in
/-- One-sided Poisson summation over the infinite places and a finite set `T` of finite places. Let
the elements of `V` be integral off `T`, read as points (`ratPoint`) scaled by `r > 0` at infinity.
Let `F ≥ 0` be integrable and lower semicontinuous at these points. Let its Fourier transform at
each unit `ξ` have modulus at most `β ξ * M` with `0 ≤ M`. Let `ε` bound the finite sums of `β` over
nonzero `T`-integers, scaled by `2πi / (Φ v ϖ * r v)`. Then the sum of `F` over the points is at
most `volÔ E / ∏ v, r v ^ 2` times `ε * M + ∫ F`, with `volÔ E` the volume of the integral finite
adeles. -/
lemma sum_ratPoint_le_mul_add_integral_of_fourier_le {r : InfinitePlace E → ℝ}
  (hr : ∀ v : InfinitePlace E, 0 < r v)
    {V : Finset Eˣ} (hV : ∀ t ∈ V, (t : E) ∈ ratIntegralOff T)
    {β : (InfinitePlace E → ℂ) × LocProd T → ℝ} {ε M : ℝ}
    (hβ : ∀ X : Finset E, (∀ y ∈ X, y ≠ 0) → (∀ y ∈ X, y ∈ ratIntegralOff T) →
      ∑ y ∈ X, β (ratPoint T (fun v : InfinitePlace E ↦ 2 * π * .I / Φ v S.deltaE / r v) y) ≤ ε)
    {F : (InfinitePlace E → ℂ) × LocProd T → ℝ} (hF : Integrable F) (hF_nonneg : 0 ≤ F)
    (hM_nonneg : 0 ≤ M) (hF_lsc : ∀ t ∈ V,
      LowerSemicontinuousAt F (ratPoint T (fun v : InfinitePlace E ↦ (r v : ℂ)) (t : E)))
    (hF_hat : ∀ ξ : (InfinitePlace E → ℂ) × LocProd T, IsUnit ξ →
      ‖∫ x : (InfinitePlace E → ℂ) × LocProd T, S.globalChar T (ξ * x) * F x‖ ≤ β ξ * M) :
    ∑ t ∈ V, F (ratPoint T (fun v : InfinitePlace E ↦ (r v : ℂ)) (t : E)) ≤
      volÔ E / (∏ v : InfinitePlace E, r v ^ 2) *
        (ε * M + ∫ x : (InfinitePlace E → ℂ) × LocProd T, F x) := by
  classical
  -- Apply Poisson summation on the adeles to the extension `G` of `F`. Its transform `FG y` at
  -- `y / ϖ` is zero unless `y` is a `T`-integer, and then it is `c` times the transform `FF y` of
  -- `F` at the matching frequency `f y`.
  set c : ℝ := volÔ E / ∏ v, r v ^ 2
  let G : 𝔸 E → ℝ := extendToAdeles T r F
  let f : E → (InfinitePlace E → ℂ) × LocProd T := ratPoint T fun v ↦
    2 * π * .I / Φ v S.deltaE / r v
  let FG (y : E) : ℂ := ∫ z, New.stdAddChar E (toAdele (y / S.deltaE) * -z) * (G z : ℂ)
  let FF (y : E) : ℂ := ∫ x, S.globalChar T (f y * x) * F x
  have h_supp (y : E) (hy : ‖FG y‖ ≠ 0) : y ∈ ratIntegralOff T :=
    S.mem_ratIntegralOff_of_transform_ne_zero T
      (fun a ha z ↦ congrArg Complex.ofReal (extendToAdeles_sub_adeleOfLocal_add T ha z))
        (norm_ne_zero_iff.1 hy)
  have h_norm (y : E) (hy : y ∈ ratIntegralOff T) : ‖FG y‖ = c * ‖FF y‖ := by
    rw [show FG y = c • FF y from S.integral_stdAddChar_mul_extendToAdeles T hr hF hy rfl,
      norm_smul,
      Real.norm_of_nonneg (by positivity)]
  have h_zero : ‖FF 0‖ = ∫ x, F x := by
    simp [FF, f, ratPoint, globalChar, wave, integral_complex_ofReal, integral_nonneg hF_nonneg]
  have h_unit {y : E} (hy : y ≠ 0) : IsUnit (f y) := by
    simp [f, ratPoint, Prod.isUnit_iff, Pi.isUnit_iff, IsUnit.map, ne_of_gt, hr, hy]
  have h_bound (Y : Finset E) : ∑ y ∈ Y, ‖FG y‖ ≤ c * (ε * M + ∫ x, F x) := by
    let X : Finset E := {y ∈ Y | y ∈ ratIntegralOff T}.erase 0
    have h_freq : ∑ y ∈ X, β (f y) ≤ ε := hβ X (fun y hy ↦ ne_of_mem_erase hy)
      fun y hy ↦ (mem_filter.1 (mem_of_mem_erase hy)).2
    calc
      _ = ∑ y ∈ Y with y ∈ ratIntegralOff T, c * ‖FF y‖ := by
        rw [← sum_filter_of_ne fun y _ ↦ h_supp y]
        exact sum_congr rfl fun y hy ↦ h_norm y (mem_filter.1 hy).2
      _ ≤ ∑ y ∈ insert 0 X, c * ‖FF y‖ := by
        gcongr
        exact insert_erase_subset 0 _
      _ = c * (∫ x, F x) + ∑ y ∈ X, c * ‖FF y‖ := by rw [sum_insert (notMem_erase 0 _), h_zero]
      _ ≤ c * (∫ x, F x) + ∑ y ∈ X, c * (β (f y) * M) := by
        gcongr with y hy
        exact hF_hat (f y) (h_unit (ne_of_mem_erase hy))
      _ ≤ _ := by grw [← mul_sum, ← sum_mul, h_freq, mul_add, add_comm]
  -- The frequencies are reindexed by `y ↦ y / ϖ`.
  have h_all (Y : Finset E) :
      ∑ y ∈ Y, ‖∫ z, New.stdAddChar E (toAdele y * -z) * (G z : ℂ)‖ ≤ c * (ε * M + ∫ x, F x) := by
    simpa [FG, S.deltaE_ne_zero] using
      h_bound (Y.map (Equiv.mulRight₀ _ S.deltaE_ne_zero).toEmbedding)
  let ι : Eˣ ↪ ratAdeles E :=
    ⟨fun t ↦ ⟨toAdele (t : E), t, rfl⟩, fun t ↦ by simp [toAdele, Units.val_inj]⟩
  calc
    _ = ∑ t ∈ V.map ι, G t := by
      rw [sum_map]
      exact sum_congr rfl fun t ht ↦ (extendToAdeles_toAdele T (hV t ht)).symm
    _ ≤ _ := IsDualFamily.sum_le_of_fourier (integrable_extendToAdeles T hr hF)
      (Set.indicator_nonneg fun z _ ↦ hF_nonneg _) (V.map ι) (forall_mem_map.2 fun t ht ↦
        lowerSemicontinuousAt_extendToAdeles T (hV t ht) (hF_lsc t ht)) h_all

/-- A head is a sequence of entries on which the forms of the sieve are evaluated. Here each entry
is a unit at every infinite place together with a unit of the product of the completions at `T`. -/
abbrev GlobalHead : Type := ℕ → (InfinitePlace E → ℂˣ) × (LocProd T)ˣ

/-- A point of the product of the infinite places and `T` as a unit. A component at an infinite
place that is zero is replaced by `1`, and so is the component in `LocProd T` if it is not a
unit. -/
noncomputable abbrev unitOrOneAtPlaces (x : (InfinitePlace E → ℂ) × LocProd T) :
    (InfinitePlace E → ℂˣ) × (LocProd T)ˣ :=
  Prod.map (unitOrOne ∘ ·) unitOrOne x

/-- A sieve system on the product of the infinite places and `T`, for the character
`S.globalChar T`. The density `J i` pairs two heads and, for `i ≤ n`, is the integral of `J (i + 1)`
over a common entry at position `i`. The density at the last entry `J (n + 1)` is continuous, and
positive semidefinite on heads with a common entry at position `n`; the mass `J 0` has modulus at
most `En`. The transform of `J (i + 1)` in the common entry at a unit `ξ` has modulus at most the
decay `β ξ` times the weights `Λ i` of the two heads. For `i < n`, the same bound with weights
`Λ (i + 1)` holds for `J (i + 1)` at two heads with entries `t`, `s` at position `i`, if
`ξ = 1 / t - 1 / s` (divided by the level `M = S.M` at `T`) is a unit. -/
abbrev IsGlobalSieveSystem (n : ℕ) (J : ℕ → GlobalHead T → GlobalHead T → ℂ) (En : ℝ)
    (Λ : ℕ → GlobalHead T → ℝ) (β : (InfinitePlace E → ℂ) × LocProd T → ℝ) : Prop :=
  SieveSystem (unitOrOneAtPlaces T)
    (Prod.map (fun z : InfinitePlace E → ℂˣ ↦ (fun w : ℂˣ ↦ ((w⁻¹ : ℂˣ) : ℂ)) ∘ z)
      fun w : (LocProd T)ˣ ↦ ratToPlaces T (S.M : E)⁻¹ * ((w⁻¹ : (LocProd T)ˣ) : LocProd T))
    n J (S.globalChar T) En Λ β

/-- `ε` bounds the sums of the decay `β` over nonzero frequencies that are integral off `T`, at all
scales `c v / frameScaleSq v a` with `‖c v‖⁻¹ ≤ |realM v| / M`. These cover the frequencies of
Poisson summation (`c v = 2πi / Φ v ϖ`) and, when `1 ≤ |realM v|`, of two heads with different last
entries (`c v = M`). Here `M` is the level, `realM v` is the real number `M * Φ v ϖ / (2πi)`, and
`frameScaleSq v a = realM v ^ (2 (ϱ - a)) / N` scales the entry `a`. -/
def BoundsDecay (β : (InfinitePlace E → ℂ) × LocProd T → ℝ) (ε : ℝ) : Prop :=
  ∀ (a : ℕ) (c : InfinitePlace E → ℂ), (∀ v : InfinitePlace E, ‖c v‖⁻¹ ≤ |S.realM v| / S.M) →
    ∀ X : Finset E, (∀ y ∈ X, y ≠ 0) → (∀ y ∈ X, y ∈ ratIntegralOff T) →
      ∑ y ∈ X, β (ratPoint T (fun v : InfinitePlace E ↦ c v / S.frameScaleSq v a) y) ≤ ε

/-- The number `t` as the entry `a` of a head: scaled at the infinite place `v` by
`S.frameScaleSq v a = κ_v ^ (2 (ϱ - a)) / N`, with `κ_v = S.realM v`, and read at `T`. -/
noncomputable def scaledEntry (a : ℕ) (t : Eˣ) : (InfinitePlace E → ℂ) × LocProd T :=
  ratPoint T (fun v : InfinitePlace E ↦ (S.frameScaleSq v a : ℂ)) (t : E)

/-- The head with first entries `p`, next entry `t` and later entries `1`, read in the scaled frame
at the infinite places and at `T`. -/
noncomputable def scaledHead {A : Finset Eˣ} {i : ℕ} (p : Fin i → A) (t : Eˣ) : GlobalHead T :=
  fun a : ℕ ↦ unitOrOneAtPlaces T (S.scaledEntry T a (padTuple (fun j : Fin i ↦ (p j : Eˣ)) t a))

/-- The constant of Poisson summation in the entry `a`: the volume of the integral finite adeles
divided by the Jacobian of the scaling at the infinite places. -/
noncomputable def poissonConst (a : ℕ) : ℝ :=
  volÔ E / ∏ v : InfinitePlace E, S.frameScaleSq v a ^ 2

omit [WeilData E] in
lemma poissonConst_nonneg (a : ℕ) : 0 ≤ S.poissonConst a :=
  div_nonneg (by positivity) (by positivity)

/-- The sum of the densities `J (i + 1)` over the pairs of heads of length `i` with entries in `A`,
at the common next entry `x`. -/
noncomputable def entryDensity (A : Finset Eˣ) (J : ℕ → GlobalHead T → GlobalHead T → ℂ) (i : ℕ)
    (x : (InfinitePlace E → ℂ) × LocProd T) : ℂ :=
  ∑ p : Fin i → A, ∑ q : Fin i → A, J (i + 1)
    (Function.update (S.scaledHead T p 1) i (unitOrOneAtPlaces T x))
    (Function.update (S.scaledHead T q 1) i (unitOrOneAtPlaces T x))

/-- The sum of densities in which `i` entries are still summed over `A`, the last of them common
to the two heads: the real part of the mass for `i = 0`, and of the sum of `entryDensity (i - 1)`
over `A` for `i > 0`. -/
noncomputable def densitySum (A : Finset Eˣ) (J : ℕ → GlobalHead T → GlobalHead T → ℂ) : ℕ → ℝ
  | 0 => (J 0 (S.scaledHead T (A := A) ![] 1) (S.scaledHead T (A := A) ![] 1)).re
  | i + 1 => ∑ t ∈ A, (S.entryDensity T A J i (S.scaledEntry T i t)).re

section OneEntryFewer

variable {A : Finset Eˣ} {n : ℕ} {J : ℕ → GlobalHead T → GlobalHead T → ℂ} {massBound ε : ℝ}
  {Λ : ℕ → GlobalHead T → ℝ} {β : (InfinitePlace E → ℂ) × LocProd T → ℝ}

omit [WeilData E] [T.StarStable]

/-- At the point `scaledEntry T i t` (the unit `t` as entry `i`, scaled at each infinite place `v`
by `frameScaleSq v i` and read at `T`), the entry density `entryDensity T A J i` is the sum of
`J (i + 1)` over the pairs of heads `scaledHead T p t`, `scaledHead T q t`. These heads have first
entries `p`, `q : Fin i → A`, common next entry `t`, and later entries `1`. -/
lemma entryDensity_scaledEntry (i : ℕ) (t : Eˣ) :
    S.entryDensity T A J i (S.scaledEntry T i t) =
      ∑ p : Fin i → A, ∑ q : Fin i → A, J (i + 1) (S.scaledHead T p t) (S.scaledHead T q t) := by
  have h_update (p : Fin i → A) : Function.update (S.scaledHead T p 1) i
      (unitOrOneAtPlaces T (S.scaledEntry T i t)) = S.scaledHead T p t := by
    simp +contextual [scaledHead, padTuple, Function.update_eq_iff]
  simp only [entryDensity, h_update]

/-- A head whose first entries are `p` followed by `t`, and whose later entries are `1`, is the head
with first entries `p` and next entry `t`. -/
lemma scaledHead_snoc {i : ℕ} (p : Fin i → A) (t : A) :
    S.scaledHead T (Fin.snoc p t : Fin (i + 1) → A) 1 = S.scaledHead T p t :=
  funext fun a ↦ by grind [scaledHead, padTuple, Fin.snoc, Fin.castLT]

/-- For a sieve system of length `n` with densities `J` and `i ≤ n`, the sum of `J (i + 1)` over the
pairs of heads with a common entry at position `i` is a nonnegative real number. -/
lemma entryDensity_nonneg (K : S.IsGlobalSieveSystem T n J massBound Λ β) {i : ℕ} (hi : i ≤ n) :
    0 ≤ S.entryDensity T A J i :=
  fun _ ↦ K.sum_nonneg hi _ fun _ ↦ Function.update_self ..

/-- Let `K` be a sieve system of length `n` with densities `J`, let `A` be a finite set of units of
`E`, and let `i ≤ n`. The entry density at `x` (`entryDensity`) is the sum of `J (i + 1)` over the
pairs of heads with first `i` entries in `A` and common entry `x` at position `i`. Its real part is
lower semicontinuous in `x` at each point `scaledEntry T i t`, which is the unit `t` scaled at each
infinite place `v` by `frameScaleSq v i = κ_v ^ (2 (ϱ - i)) / N` and read at `T`. -/
lemma lowerSemicontinuousAt_entryDensity (K : S.IsGlobalSieveSystem T n J massBound Λ β) {i : ℕ}
    (hi : i ≤ n) (t : Eˣ) :
    LowerSemicontinuousAt
      (fun x : (InfinitePlace E → ℂ) × LocProd T ↦ (S.entryDensity T A J i x).re)
      (S.scaledEntry T i t) := by
  -- The rational point is a unit, where passing to units is continuous.
  have h_cont : ContinuousAt (unitOrOneAtPlaces T) (S.scaledEntry T i t) :=
    .prodMap (.piMap fun v ↦ continuousAt_unitOrOne
        (.mk0 (S.frameScaleSq v i * Φ v t) (by simp [(S.frameScaleSq_pos v i).ne'])))
      (continuousAt_unitOrOne (t.map (ratToPlaces T).toMonoidHom))
  have h_lsc : LowerSemicontinuousAt
      (fun x ↦ ENNReal.ofReal (S.entryDensity T A J i x).re) (S.scaledEntry T i t) :=
    K.lowerSemicontinuousAt_sum hi _ (fun _ _ ↦ Function.update_self ..)
      fun _ ↦ continuousAt_const.update i h_cont
  -- The density is nonnegative, so `ENNReal.ofReal` loses nothing.
  intro y hy
  obtain hy_neg | hy_nonneg := lt_or_ge y 0
  · exact .of_forall fun x ↦ hy_neg.trans_le (S.entryDensity_nonneg T K hi x).1
  · simpa only [ofReal_lt_ofReal_iff_of_nonneg hy_nonneg] using
      h_lsc _ ((ofReal_lt_ofReal_iff_of_nonneg hy_nonneg).2 hy)

/-- Poisson summation in the entry `i ≤ n`. Let `S` satisfy the standing hypotheses
(`IsAdmissible`). Let `J` be the densities of a sieve system of length `n` with weights `Λ` and
decay `β`, summed to at most `ε` over nonzero frequencies (`BoundsDecay`), and let the elements of
`A` be integral off `T`. The head `scaledHead T p 1` has first entries `p` and later entries `1`,
with the entry `a` scaled at the infinite place `v` by `frameScaleSq v a = κ_v ^ (2 (ϱ - a)) / N`.
The left side is the real part of the sum of `J (i + 1)` over the pairs of heads of length `i + 1`
with entries in `A` and a common last entry. Up to the constant `poissonConst i = volÔ E / ∏ v,
frameScaleSq v i ^ 2`, with `volÔ E` the volume of the integral finite adeles, the frequency `0`
gives the sum of `J i` over all pairs of heads of length `i`, and the other frequencies give at most
`ε` times the squared sum of the weights of these heads. -/
lemma densitySum_succ_le [S.IsAdmissible] (hA : ∀ t ∈ A, (t : E) ∈ ratIntegralOff T)
    (K : S.IsGlobalSieveSystem T n J massBound Λ β) (hβ : S.BoundsDecay T β ε) {i : ℕ}
    (hi : i ≤ n) :
    S.densitySum T A J (i + 1) ≤ S.poissonConst i *
      (ε * (∑ p : Fin i → A, Λ i (S.scaledHead T p 1)) ^ 2 +
        (∑ p : Fin i → A, ∑ q : Fin i → A, J i (S.scaledHead T p 1) (S.scaledHead T q 1)).re) := by
  set density : (InfinitePlace E → ℂ) × LocProd T → ℂ := S.entryDensity T A J i
  have h_nonneg : 0 ≤ density := S.entryDensity_nonneg T K hi
  have h_int : Integrable density := K.integrable_sum_update hi (S.scaledHead T · 1)
  have h_integral : ∫ x, (density x).re =
      (∑ p : Fin i → A, ∑ q : Fin i → A, J i (S.scaledHead T p 1) (S.scaledHead T q 1)).re :=
    (integral_re h_int).trans (congrArg re (K.integral_sum_update hi (S.scaledHead T · 1)))
  have h_hat (ξ : (InfinitePlace E → ℂ) × LocProd T) (hξ : IsUnit ξ) :
      ‖∫ x, S.globalChar T (ξ * x) * ((density x).re : ℂ)‖ ≤
        β ξ * (∑ p : Fin i → A, Λ i (S.scaledHead T p 1)) ^ 2 := by
    -- The density is real.
    simp only [← eq_re_of_ofReal_le (h_nonneg _)]
    exact K.norm_integral_mul_sum_update_le hi (S.scaledHead T · 1) hξ
  have h_scale (v : InfinitePlace E) : ‖2 * π * .I / Φ v S.deltaE‖⁻¹ ≤ |S.realM v| / S.M := by
    simp [abs_realM_eq, div_right_comm _ (2 * π), abs_of_pos pi_pos, Nat.Prime.ne_zero]
  rw [← h_integral]
  exact S.sum_ratPoint_le_mul_add_integral_of_fourier_le T (F := fun x ↦ (density x).re)
    (S.frameScaleSq_pos · i) hA
    (hβ i _ h_scale) h_int.re (fun x ↦ (h_nonneg x).1) (sq_nonneg _)
    (fun t _ ↦ S.lowerSemicontinuousAt_entryDensity T K hi t) h_hat

/-- Let `J`, `Λ ≥ 0`, `β` be the densities, weights and decay of a sieve system of length `n`: for
`i < n`, the modulus of `J (i + 1)` at two heads is at most `β ξ` times their weights `Λ (i + 1)` if
the difference `ξ` of the inverses of their entries at position `i` (divided by the level `M = S.M`
at `T`) is a unit. Let `β` sum to at most `ε` over nonzero frequencies (`BoundsDecay`), and let the
inverses of `M` and of the elements of `A` be integral off `T`. At two heads with different entries
`t`, `s` at position `i < n`, the frequency comes from the nonzero `T`-integer
`(1 / t - 1 / s) / M`, so the real part of `J (i + 1)` is at most `ε` times the two weights. -/
lemma re_le_of_last_entries_ne [S.IsAdmissible]
    (hA : ∀ t ∈ A, ((t⁻¹ : Eˣ) : E) ∈ ratIntegralOff T)
    (hM_inv : (S.M : E)⁻¹ ∈ ratIntegralOff T) (K : S.IsGlobalSieveSystem T n J massBound Λ β)
    (hβ : S.BoundsDecay T β ε) (hΛ : ∀ (i : ℕ) (p : GlobalHead T), 0 ≤ Λ i p) {i : ℕ} (hi : i < n)
    {t s : A} (hts : t ≠ s) (p q : Fin i → A) :
    (J (i + 1) (S.scaledHead T p t) (S.scaledHead T q s)).re ≤
      ε * (Λ (i + 1) (S.scaledHead T p t) * Λ (i + 1) (S.scaledHead T q s)) := by
  let y : E := (S.M : E)⁻¹ * (t.1⁻¹.1 - s.1⁻¹.1)
  let ξ : (InfinitePlace E → ℂ) × LocProd T := ratPoint T (fun v ↦ S.M / S.frameScaleSq v i) y
  have y_ne : y ≠ 0 := by
    simp [y, sub_eq_zero, Units.val_inj, hts, Nat.Prime.ne_zero]
  have y_mem : y ∈ ratIntegralOff T := mul_mem hM_inv (sub_mem (hA t t.2) (hA s s.2))
  have ξ_unit : IsUnit ξ := by
    simp [ξ, y_ne, ratPoint, Prod.isUnit_iff, Pi.isUnit_iff, IsUnit.map,
      (S.frameScaleSq_pos _ i).ne', Nat.Prime.ne_zero]
  have h_scale (v : InfinitePlace E) : ‖(S.M : ℂ)‖⁻¹ ≤ |S.realM v| / S.M := by
    grw [← one_le_abs_realM, Complex.norm_natCast, one_div]
  have hβ_le : β ξ ≤ ε := by
    simpa [ξ] using hβ i (fun _ ↦ S.M) h_scale {y} (by simpa using y_ne) (by simpa using y_mem)
  have h_off : ‖J (i + 1) (S.scaledHead T p t) (S.scaledHead T q s)‖ ≤
      β ξ * (Λ (i + 1) (S.scaledHead T p t) * Λ (i + 1) (S.scaledHead T q s)) := by
    have h_raw := K.norm_le_of_isUnit_sub i (S.scaledHead T p t) (S.scaledHead T q s) hi
    -- The frequency `ξ'` of the sieve system at these two heads is `ξ`.
    extract_lets ξ' at h_raw
    have hξ : ξ' = ξ := by
      simp [ξ', ξ, scaledHead, scaledEntry, ratPoint, padTuple, unitOrOne, y, field, funext_iff,
        IsUnit.map, (S.frameScaleSq_pos _ i).ne', ↓map_sub, ↓map_mul, ↓map_units_inv]
      intro v
      field [Nat.Prime.ne_zero]
    rw [hξ] at h_raw
    exact h_raw ξ_unit
  grw [re_le_norm, h_off, hβ_le]
  exact mul_nonneg (hΛ _ _) (hΛ _ _)

/-- Let `J`, `Λ ≥ 0`, `β` be the densities, weights and decay of a sieve system of length `n`. Let
`β` sum to at most `ε ≥ 0` over nonzero frequencies (`BoundsDecay`), and let the inverses of the
level `M = S.M` and of the elements of `A` be integral off `T`. For `i ≤ n`, sum the real part of
`J i` over the pairs of heads of length `i` with entries in `A`. The pairs with equal last entries
give `densitySum T A J i`, by definition, and the others give at most `ε` times the squared sum of
the weights. -/
lemma re_sum_sum_le_densitySum_add [S.IsAdmissible]
    (hA : ∀ t ∈ A, ((t⁻¹ : Eˣ) : E) ∈ ratIntegralOff T)
    (hM_inv : (S.M : E)⁻¹ ∈ ratIntegralOff T) (K : S.IsGlobalSieveSystem T n J massBound Λ β)
    (hβ : S.BoundsDecay T β ε) (hε : 0 ≤ ε) (hΛ : ∀ (i : ℕ) (p : GlobalHead T), 0 ≤ Λ i p) {i : ℕ}
    (hi : i ≤ n) :
    (∑ p : Fin i → A, ∑ q : Fin i → A, J i (S.scaledHead T p 1) (S.scaledHead T q 1)).re ≤
      S.densitySum T A J i + ε * (∑ p : Fin i → A, Λ i (S.scaledHead T p 1)) ^ 2 := by
  classical
  obtain _ | i := i
  · -- There is a single pair of empty heads.
    simpa [densitySum, Subsingleton.elim default ![]] using mul_nonneg hε (sq_nonneg _)
  -- Write each head as its first entries and its last entry, and separate equal last entries.
  have h_split (f : (Fin (i + 1) → A) → ℝ) :
      ∑ p, f p = ∑ t : A, ∑ p : Fin i → A, f (Fin.snoc p t) := by
    simp [← (Fin.snocEquiv fun _ ↦ A).sum_comp, sum_prod_type, Fin.snocEquiv]
  let w (t : A) (p : Fin i → A) : ℝ := Λ (i + 1) (S.scaledHead T p t)
  let d (t s : A) (p q : Fin i → A) : ℝ :=
    (J (i + 1) (S.scaledHead T p t) (S.scaledHead T q s)).re
  calc
    _ = ∑ t, ∑ p, ∑ s, ∑ q, d t s p q := by simp only [d, re_sum, h_split, scaledHead_snoc]
    _ ≤ ∑ t, ∑ p, (∑ q, d t t p q + ∑ s ∈ univ.erase t, ∑ q, ε * (w t p * w s q)) := by
      gcongr with t _ p
      rw [← add_sum_erase _ _ (mem_univ t)]
      gcongr with s hs q
      exact S.re_le_of_last_entries_ne T hA hM_inv K hβ hΛ hi (ne_of_mem_erase hs).symm p q
    _ ≤ ∑ t, ∑ p, (∑ q, d t t p q + ∑ s, ∑ q, ε * (w t p * w s q)) := by
      gcongr
      · exact fun s _ _ ↦ Finset.sum_nonneg fun q _ ↦ mul_nonneg hε (mul_nonneg (hΛ _ _) (hΛ _ _))
      · exact erase_subset _ _
    _ = _ := by
      simp only [d, w, densitySum, entryDensity_scaledEntry, re_sum, h_split, scaledHead_snoc,
        sum_add_distrib, ← mul_sum, ← sum_mul, sq, ← A.sum_coe_sort]

/-- Let `J` be the densities of a sieve system with weights `Λ` and decay `β`, summed to at most
`ε`, and let `1 / M` and both `t` and `1 / t` for `t ∈ A` be integral off `T`. Up to the constant of
Poisson summation, each sum of densities is at most the one before plus an error from the nonzero
frequencies and from the pairs of heads with different last entries; each part of the error is at
most `ε` times the squared sum of the weights. -/
lemma densitySum_succ_le_mul_densitySum_add [S.IsAdmissible]
    (hA : ∀ t ∈ A, (t : E) ∈ ratIntegralOff T ∧ ((t⁻¹ : Eˣ) : E) ∈ ratIntegralOff T)
    (hM_inv : (S.M : E)⁻¹ ∈ ratIntegralOff T) (K : S.IsGlobalSieveSystem T n J massBound Λ β)
    (hβ : S.BoundsDecay T β ε) (hε : 0 ≤ ε) (hΛ : ∀ (i : ℕ) (p : GlobalHead T), 0 ≤ Λ i p) {i : ℕ}
    (hi : i ≤ n) :
    S.densitySum T A J (i + 1) ≤ S.poissonConst i *
      (S.densitySum T A J i + 2 * (ε * (∑ p : Fin i → A, Λ i (S.scaledHead T p 1)) ^ 2)) := by
  have hc : 0 ≤ S.poissonConst i := S.poissonConst_nonneg i
  grw [S.densitySum_succ_le T (fun t ht ↦ (hA t ht).1) K hβ hi,
    S.re_sum_sum_le_densitySum_add T (fun t ht ↦ (hA t ht).2) hM_inv K hβ hε hΛ hi, two_mul,
      add_left_comm]

/-- Let `J` be the densities of a sieve system `K` (`IsGlobalSieveSystem`, so `massBound` bounds the
mass `J 0`) with weights `Λ` and decay `β` summed to at most `ε` (`BoundsDecay`), and let `1 / M`
and `t`, `1 / t` for `t ∈ A` be integral off `T`. Let `Γ` bound the squared sums of the weights,
relative to the constants of Poisson summation. Then the `i`-th sum of densities is at most the
product of the first `i` constants times `massBound + 2 i Γ ε`. -/
lemma densitySum_le [S.IsAdmissible]
    (hA : ∀ t ∈ A, (t : E) ∈ ratIntegralOff T ∧ ((t⁻¹ : Eˣ) : E) ∈ ratIntegralOff T)
    (hM_inv : (S.M : E)⁻¹ ∈ ratIntegralOff T) (K : S.IsGlobalSieveSystem T n J massBound Λ β)
    (hβ : S.BoundsDecay T β ε) (hε : 0 ≤ ε) (hΛ : ∀ (i : ℕ) (p : GlobalHead T), 0 ≤ Λ i p) {Γ : ℝ}
    (hΓ : ∀ i ≤ n, (∑ p : Fin i → A, Λ i (S.scaledHead T p 1)) ^ 2 ≤
      Γ * ∏ a ∈ range i, S.poissonConst a) {i : ℕ} (hi : i ≤ n + 1) :
    S.densitySum T A J i ≤ (∏ a ∈ range i, S.poissonConst a) * (massBound + 2 * i * Γ * ε) := by
  induction i with
  | zero => simpa [densitySum] using (re_le_norm _).trans (K.norm_bot_le _ _)
  | succ i ih =>
    have hc : 0 ≤ S.poissonConst i := S.poissonConst_nonneg i
    have hi_le : i ≤ n := Nat.le_of_succ_le_succ hi
    grw [S.densitySum_succ_le_mul_densitySum_add T hA hM_inv K hβ hε hΛ hi_le,
      ih (Nat.le_succ_of_le hi_le), hΓ i hi_le, prod_range_succ, Nat.cast_succ]
    exact le_of_eq (by ring)

end OneEntryFewer

section

omit [WeilData E]

/-- Under the standing hypotheses `IsAdmissible`, each scale
`frameScaleSq v a = κ_v ^ (2 (ϱ - a)) / N`, where κ_v is the real number `realM v`, is at most
`|realM v| ^ (2 ϱ) / N`. -/
lemma frameScaleSq_le_realM_pow [S.IsAdmissible] (v : InfinitePlace E) (a : ℕ) :
    S.frameScaleSq v a ≤ |S.realM v| ^ (2 * 𝔰.ϱ) / S.N := by
  rw [frameScaleSq, ← pow_abs_two_mul]
  gcongr
  exacts [S.one_le_abs_realM v, Nat.sub_le _ _]

/-- The product of the absolute values of the numbers `κ_v = M Φ v ϖ / (2πi)` over the infinite
places is `(M rd / (2π)) ^ f`, because `ϖ` generates the different. Here `rd` is the root
discriminant of `E`, and `f` is the number of infinite places. -/
lemma prod_abs_realM : ∏ v : InfinitePlace E, |S.realM v| =
    (S.M * rootDiscr E / (2 * π)) ^ numInfPlaces E := by
  -- The square of `∏ ‖Φ v ϖ‖` is the norm of the different, that is `|discr E| = rd ^ (2 f)`.
  have h_absNorm : Ideal.absNorm (Ideal.span {S.deltaE}) = (discr E).natAbs := by
    rw [← S.span_deltaE, absNorm_differentIdeal E]
  have h_norm : |(Algebra.norm ℚ S.deltaE.val : ℝ)| = |(discr E : ℝ)| := by
    simpa [← Algebra.coe_norm_int] using congrArg (Nat.cast : ℕ → ℝ) h_absNorm
  have h_varpi : ∏ v : InfinitePlace E, v S.deltaE.val = rootDiscr E ^ numInfPlaces E := by
    rw [← sq_eq_sq₀ (by positivity) (pow_pos (rootDiscr_pos E) _).le,
      ← abs_discr_eq_rootDiscr_pow, ← h_norm]
    simpa [prod_pow] using InfinitePlace.prod_eq_abs_norm S.deltaE.val
  simp only [abs_realM_eq, ← InfinitePlace.apply, mk_Φ, Finset.prod_div_distrib,
    prod_mul_distrib, prod_const, card_univ, h_varpi, div_pow, mul_pow]

/-- The product over the infinite places of the constants in the decay: `scaledVolumeRatio`, a
constant of the shape, times the power `k - n⁷` of `|κ_v| ^ (2 ϱ + 1) / (M N)`, where
`κ_v = S.realM v` is the real number `M * Φ v ϖ / (2πi)`. For admissible `S`, the base of this power
bounds the inverses of the scales of the frequencies in `BoundsDecay`. -/
noncomputable def decayConst : ℝ :=
  ∏ v : InfinitePlace E,
    𝔰.scaledVolumeRatio * (|S.realM v| ^ (2 * 𝔰.ϱ + 1) / (S.M * S.N)) ^ (𝔰.k - 𝔰.n ^ 7)

lemma decayConst_nonneg : 0 ≤ S.decayConst := by
  have ratio_pos : 0 < 𝔰.scaledVolumeRatio := by simp [Shape.scaledVolumeRatio, pi_pos]
  unfold decayConst
  positivity

omit [T.StarStable] in
/-- Let `κ_v = S.realM v` be the real number `M Φ v ϖ / (2πi)`, with `ϖ` the generator of the
different. Let `S` satisfy the standing hypotheses (`IsAdmissible`), among them
`1 ≤ |κ_v| ≤ b ^ 23`. For a frequency `ξ`, with components `ξ.1 v` at the infinite places `v` and
`ξ.2` in `LocProd T`, the product of the completions at `T`, let the decay at `ξ` be the product
over `v` of `scaledVolumeRatio * b ^ (2000 n⁹) * dampedPower (k - n⁷) ‖ξ.1 v‖⁻¹`, times
`frequencyDecay T ξ.2`. Its sum over any finite set of nonzero `T`-integers, read with the scales
`c v / frameScaleSq v a` for any entry `a` and any `c` with `‖c v‖⁻¹ ≤ |κ_v| / M` (`BoundsDecay`),
is at most `decayConst` times `b ^ (2002 n⁹ f)`, with `f` the number of infinite places. -/
lemma boundsDecay_prod [S.IsAdmissible] :
    S.BoundsDecay T
      (fun ξ : (InfinitePlace E → ℂ) × LocProd T ↦
        (∏ v : InfinitePlace E, 𝔰.scaledVolumeRatio * S.b ^ (2000 * 𝔰.n ^ 9) *
          dampedPower (𝔰.k - 𝔰.n ^ 7) ‖ξ.1 v‖⁻¹) * S.frequencyDecay T ξ.2)
      (S.decayConst * S.b ^ (2002 * 𝔰.n ^ 9 * numInfPlaces E)) := by
  -- Sum the frequencies with `x v = realM v ^ (2 * ϱ + 1) / (M * N)`, where `|x v| ≤ B`.
  intro a c hc X hX₀ hXT
  have hb : 1 ≤ S.b := S.one_le_b
  have MN_pos : 0 < S.M * S.N := by simp [Nat.pos_iff_ne_zero, Nat.Prime.ne_zero, S.N_prime.ne_zero]
  have ratio_pos : 0 < 𝔰.scaledVolumeRatio := by simp [Shape.scaledVolumeRatio, pi_pos]
  let x (v : InfinitePlace E) : ℝ := S.realM v ^ (2 * 𝔰.ϱ + 1) / (S.M * S.N)
  let B : ℝ := (S.b ^ 23) ^ (2 * 𝔰.ϱ + 1)
  have abs_x (v : InfinitePlace E) : |x v| = |S.realM v| ^ (2 * 𝔰.ϱ + 1) / (S.M * S.N) := by
    simp [x, abs_div]
  have lower (v : InfinitePlace E) : ‖c v / S.frameScaleSq v a‖⁻¹ ≤ |x v| := by
    have h_pos : 0 < S.frameScaleSq v a := S.frameScaleSq_pos v a
    calc
      _ = ‖c v‖⁻¹ * S.frameScaleSq v a := by simp [div_eq_inv_mul, abs_of_pos h_pos]
      _ ≤ |S.realM v| / S.M * (|S.realM v| ^ (2 * 𝔰.ϱ) / S.N) := by
        grw [hc v, S.frameScaleSq_le_realM_pow v a]
      _ = |x v| := by rw [abs_x, pow_succ', div_mul_div_comm]
  have upper (v : InfinitePlace E) : |x v| ≤ B := by
    grw [abs_x, div_le_self (by positivity) (mod_cast MN_pos), S.abs_realM_le]
  have hB : (S.b * B ^ 2) ^ 3 ≤ S.b ^ 𝔰.n ^ 9 := by
    -- Compare the exponents of `b`, using `n² ≤ n⁹` and that `ϱ` is large.
    simp only [B, ← pow_mul, ← pow_succ']
    gcongr
    grw [← Nat.pow_le_pow_right 𝔰.ϱ.succ_pos (by norm_num : 2 ≤ 9)]
    nlinarith [S.ten_pow_five_le_varrho]
  have h_sum : ∑ y ∈ X,
      (∏ v, dampedPower (𝔰.k - 𝔰.n ^ 7) ‖c v / S.frameScaleSq v a * Φ v y‖⁻¹) *
        (√(genIndex (ratToPlaces T y)) ^ (𝔰.k - 𝔰.n ^ 7) / denomIndex O (ratToPlaces T y) ^ 3) ≤
      ∏ v, |x v| ^ (𝔰.k - 𝔰.n ^ 7) * S.b ^ 𝔰.n ^ 9 := by
    grw [S.sum_frequencies_le T B _ X _ x (by bound) lower upper hX₀ hXT, hB]
  -- Take the constants out of the sum; after the bound for it the two sides are equal.
  simp_rw [ratPoint, frequencyDecay, prod_mul_distrib, mul_assoc, ← mul_sum, ← mul_assoc, ← sum_mul]
  grw [h_sum]
  simp only [decayConst, abs_x, prod_mul_distrib, prod_const, card_univ]
  exact le_of_eq (by ring)

end

/-- The product of the first `j` entries of a head `p` with entries in `A`. -/
noncomputable def headProduct {A : Finset Eˣ} {i : ℕ} (p : Fin i → A) (j : ℕ) : E :=
  ∏ a ∈ range j, (padTuple (fun l : Fin i ↦ (p l : Eˣ)) 1 a : Eˣ)

omit [CMType E] [WeilData E] in
lemma headProduct_ne_zero {A : Finset Eˣ} {i : ℕ} (p : Fin i → A) (j : ℕ) : headProduct p j ≠ 0 :=
  prod_ne_zero_iff.2 fun _ _ ↦ Units.ne_zero _

omit [WeilData E] [T.StarStable] in
lemma headProduct_mem_ratIntegralOff {A : Finset Eˣ} (hA : ∀ t ∈ A, (t : E) ∈ ratIntegralOff T)
    {i : ℕ} (p : Fin i → A) (j : ℕ) : headProduct p j ∈ ratIntegralOff T := by
  simp [headProduct, hA, padTuple, prod_mem, apply_dite, -Subring.mem_comap]

omit [CMType E] [WeilData E] in
/-- A head `p : Fin i → A` (a tuple of `i` units from `A`) is determined by the products
`headProduct p (j + 1)` of its first `j + 1` entries, for `j < i`. -/
lemma headProduct_injective {A : Finset Eˣ} {i : ℕ} :
    Function.Injective fun (p : Fin i → A) (j : Fin i) ↦ headProduct p (j + 1) := by
  intro p q h_eq
  have h_all : ∀ k ≤ i, headProduct p k = headProduct q k
    | 0, _ => by simp [headProduct]
    | k + 1, hk => congrFun h_eq ⟨k, hk⟩
  -- `p j` is the quotient of two consecutive products.
  funext j
  have h_quot : headProduct p (j + 1) / headProduct p j =
      headProduct q (j + 1) / headProduct q j := by rw [h_all (j + 1) j.2, h_all j j.2.le]
  simpa [headProduct, prod_range_succ, padTuple, prod_eq_zero_iff, Units.val_inj] using h_quot

omit [WeilData E] [T.StarStable] in
/-- The product formula for the weights. Let `δ ≠ 0` be integral off `T`, and let `r` bound
`‖Φ v δ‖` and `‖c v‖⁻¹` at all infinite places. Then the product of the numbers
`max 1 ‖c v * Φ v δ‖⁻¹` and of the square root of the index `[O : δ O]` at `T` is at most `r ^ f`,
with `f` the number of infinite places. -/
lemma prod_max_inv_norm_mul_sqrt_genIndex_le {δ : E} (hδ₀ : δ ≠ 0) (hδT : δ ∈ ratIntegralOff T)
    {c : InfinitePlace E → ℂ} {r : ℝ} (hc : ∀ v : InfinitePlace E, ‖c v‖⁻¹ ≤ r)
    (hδ : ∀ v : InfinitePlace E, ‖Φ v δ‖ ≤ r) :
    (∏ v : InfinitePlace E, max 1 ‖c v * Φ v δ‖⁻¹) * √(genIndex (ratToPlaces T δ)) ≤
      r ^ numInfPlaces E := by
  have h_place (v : InfinitePlace E) : max 1 ‖c v * Φ v δ‖⁻¹ * ‖Φ v δ‖ ≤ r := by
    rw [max_mul_of_nonneg _ _ (norm_nonneg _), one_mul, norm_mul, mul_inv,
      inv_mul_cancel_right₀ (by simpa using hδ₀)]
    exact max_le (hδ v) (hc v)
  grw [sqrt_genIndex_le_prod_norm T hδ₀ hδT, ← prod_mul_distrib, h_place, prod_const, card_univ]

section

omit [WeilData E]

/-- Let `S` satisfy the standing hypotheses (`IsAdmissible`), among them `1 ≤ |κ_v|` and
`N ≤ b ^ (60 n)` for the prime `N = S.N`, the size parameter `b = S.b` and `n = ϱ + 1`. For `j ≤ ϱ`,
the inverse of the product of the scales `frameScaleSq v a = κ_v ^ (2 (ϱ - a)) / N`, `a < j`, is at
most `b ^ (60 n²)`. -/
lemma inv_norm_prod_frameScaleSq_le [S.IsAdmissible] (v : InfinitePlace E) {j : ℕ} (hj : j ≤ 𝔰.ϱ) :
    ‖(∏ a ∈ range j, S.frameScaleSq v a : ℂ)‖⁻¹ ≤ S.b ^ (60 * 𝔰.n ^ 2) :=
  calc
    _ = (S.N : ℝ) ^ j / ∏ a ∈ range j, |S.realM v| ^ (2 * (𝔰.ϱ - a)) := by simp [frameScaleSq]
    _ ≤ (S.N : ℝ) ^ j := div_le_self (by positivity)
      (Finset.one_le_prod₀ fun a _ ↦ one_le_pow₀ (S.one_le_abs_realM v))
    _ ≤ (S.b ^ (60 * 𝔰.n)) ^ 𝔰.n := by
      grw [N_le, pow_le_pow_right₀ (one_le_pow₀ S.one_le_b) (hj.trans 𝔰.ϱ.le_succ)]
    _ = _ := by ring

/-- The weight of a head `p` of length `i`, read at the infinite places and at `T`: a product over
the partial products `δ = p 0 * ⋯ * p l`, `l < i`. At an infinite place the factor (`headWeight`) is
`max 1 ‖δ‖⁻¹ ^ n⁶` if `‖δ‖ ≤ b ^ (60 n²)` and `0` otherwise. At `T` the factor (`finHeadWeight`) is
`[O : δ O] ^ (n⁶ / 2)` if `δ` lies in `O` and `0` otherwise. -/
noncomputable def globalWeight (i : ℕ) (p : GlobalHead T) : ℝ :=
  (∏ v : InfinitePlace E, headWeight (S.b ^ (60 * 𝔰.n ^ 2)) (𝔰.n ^ 6) i ((·.1 v) ∘ p)) *
    finHeadWeight (𝔰.n ^ 6) i ((·.2) ∘ p)

omit [T.StarStable] in
lemma globalWeight_nonneg (i : ℕ) (p : GlobalHead T) : 0 ≤ S.globalWeight T i p := by
  unfold globalWeight headWeight finHeadWeight
  positivity

open scoped Classical in
omit [T.StarStable] in
/-- Let `S` satisfy the standing hypotheses (`IsAdmissible`), with size parameter `b = S.b` and
`n = ϱ + 1`. The head `scaledHead T p 1` has first entries `p` and later entries `1`. The entry `a`
is scaled at the infinite place `v` by `frameScaleSq v a = κ_v ^ (2 (ϱ - a)) / N`, where
`κ_v = S.realM v` and `N = S.N`. Its weight (`globalWeight`) is a product over the products
`δ = headProduct p (j + 1)` of the first entries of `p`. At an infinite place `v`, let `Φ v` be the
chosen complex embedding inducing `v`, and let `c j v` be the product of the scales of these
entries. There the factor is `max 1 ‖c j v * Φ v δ‖⁻¹ ^ n⁶` if `‖c j v * Φ v δ‖ ≤ b ^ (60 n²)`, and
`0` otherwise. At `T` the factor is `[O : δ O] ^ (n⁶ / 2)` if `ratToPlaces T δ` lies in `O`, and `0`
otherwise. Here `O` is the ring of integers of the product of the completions at `T`. -/
lemma globalWeight_scaledHead [S.IsAdmissible] {A : Finset Eˣ} {i : ℕ} (p : Fin i → A) :
    let c (j : Fin i) (v : InfinitePlace E) : ℂ := ∏ a ∈ range (j + 1), S.frameScaleSq v a
    S.globalWeight T i (S.scaledHead T p 1) = ∏ j : Fin i,
      (∏ v : InfinitePlace E,
        if ‖c j v * Φ v (headProduct p (j + 1))‖ ≤ S.b ^ (60 * 𝔰.n ^ 2) then
          max 1 ‖c j v * Φ v (headProduct p (j + 1))‖⁻¹ ^ 𝔰.n ^ 6 else 0) *
      if ratToPlaces T (headProduct p (j + 1)) ∈ O then
        √(genIndex (ratToPlaces T (headProduct p (j + 1)))) ^ 𝔰.n ^ 6 else 0 := by
  intro c
  have h_inf (j : Fin i) (v : InfinitePlace E) :
      ∏ a ∈ range (j + 1), ((S.scaledHead T p 1 a).1 v : ℂ) =
        c j v * Φ v (headProduct p (j + 1)) := by
    simp [c, headProduct, scaledHead, scaledEntry, ratPoint, unitOrOne,
      (S.frameScaleSq_pos _ _).ne', prod_mul_distrib]
  have h_fin (j : Fin i) : ∏ a ∈ range (j + 1), ((S.scaledHead T p 1 a).2 : LocProd T) =
      ratToPlaces T (headProduct p (j + 1)) := by
    simp [headProduct, scaledHead, scaledEntry, ratPoint, unitOrOne, IsUnit.map]
  simp only [globalWeight, headWeight, finHeadWeight, prod_range (n := i), Function.comp_apply,
    h_inf, h_fin]
  rw [Finset.prod_comm, ← prod_mul_distrib]

omit [T.StarStable] in
/-- Let `S` satisfy the standing hypotheses (`IsAdmissible`), and let `p` be a head of length
`i ≤ ϱ` with entries in a finite set `A` of numbers integral off `T`. Suppose the weight
(`globalWeight`) of `scaledHead T p 1`, the head with first entries `p` and later entries `1` read
in the scaled frame, is not zero. Then the products of the first entries of `p` are integers of `E`
of modulus at most `b ^ (120 n²)` at all infinite places. -/
lemma isIntegral_headProduct_and_norm_le [S.IsAdmissible] {A : Finset Eˣ}
    (hA : ∀ t ∈ A, (t : E) ∈ ratIntegralOff T) {i : ℕ} (hi : i ≤ 𝔰.ϱ) {p : Fin i → A}
    (hp : S.globalWeight T i (S.scaledHead T p 1) ≠ 0) (j : Fin i) :
    IsIntegral ℤ (headProduct p (j + 1)) ∧
      ∀ v : InfinitePlace E, ‖Φ v (headProduct p (j + 1))‖ ≤ S.b ^ (120 * 𝔰.n ^ 2) := by
  classical
  rw [globalWeight_scaledHead] at hp
  obtain ⟨h_inf, h_fin⟩ := mul_ne_zero_iff.1 (prod_ne_zero_iff.1 hp j (mem_univ j))
  refine ⟨?_, fun v ↦ ?_⟩
  · -- integral at `T` and off `T`
    rw [← algebraMap_mem_Ô, mem_Ô_iff T]
    exact ⟨(ite_ne_right_iff.1 h_fin).1, headProduct_mem_ratIntegralOff T hA p (j + 1)⟩
  · have hb : 1 ≤ S.b := S.one_le_b
    let c : ℂ := ∏ a ∈ range (j + 1), S.frameScaleSq v a
    have h_small : ‖c * Φ v (headProduct p (j + 1))‖ ≤ S.b ^ (60 * 𝔰.n ^ 2) :=
      (ite_ne_right_iff.1 (prod_ne_zero_iff.1 h_inf v (mem_univ v))).1
    calc
      _ = ‖c‖⁻¹ * ‖c * Φ v (headProduct p (j + 1))‖ := by
        simp [c, prod_ne_zero_iff, (S.frameScaleSq_pos v _).ne']
      _ ≤ S.b ^ (60 * 𝔰.n ^ 2) * S.b ^ (60 * 𝔰.n ^ 2) := by
        grw [h_small, S.inv_norm_prod_frameScaleSq_le v (j.2.trans_le hi)]
      _ = _ := by ring

omit [T.StarStable] in
/-- The largest weight. Let `S` satisfy the standing hypotheses (`IsAdmissible`), and let `p` be a
tuple of length `i ≤ ϱ` with entries integral off `T`. The head `scaledHead T p 1` has first entries
`p` and later entries `1`, with the entry `a` scaled at the infinite place `v` by
`frameScaleSq v a = κ_v ^ (2 (ϱ - a)) / N` (`κ_v = S.realM v`, `N = S.N`). Its weight
(`globalWeight`) is a product over the partial products `δ` of its first `i` entries, of
`max 1 ‖δ‖⁻¹ ^ n⁶` or `0` at each infinite place and of `[O : δ O] ^ (n⁶ / 2)` or `0` at `T`, with
`O` the integers at `T`. This weight is at most `b ^ (120 n⁸ f i)`. Here `b = S.b` is the size
parameter, `n = ϱ + 1`, and `f` is the number of infinite places. -/
lemma globalWeight_scaledHead_le [S.IsAdmissible] {A : Finset Eˣ}
    (hA : ∀ t ∈ A, (t : E) ∈ ratIntegralOff T) {i : ℕ} (hi : i ≤ 𝔰.ϱ) (p : Fin i → A) :
    S.globalWeight T i (S.scaledHead T p 1) ≤ S.b ^ (120 * 𝔰.n ^ 8 * numInfPlaces E * i) := by
  classical
  have hb : 1 ≤ S.b := S.one_le_b
  by_cases hp : S.globalWeight T i (S.scaledHead T p 1) = 0
  · exact hp.trans_le (by positivity)
  -- Each product `δ j` is small, so it contributes at most `(b ^ (120 n²)) ^ (f n⁶)`.
  let c (j : Fin i) (v : InfinitePlace E) : ℂ := ∏ a ∈ range (j + 1), S.frameScaleSq v a
  let δ (j : Fin i) : E := headProduct p (j + 1)
  have h_factor (j : Fin i) : (∏ v, max 1 ‖c j v * Φ v (δ j)‖⁻¹) *
      √(genIndex (ratToPlaces T (δ j))) ≤ (S.b ^ (120 * 𝔰.n ^ 2)) ^ numInfPlaces E :=
    prod_max_inv_norm_mul_sqrt_genIndex_le T (headProduct_ne_zero p _)
      (headProduct_mem_ratIntegralOff T hA p _)
      (fun v ↦ (S.inv_norm_prod_frameScaleSq_le v (j.2.trans_le hi)).trans
        (pow_le_pow_right₀ hb (by lia)))
      (S.isIntegral_headProduct_and_norm_le T hA hi hp j).2
  rw [globalWeight_scaledHead]
  calc
    _ ≤ ∏ j : Fin i, (∏ v, max 1 ‖c j v * Φ v (δ j)‖⁻¹ ^ 𝔰.n ^ 6) *
        √(genIndex (ratToPlaces T (δ j))) ^ 𝔰.n ^ 6 := by
      gcongr ∏ j, (∏ v, ?_) * ?_ with j _ v
      all_goals
        split_ifs
        exacts [le_rfl, by positivity]
    _ ≤ ∏ _j : Fin i, ((S.b ^ (120 * 𝔰.n ^ 2)) ^ numInfPlaces E) ^ 𝔰.n ^ 6 := by
      simp only [prod_pow (univ : Finset (InfinitePlace E)), ← mul_pow]
      grw [h_factor]
    _ = _ := by
      rw [prod_const, card_univ, Fintype.card_fin]
      ring

omit [T.StarStable] in
/-- The sum of the weights of the heads of length `i ≤ ϱ` with entries in a finite set `A` of
numbers integral off `T` is at most `b ^ (130 n⁹ f)`: the number of heads whose products are small
integers, times the largest weight. Here `b = S.b` is the size parameter of the admissible filling
data `S`, `n = ϱ + 1`, and `f` is the number of infinite places. -/
lemma sum_globalWeight_le [S.IsAdmissible] {A : Finset Eˣ}
    (hA : ∀ t ∈ A, (t : E) ∈ ratIntegralOff T) {i : ℕ} (hi : i ≤ 𝔰.ϱ) :
    ∑ p : Fin i → A, S.globalWeight T i (S.scaledHead T p 1) ≤
      S.b ^ (130 * 𝔰.n ^ 9 * numInfPlaces E) := by
  classical
  have hb : 1 ≤ S.b := S.one_le_b
  let P : Finset (Fin i → A) := {p | S.globalWeight T i (S.scaledHead T p 1) ≠ 0}
  have h_card : (#P : ℝ) ≤ (1 + 2 * S.b ^ (120 * 𝔰.n ^ 2)) ^ (i * numInfPlaces E * 2) := by
    rw [← ofReal_le_ofReal_iff (by positivity), ENNReal.ofReal_natCast]
    simpa using encard_le_of_isIntegral_norm_le (A := (P : Set (Fin i → A)))
      (fun p (j : Fin i) ↦ headProduct p (j + 1)) (by positivity)
      (fun p hp ↦ S.isIntegral_headProduct_and_norm_le T hA hi (mem_filter.1 hp).2)
      headProduct_injective.injOn
  have h_base : 1 + 2 * S.b ^ (120 * 𝔰.n ^ 2) ≤ S.b ^ (120 * 𝔰.n ^ 2 + 1) := by
    rw [pow_succ S.b]
    nlinarith [S.thousand_le_b, one_le_pow₀ hb (n := 120 * 𝔰.n ^ 2)]
  calc
    _ = ∑ p ∈ P, S.globalWeight T i (S.scaledHead T p 1) := (sum_filter_ne_zero univ).symm
    _ ≤ #P * S.b ^ (120 * 𝔰.n ^ 8 * numInfPlaces E * i) := by
      grw [S.globalWeight_scaledHead_le T hA hi, sum_const, nsmul_eq_mul]
    _ ≤ (S.b ^ (120 * 𝔰.n ^ 2 + 1)) ^ (𝔰.n * numInfPlaces E * 2) *
        S.b ^ (120 * 𝔰.n ^ 8 * numInfPlaces E * 𝔰.n) := by
      grw [h_card, h_base, hi.trans 𝔰.ϱ.le_succ, hi.trans 𝔰.ϱ.le_succ]
      exact one_le_pow₀ hb
    _ ≤ _ := by
      rw [← pow_mul, ← pow_add]
      gcongr
      obtain ⟨m, hm⟩ : ∃ m : ℕ, 𝔰.ϱ = 10 ^ 5 + m := exists_add_of_le S.ten_pow_five_le_varrho
      simp only [Shape.n, hm]
      lia

/-- For `i ≤ ϱ`, the product of the first `i` constants of Poisson summation is at least
`b ^ (-100 n² f)`, with `f` the number of infinite places. -/
lemma one_le_pow_mul_prod_poissonConst [S.IsAdmissible] {i : ℕ} (hi : i ≤ 𝔰.ϱ) :
    1 ≤ S.b ^ (100 * 𝔰.n ^ 2 * numInfPlaces E) * ∏ a ∈ range i, S.poissonConst a := by
  -- Use `frameScaleSq v a ≤ b ^ (46 * ϱ)` and the value `(2 / rd) ^ f` of `volÔ E`.
  have hb : 1 ≤ S.b := S.one_le_b
  have rd_pos : 0 < rootDiscr E := rootDiscr_pos E
  have scale_le (v : InfinitePlace E) (a : ℕ) : S.frameScaleSq v a ≤ (S.b ^ 23) ^ (2 * 𝔰.ϱ) := by
    grw [S.frameScaleSq_le_realM_pow, div_le_self (by positivity) (mod_cast S.N_prime.pos),
      S.abs_realM_le]
  calc
    _ ≤ S.b ^ (100 * 𝔰.n ^ 2 * numInfPlaces E) * ∏ _a ∈ range i,
          (S.b ^ numInfPlaces E)⁻¹ / ∏ _v : InfinitePlace E, ((S.b ^ 23) ^ (2 * 𝔰.ϱ)) ^ 2 := by
      simp [field, ← pow_mul, ← pow_add]
      gcongr
      grw [hi]
      lia
    _ ≤ _ := by
      simp only [poissonConst]
      grw [volÔ_eq, scale_le, half_le_self (by bound), S.rootDiscr_le_b]
      exacts [(S.frameScaleSq_pos _ _).le, prod_pos fun v _ ↦ pow_pos (S.frameScaleSq_pos v _) 2]

omit [T.StarStable] in
/-- Let `S` satisfy the standing hypotheses `IsAdmissible`. Let `b = S.b`, `ϱ = 𝔰.ϱ`, `n = ϱ + 1`,
and let `f` be the number of infinite places. Let `A` be a finite set of units of `E` integral off
`T`, and let `i ≤ ϱ`. Sum, over heads `p` of length `i` with entries in `A`, the weight
`globalWeight T i` of the head `scaledHead T p 1`. The square of this sum is at most
`b ^ (400 n⁹ f)` times the product of the first `i` constants `poissonConst a` of Poisson
summation. -/
lemma sq_sum_globalWeight_le [S.IsAdmissible] {A : Finset Eˣ}
    (hA : ∀ t ∈ A, (t : E) ∈ ratIntegralOff T) {i : ℕ} (hi : i ≤ 𝔰.ϱ) :
    (∑ p : Fin i → A, S.globalWeight T i (S.scaledHead T p 1)) ^ 2 ≤
      S.b ^ (400 * 𝔰.n ^ 9 * numInfPlaces E) * ∏ a ∈ range i, S.poissonConst a := by
  have hb : 1 ≤ S.b := S.one_le_b
  have h_prod : 0 ≤ ∏ a ∈ range i, S.poissonConst a :=
    prod_nonneg fun a _ ↦ S.poissonConst_nonneg a
  have h_exp : 130 * 𝔰.n ^ 9 * numInfPlaces E * 2 + 100 * 𝔰.n ^ 2 * numInfPlaces E ≤
      400 * 𝔰.n ^ 9 * numInfPlaces E := by
    grw [Nat.pow_le_pow_right 𝔰.ϱ.succ_pos (by norm_num : 2 ≤ 9)]
    lia
  calc
    _ ≤ (S.b ^ (130 * 𝔰.n ^ 9 * numInfPlaces E)) ^ 2 *
        (S.b ^ (100 * 𝔰.n ^ 2 * numInfPlaces E) * ∏ a ∈ range i, S.poissonConst a) := by
      grw [← S.one_le_pow_mul_prod_poissonConst hi, mul_one, S.sum_globalWeight_le T hA hi]
      exact Finset.sum_nonneg fun p _ ↦ S.globalWeight_nonneg T i _
    _ ≤ _ := by grw [← mul_assoc, ← pow_mul, ← pow_add, h_exp]

end

omit [WeilData E] [T.StarStable] in
/-- The sieve. Let `b = S.b`, `M = S.M` and `N = S.N` be the size parameter, the level and the prime
of the admissible filling data `S`, let `k`, `ϱ`, `n = ϱ + 1` be the parameters of its shape `𝔰`,
and let `f` be the number of infinite places. Let `U ⊆ A`, and let `1 / M` and `t`, `1 / t` for
`t ∈ A` be integral off `T`. Let the forms `J_T i` on pairs of heads (sequences of units) at `T`
satisfy the axioms of the sieve (`SieveSystem`) in length `ϱ`: for `i ≤ ϱ`, `J_T i` is the integral
of `J_T (i + 1)` over a common entry at position `i`, read as a unit (`unitOrOne`); the top form
`J_T n` is continuous, and positive semidefinite on heads with a common entry at position `ϱ`; the
mass `J_T 0` has modulus at most `mass_T`; and the decay `frequencyDecay` times the weights
`finHeadWeight` bounds the transforms for `S.charOnPlaces T` and the forms at heads with entries
`w`, `w'` whose frequency `(1 / w - 1 / w') / M` is a unit. Multiply `J_T` by the forms `bandLimit`
that are part of the Bessel systems `S.besselSystem v` at the infinite places: they satisfy the same
axioms over `ℂ`, with mass at most `(1 + b ^ (-10)) / deg`.

The real part of the sum of the products of the top forms `bandLimit n` and `J_T n` over all pairs
of heads with entries in `A` and a common last entry in `U` is at most the product of the constants
of Poisson summation times the sum of the product of the bounds for the masses and of the error
`b ^ (2403 n⁹ f) * decayConst`. The heads have first entries `p`, then `t`, then `1` (`padTuple`).
At `T` they are `y p t`; at the infinite place `v` they are `x v p t`, with the entry `i` scaled by
`frameScaleSq v i = κ_v ^ (2 (ϱ - i)) / N`, where `κ_v = S.realM v`. The constants are `poissonConst
i = volÔ E / ∏ v, frameScaleSq v i ^ 2`, with `volÔ E` the volume of the integral finite adeles, and
`decayConst = ∏ v, scaledVolumeRatio * (|κ_v| ^ (2 ϱ + 1) / (M N)) ^ (k - n⁷)`. -/
theorem sieve [S.IsAdmissible] {A : Finset Eˣ}
    (hA : ∀ t ∈ A, (t : E) ∈ ratIntegralOff T ∧ ((t⁻¹ : Eˣ) : E) ∈ ratIntegralOff T)
    (hM_inv : (S.M : E)⁻¹ ∈ ratIntegralOff T)
    {J_T : ℕ → (ℕ → (LocProd T)ˣ) → (ℕ → (LocProd T)ˣ) → ℂ} {mass_T : ℝ} {U : Finset Eˣ}
    (hJ_T : SieveSystem unitOrOne
      (fun w : (LocProd T)ˣ ↦ ratToPlaces T (S.M : E)⁻¹ * ((w⁻¹ : (LocProd T)ˣ) : LocProd T))
      𝔰.ϱ J_T (S.charOnPlaces T) mass_T (finHeadWeight (𝔰.n ^ 6)) (S.frequencyDecay T))
    (hU : U ⊆ A) :
    -- the heads at the infinite place `v`
    let x (v : InfinitePlace E) (p : Fin 𝔰.ϱ → A) (t : Eˣ) (i : ℕ) : ℂˣ :=
      unitOrOne (S.frameScaleSq v i * Φ v (padTuple (fun j : Fin 𝔰.ϱ ↦ (p j : Eˣ)) t i : Eˣ))
    -- the heads at `T`
    let y (p : Fin 𝔰.ϱ → A) (t : Eˣ) : ℕ → (LocProd T)ˣ :=
      Units.map (ratToPlaces T) ∘ padTuple (fun j : Fin 𝔰.ϱ ↦ (p j : Eˣ)) t
    (∑ t ∈ U, ∑ p : Fin 𝔰.ϱ → A, ∑ q : Fin 𝔰.ϱ → A,
        (∏ v : InfinitePlace E, (S.besselSystem v).bandLimit 𝔰.n (x v p t) (x v q t)) *
          J_T 𝔰.n (y p t) (y q t)).re ≤
      (∏ i ∈ range 𝔰.n, S.poissonConst i) *
        ((∏ v : InfinitePlace E, (1 + S.b⁻¹ ^ 10) / (S.besselSystem v).deg) * mass_T +
          S.b ^ (2403 * 𝔰.n ^ 9 * numInfPlaces E) * S.decayConst) := by
  -- Remove all entries in the product system. The error is `2 n Γ ε`: here `ε` bounds the decay
  -- summed over the nonzero frequencies, and `Γ` times the product of the first `i` constants of
  -- Poisson summation bounds the squared sum of the weights of the heads of length `i`.
  have hb : 1 ≤ S.b := S.one_le_b
  have h_decay : 0 ≤ S.decayConst := S.decayConst_nonneg
  intro x y
  let J (i : ℕ) (p q : GlobalHead T) : ℂ :=
    (∏ v, (S.besselSystem v).bandLimit i ((·.1 v) ∘ p) ((·.1 v) ∘ q)) *
      J_T i ((·.2) ∘ p) ((·.2) ∘ q)
  let massBound : ℝ := (∏ v, (1 + S.b⁻¹ ^ 10) / (S.besselSystem v).deg) * mass_T
  let Γ : ℝ := S.b ^ (400 * 𝔰.n ^ 9 * numInfPlaces E)
  let ε : ℝ := S.decayConst * S.b ^ (2002 * 𝔰.n ^ 9 * numInfPlaces E)
  have K : S.IsGlobalSieveSystem T 𝔰.ϱ J massBound (S.globalWeight T) fun ξ ↦
      (∏ v, 𝔰.scaledVolumeRatio * S.b ^ (2000 * 𝔰.n ^ 9) * dampedPower (𝔰.k - 𝔰.n ^ 7) ‖ξ.1 v‖⁻¹) *
        S.frequencyDecay T ξ.2 :=
    hJ_T.pi fun v ↦ (S.besselSystem v).hasLocalBounds.1
  have hx (v : InfinitePlace E) (p : Fin 𝔰.ϱ → A) (t : Eˣ) :
      (·.1 v) ∘ S.scaledHead T p t = x v p t := rfl
  have hy (p : Fin 𝔰.ϱ → A) (t : Eˣ) : (·.2) ∘ S.scaledHead T p t = y p t := by
    ext
    simp [y, scaledHead, scaledEntry, ratPoint, unitOrOne, IsUnit.map]
  have len_le : 2 * (𝔰.ϱ + 1 : ℕ) ≤ S.b ^ (𝔰.n ^ 9 * numInfPlaces E) := by
    have h_nat : 2 * (𝔰.ϱ + 1) ≤ 𝔰.k := by linarith [S.thousand_mul_le_k]
    calc
      _ ≤ (𝔰.k : ℝ) := mod_cast h_nat
      _ ≤ S.b := S.k_le_b
      _ ≤ _ := le_self_pow₀ hb (by simp [Fintype.card_ne_zero])
  calc
    _ = ∑ t ∈ U, (S.entryDensity T A J 𝔰.ϱ (S.scaledEntry T 𝔰.ϱ t)).re := by
      simp only [re_sum, entryDensity_scaledEntry, J, hx, hy]
    _ ≤ S.densitySum T A J 𝔰.n :=
      sum_le_sum_of_subset_of_nonneg hU fun t _ _ ↦ (S.entryDensity_nonneg T K le_rfl _).1
    _ ≤ (∏ a ∈ range 𝔰.n, S.poissonConst a) * (massBound + 2 * (𝔰.ϱ + 1 : ℕ) * Γ * ε) :=
      S.densitySum_le T hA hM_inv K (S.boundsDecay_prod T) (by positivity) (S.globalWeight_nonneg T)
        (fun i ↦ S.sq_sum_globalWeight_le T fun t ht ↦ (hA t ht).1) le_rfl
    _ ≤ (∏ a ∈ range 𝔰.n, S.poissonConst a) *
        (massBound + S.b ^ (𝔰.n ^ 9 * numInfPlaces E) * Γ * ε) := by
      grw [len_le]
      exact prod_nonneg fun a _ ↦ S.poissonConst_nonneg a
    _ = _ := by ring

end New.Filling
