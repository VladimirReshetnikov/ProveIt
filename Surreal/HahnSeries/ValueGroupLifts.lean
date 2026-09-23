import Mathlib.RingTheory.HahnSeries.Lex
import Mathlib.RingTheory.HahnSeries.Summable
import Mathlib.RingTheory.HahnSeries.Valuation
import Mathlib.Algebra.Order.Hom.Ring
import Mathlib.Algebra.Algebra.Rat
import Surreal.Algebra.ExponentialProfile
import Surreal.HahnSeries.EulerDerivation
import Surreal.Foundations.SignSequenceField
import Surreal.Foundations.SignSequenceValuation

/-!
# Value-group automorphisms: Hahn lifts, rational dilations and a bounded additive map

This file formalizes `prop:hahn-lift` (`eq:hahn-lift`), `thm:dilation` (with `eq:dilation-error`
and `eq:dilation-contradiction`) and `prop:additive-bounded` of
`docs/surreal/exponential-automorphism-rigidity/article.tex`, together with
`eq:laurent-derivation`, `eq:laurent-contraction` and the consequence of `thm:derivation-valued`
drawn after them. Labels in that report are unprefixed.

## The canonical Hahn lift (`prop:hahn-lift`)

Let `Γ` be a linearly ordered abelian group, `T : Γ ≃+o Γ` an ordered additive automorphism and
`R` a semiring. `hahnLift T : R((t^Γ)) ≃+* R((t^Γ))` is `∑ a_γ t^γ ↦ ∑ a_γ t^{T γ}`, built from
`HahnSeries.embDomain`; `coeff_hahnLift` says that its coefficient at `g` is the old coefficient
at `T⁻¹ g`. It is a ring automorphism with inverse `hahnLift T⁻¹` (`hahnLift_symm`). It fixes
the constants (`hahnLift_C`), induces `T` on values (`orderTop_hahnLift`) and preserves leading
coefficients (`leadingCoeff_hahnLift`). For ordered `R` it preserves the lexicographic order
(`hahnLift_le_iff`), and `hahnLiftOrderRingIso` bundles it as an ordered ring automorphism of
`Lex R((t^Γ))`. It maps every summable family to a summable family (`liftFamily`), with
`∑ T̂ (s a) = T̂ (∑ s a)` (`hsum_liftFamily`). `hahn_lift` bundles these clauses.

## Rational dilations (`thm:dilation`)

`Γ` is any linearly ordered abelian group with a `ℚ`-module structure, that is, a divisible one.
The compatibility of `ℚ`-scaling with the order is derived, not assumed
(`rat_smul_le_smul_iff`). For `r ∈ ℚ_{>0}`, `dilation r hr : Γ ≃+o Γ` is `γ ↦ r γ`. For
`r ≠ 1` its displacement image is all of `Γ` (`range_dilation_sub`), and it is not the identity
when `Γ` is nontrivial (`dilation_ne_refl`).

The non-lifting half is proved for any ordered field `F` with an ordered exponential `E`
(`Surreal.ExponentialProfile.OrderedExp`) and any nontrivial convex valuation
`w : F → WithTop Γ`. Here `σ` ranges over all unital endomorphisms `F →+* F` commuting with `E`,
not only automorphisms, and `w` need not be onto `Γ`.

* `mul_self_eq_of_abs_sub_mul_le` and `eq_one_of_abs_sub_mul_le` (`eq:dilation-contradiction`):
  if `|σ x - r x| ≤ B` for all `x`, then `r² = r`, so `r = 1` when `r ≠ 0`. The source's
  `x = ω` with finite errors is replaced by an `x` that is large compared with `B`.
* `profile_sub_mul_eq_zero_of_nsmul` (`eq:dilation-error`): if the action `τ` of `σ` on values
  satisfies `n • τ g = m • g`, then `ν (σ x - (m/n) x) = 0` for `ν = w ∘ E`, that is,
  `σ x - (m/n) x ∈ ker ν`, the generic form of the source's `σ x - r x ∈ 𝒪`. This
  division-free form replaces the source's `ℚ`-linearity of `ν`; only torsion-freeness of `Γ`
  is used. `exists_abs_sub_lt_of_nsmul`: since `ker ν` is a proper convex subgroup
  (`lem:bridge`), the error is bounded by one `B > 0` for all `x`.
* `eq_of_nsmul_valueMap`: then `m = n`. `not_lift_dilation`: no such `σ` induces `T_r`, that
  is, satisfies `w (σ y) = r • w y` for `y ≠ 0`.
* `dilation_theorem` bundles `thm:dilation` at this generality. `surreal_dilation` gives its
  value-group clauses at `Γ = (No, +, <)`, the additive group of the actual surreal field
  `SignSequence`, where `T_r γ = r γ` is surreal multiplication. `surreal_not_lift_dilation`
  gives the non-lifting clause at `No` for the natural valuation `SignSequence.valuation`,
  conditionally on an ordered exponential `E : OrderedExp SignSequence` supplied as a
  hypothesis.

The source's first, valuation-theoretic contradiction (comparing `v(σ ω) = -1` with
`r v(ω) = -r`) is not formalized; the multiplicative argument proves the theorem by itself.

## Laurent examples (`prop:additive-bounded`, `eq:laurent-derivation`)

`L = R((t))` is `Lex (HahnSeries ℤ R)` for any linearly ordered commutative ring `R`; the source
takes `R = ℝ` (`additive_bounded_real`). The sign of a nonzero element is the sign of its lowest
coefficient (`HahnSeries.leadingCoeff_pos_iff`), and `t = single 1 1` is positive and below every
positive constant (`single_one_pos`, `single_one_lt_C`). `nilShift f = [t¹]f · t²` is the
`R`-linear map `N`, and `addShift = id + N : L ≃+o L` is `T`, with inverse `id - N`.
`additive_bounded` proves every clause of `prop:additive-bounded`: `T ≠ id`, `T 1 = 1`, `T`
fixes the order and the leading coefficient of every element, `|T f - f| < t`, and `T` is not
multiplicative (`T (t²) = t² ≠ (t + t²)² = T(t)²`, `addShift_single_two_ne`).

For a field `R`, `laurentDer = t · (t d/dt)` is the derivation `∂ = t² d/dt` of
`eq:laurent-derivation` (`coeff_laurentDer`: `[t^{n+1}] ∂f = n [t^n] f`; `laurentDer_single`).
It is nonzero (`laurentDer_ne_zero`) and satisfies `eq:laurent-contraction`,
`v_t (∂ f) ≥ v_t f + 1`, for the `t`-adic valuation `addVal ℤ R` (`addVal_add_one_le`). Hence
no map `E : L → L^×` has `∂ (E x) = E x ∂ x` for every `x` (`not_exists_compatible_exp`, from
`Surreal.SigmaDerivation.derivation_eq_zero_of_loss`).

## Pending

The unconditional surreal instantiations remain pending. `prop:hahn-lift` for `No` itself
needs `No` presented as the Hahn field `ℝ((t^No))` with a class-sized exponent group. The
non-lifting clause of `thm:dilation` for `No` is proved by `surreal_not_lift_dilation` for any
ordered exponential on `SignSequence`; the only missing ingredient is the global surreal
exponential itself as an `OrderedExp SignSequence` (the project has the exponential only on
infinitesimals). In the same sections of the report, `prop:single-layer`,
`thm:bounded-layers`, `prop:substitution`, `prop:partial-exp` and the compatibility
`∂ (E_0 x) = E_0(x) ∂ x` of the partial exponential on `t ℝ[[t]]` are not treated here.
-/

namespace Surreal.ValueGroupLifts

open _root_.HahnSeries Surreal.ExponentialProfile

/-! ### Rational dilations of a divisible ordered group -/

section Dilation

variable {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] [Module ℚ Γ]

omit [LinearOrder Γ] [IsOrderedAddMonoid Γ] in
/-- Clearing the denominator of a rational scalar: `q.den • (q • g) = q.num • g`. -/
theorem den_nsmul_smul (q : ℚ) (g : Γ) : q.den • (q • g) = q.num • g := by
  rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, Rat.den_mul_eq_num, Int.cast_smul_eq_zsmul ℚ]

/-- A positive rational scalar maps `Γ_{≥ 0}` into itself. No order compatibility of the
`ℚ`-module structure is assumed: it follows from `q.den • (q • g) = q.num • g`. -/
theorem rat_smul_nonneg {q : ℚ} (hq : 0 < q) {g : Γ} (hg : 0 ≤ g) : 0 ≤ q • g := by
  by_contra h
  push Not at h
  have h1 : q.den • (q • g) < 0 := nsmul_neg h q.den_nz
  obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (Rat.num_pos.2 hq).le
  rw [den_nsmul_smul, hk, natCast_zsmul] at h1
  exact absurd h1 (not_lt.2 (nsmul_nonneg hg k))

/-- Multiplication by a positive rational is an order embedding of `Γ`. -/
theorem rat_smul_le_smul_iff {q : ℚ} (hq : 0 < q) {g h : Γ} : q • g ≤ q • h ↔ g ≤ h := by
  have mono : ∀ {p : ℚ}, 0 < p → ∀ {a b : Γ}, a ≤ b → p • a ≤ p • b := fun hp a b hab => by
    have := rat_smul_nonneg hp (sub_nonneg.2 hab)
    rwa [smul_sub, sub_nonneg] at this
  refine ⟨fun hle => ?_, mono hq⟩
  have := mono (inv_pos.2 hq) hle
  rwa [smul_smul, smul_smul, inv_mul_cancel₀ hq.ne', one_smul, one_smul] at this

/-- The dilation `T_r (γ) = r γ` of `thm:dilation`, for a positive rational `r`, as an ordered
additive automorphism of a divisible linearly ordered abelian group (a `ℚ`-module). -/
def dilation (r : ℚ) (hr : 0 < r) : Γ ≃+o Γ where
  toFun g := r • g
  invFun g := r⁻¹ • g
  left_inv g := by simp only [smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
  right_inv g := by simp only [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  map_add' := smul_add r
  map_le_map_iff' := rat_smul_le_smul_iff hr

@[simp]
theorem dilation_apply {r : ℚ} (hr : 0 < r) (g : Γ) : dilation r hr g = r • g := rfl

theorem dilation_symm_apply {r : ℚ} (hr : 0 < r) (g : Γ) : (dilation r hr).symm g = r⁻¹ • g :=
  rfl

/-- `thm:dilation`: for `r ≠ 1` the displacement image `(T_r - id)(Γ)` is all of `Γ`. -/
theorem range_dilation_sub {r : ℚ} (hr : 0 < r) (hr1 : r ≠ 1) :
    Set.range (fun g : Γ => dilation r hr g - g) = Set.univ := by
  refine Set.eq_univ_of_forall fun h => ⟨(r - 1)⁻¹ • h, ?_⟩
  have hr1' : r - 1 ≠ 0 := sub_ne_zero.2 hr1
  calc dilation r hr ((r - 1)⁻¹ • h) - (r - 1)⁻¹ • h = (r - 1) • ((r - 1)⁻¹ • h) := by
        rw [dilation_apply, sub_smul, one_smul]
    _ = h := by rw [smul_smul, mul_inv_cancel₀ hr1', one_smul]

/-- For `r ≠ 1`, the dilation `T_r` of a nontrivial group is not the identity. -/
theorem dilation_ne_refl [Nontrivial Γ] {r : ℚ} (hr : 0 < r) (hr1 : r ≠ 1) :
    dilation r hr ≠ OrderAddMonoidIso.refl Γ := by
  intro h
  obtain ⟨g, hg⟩ := exists_ne (0 : Γ)
  have h1 : r • g = g := by
    have := congrArg (fun T : Γ ≃+o Γ => T g) h
    simpa using this
  have h2 : (r - 1) • g = 0 := by rw [sub_smul, one_smul, h1, sub_self]
  rcases smul_eq_zero.1 h2 with h3 | h3
  · exact hr1 (sub_eq_zero.1 h3)
  · exact hg h3

end Dilation

/-! ### The multiplicative obstruction -/

section OrderedField

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- `eq:dilation-contradiction`, in any ordered field: if a unital endomorphism `σ` stays within
a fixed distance `B` of `x ↦ r x`, then `r² = r`. The source takes `x = ω` with finite errors;
here `x` is chosen large compared with `B`. -/
theorem mul_self_eq_of_abs_sub_mul_le (σ : F →+* F) {r B : F}
    (h : ∀ x, |σ x - r * x| ≤ B) : r * r = r := by
  by_contra hne
  have hc : 0 < |r * r - r| := abs_pos.2 (sub_ne_zero.2 hne)
  have hB : 0 ≤ B := by simpa using h 0
  set c := |r * r - r| with hc_def
  set K := B + 2 * |r| * B + B * B with hK_def
  have hK : 0 ≤ K := by positivity
  set x := K / c + 1 with hx_def
  have hx1 : 1 ≤ x := by
    have : 0 ≤ K / c := div_nonneg hK hc.le
    linarith
  have hx0 : 0 < x := by linarith
  have hcx : c * x = K + c := by rw [hx_def, mul_add, mul_div_cancel₀ _ hc.ne', mul_one]
  have hf : |σ x * σ x - r * (x * x)| ≤ B := by simpa [map_mul] using h (x * x)
  set e := σ x - r * x with he_def
  have he : |e| ≤ B := h x
  have hσx : σ x = r * x + e := by rw [he_def]; ring
  have key : (r * r - r) * (x * x) = (σ x * σ x - r * (x * x)) - 2 * r * x * e - e * e := by
    rw [hσx]; ring
  have h1 : c * (x * x) ≤ B + 2 * |r| * x * B + B * B := by
    have ha := abs_sub ((σ x * σ x - r * (x * x)) - 2 * r * x * e) (e * e)
    have hb := abs_sub (σ x * σ x - r * (x * x)) (2 * r * x * e)
    have hc' : |2 * r * x * e| = 2 * |r| * x * |e| := by
      rw [abs_mul, abs_mul, abs_mul, abs_two, abs_of_pos hx0]
    have hd : |e * e| = |e| * |e| := abs_mul e e
    have hcxx : c * (x * x) = |(r * r - r) * (x * x)| := by
      rw [abs_mul, abs_of_nonneg (mul_self_nonneg x)]
    rw [hcxx, key]
    have h2 : 2 * |r| * x * |e| ≤ 2 * |r| * x * B :=
      mul_le_mul_of_nonneg_left he (by positivity)
    have h3 : |e| * |e| ≤ B * B := mul_self_le_mul_self (abs_nonneg e) he
    linarith
  have h2 : B + 2 * |r| * x * B + B * B ≤ K * x := by
    have h4 : B ≤ B * x := le_mul_of_one_le_right hB hx1
    have h5 : B * B ≤ B * B * x := le_mul_of_one_le_right (mul_nonneg hB hB) hx1
    rw [hK_def]
    nlinarith
  have h3 : c * (x * x) = (K + c) * x := by rw [← hcx]; ring
  nlinarith [mul_pos hc hx0]

/-- The conclusion of `eq:dilation-contradiction`: for `r ≠ 0`, a unital endomorphism within a
fixed distance of `x ↦ r x` forces `r = 1`. -/
theorem eq_one_of_abs_sub_mul_le (σ : F →+* F) {r B : F} (hr : r ≠ 0)
    (h : ∀ x, |σ x - r * x| ≤ B) : r = 1 :=
  mul_left_cancel₀ hr (by rw [mul_self_eq_of_abs_sub_mul_le σ h, mul_one])

variable {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]

/-- `eq:dilation-error`, generic and division-free: let `E` be an ordered exponential, `w` a
valuation and `σ` a unital endomorphism commuting with `E` whose action on values `τ` satisfies
`n • τ g = m • g` (so `τ` is multiplication by `m / n`). Then the error `σ x - (m / n) x` has
profile `ν (σ x - (m / n) x) = 0`, that is, it lies in the kernel `ker ν` of `ν = w ∘ E`; this
is the generic form of the source's `σ x - r x ∈ 𝒪`. Only torsion-freeness of `Γ` is used, in
place of the source's `ℚ`-linearity of `ν`. -/
theorem profile_sub_mul_eq_zero_of_nsmul (E : OrderedExp F) {w : AddValuation F (WithTop Γ)}
    {σ : F →+* F} (hcomm : ∀ x, σ (E x) = E (σ x)) {τ : Γ → Γ}
    (hτ : ∀ (y : F) (g : Γ), w y = g → w (σ y) = τ g) {m n : ℕ} (hn : n ≠ 0)
    (hdil : ∀ g, n • τ g = m • g) (x : F) :
    profile w E (σ x - (m / n : F) * x) = 0 := by
  have hnF : (n : F) ≠ 0 := Nat.cast_ne_zero.2 hn
  have h1 : n • profile w E (σ x) = m • profile w E x := by
    rw [profile_map_of_commute E hcomm hτ, hdil]
  have h2 : n • profile w E ((m / n : F) * x) = m • profile w E x := by
    rw [← map_nsmul, ← map_nsmul, nsmul_eq_mul, nsmul_eq_mul, ← mul_assoc,
      mul_div_cancel₀ _ hnF]
  apply nsmul_right_injective hn
  change n • profile w E (σ x - (m / n : F) * x) = n • 0
  rw [map_sub, smul_sub, h1, h2, sub_self, smul_zero]

/-- The uniform bound drawn from `eq:dilation-error`: under the hypotheses of
`profile_sub_mul_eq_zero_of_nsmul`, with `w` a nontrivial convex valuation, the error
`σ x - (m / n) x` lies in the proper convex subgroup `ker ν` of `lem:bridge`, hence is bounded
by one `B > 0` for all `x`. The bound `B` may be infinite, so this is weaker than the membership
in `ker ν`, which is `profile_sub_mul_eq_zero_of_nsmul`. -/
theorem exists_abs_sub_lt_of_nsmul (E : OrderedExp F) {w : AddValuation F (WithTop Γ)}
    (hw : IsConvexValuation w) (hnt : ∃ x : F, x ≠ 0 ∧ w x ≠ 0) {σ : F →+* F}
    (hcomm : ∀ x, σ (E x) = E (σ x)) {τ : Γ → Γ}
    (hτ : ∀ (y : F) (g : Γ), w y = g → w (σ y) = τ g) {m n : ℕ} (hn : n ≠ 0)
    (hdil : ∀ g, n • τ g = m • g) :
    ∃ B : F, 0 < B ∧ ∀ x, |σ x - (m / n : F) * x| < B := by
  obtain ⟨B, hB0, hB⟩ := exists_abs_lt_of_ordConnected (ker_profile_ordConnected E hw)
    (ker_profile_ne_top E hw hnt)
  exact ⟨B, hB0, fun x => hB _ (AddMonoidHom.mem_ker.2
    (profile_sub_mul_eq_zero_of_nsmul E hcomm hτ hn hdil x))⟩

/-- `thm:dilation`, non-lifting, generic and division-free: under the hypotheses of
`exists_abs_sub_lt_of_nsmul` with `m, n ≥ 1`, necessarily `m = n`. Thus no unital endomorphism
commuting with `E` acts on values as multiplication by a positive rational other than `1`.
Neither surjectivity of `σ` nor surjectivity of `w` is used. -/
theorem eq_of_nsmul_valueMap (E : OrderedExp F) {w : AddValuation F (WithTop Γ)}
    (hw : IsConvexValuation w) (hnt : ∃ x : F, x ≠ 0 ∧ w x ≠ 0) {σ : F →+* F}
    (hcomm : ∀ x, σ (E x) = E (σ x)) {τ : Γ → Γ}
    (hτ : ∀ (y : F) (g : Γ), w y = g → w (σ y) = τ g) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (hdil : ∀ g, n • τ g = m • g) : m = n := by
  obtain ⟨B, -, hB⟩ := exists_abs_sub_lt_of_nsmul E hw hnt hcomm hτ hn hdil
  have hr : (m / n : F) ≠ 0 := div_ne_zero (Nat.cast_ne_zero.2 hm) (Nat.cast_ne_zero.2 hn)
  have h1 := eq_one_of_abs_sub_mul_le σ hr fun x => (hB x).le
  rw [div_eq_one_iff_eq (Nat.cast_ne_zero.2 hn)] at h1
  exact_mod_cast h1

/-- `thm:dilation`, non-lifting: let `Γ` be a `ℚ`-module, `E` an ordered exponential and `w` a
nontrivial convex valuation into `Γ`. For a positive rational `r ≠ 1`, no unital endomorphism
`σ` commuting with `E` induces `T_r` on values, that is, satisfies `w (σ y) = r • w y`. -/
theorem not_lift_dilation [Module ℚ Γ] (E : OrderedExp F) {w : AddValuation F (WithTop Γ)}
    (hw : IsConvexValuation w) (hnt : ∃ x : F, x ≠ 0 ∧ w x ≠ 0) {r : ℚ} (hr : 0 < r)
    (hr1 : r ≠ 1) :
    ¬ ∃ σ : F →+* F, (∀ x, σ (E x) = E (σ x)) ∧
      ∀ (y : F) (g : Γ), w y = g → w (σ y) = dilation r hr g := by
  rintro ⟨σ, hcomm, hτ⟩
  obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (Rat.num_pos.2 hr).le
  have hk0 : k ≠ 0 := by
    have := Rat.num_pos.2 hr
    omega
  have hdil : ∀ g : Γ, r.den • dilation r hr g = k • g := fun g => by
    rw [dilation_apply, den_nsmul_smul, hk, natCast_zsmul]
  have hkn := eq_of_nsmul_valueMap E hw hnt hcomm hτ hk0 r.den_nz hdil
  apply hr1
  rw [← Rat.num_div_den r, hk, hkn, Int.cast_natCast, div_self (Nat.cast_ne_zero.2 r.den_nz)]

end OrderedField

/-! ### The canonical Hahn lift -/

section HahnLift

variable {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] {R : Type*}

/-- The order embedding `Γ ↪o Γ` underlying an ordered additive automorphism. -/
def orderEmb (T : Γ ≃+o Γ) : Γ ↪o Γ :=
  T.toOrderIso.toOrderEmbedding

omit [IsOrderedAddMonoid Γ] in
@[simp]
theorem orderEmb_apply (T : Γ ≃+o Γ) (g : Γ) : orderEmb T g = T g := rfl

omit [IsOrderedAddMonoid Γ] in
/-- Coefficients of `embDomain` along an automorphism: the coefficient at `g` is the old
coefficient at `T⁻¹ g`. -/
theorem coeff_embDomain_orderEmb [Zero R] (T : Γ ≃+o Γ) (x : HahnSeries Γ R) (g : Γ) :
    (embDomain (orderEmb T) x).coeff g = x.coeff (T.symm g) := by
  obtain ⟨a, rfl⟩ := EquivLike.surjective T g
  rw [OrderAddMonoidIso.symm_apply_apply, ← orderEmb_apply, embDomain_coeff]

variable [Semiring R]

/-- `prop:hahn-lift` (`eq:hahn-lift`): the canonical lift
`T̂ (∑ a_γ t^γ) = ∑ a_γ t^{T γ}` of an ordered additive automorphism `T` of `Γ`, a ring
automorphism of `R((t^Γ))` for any semiring `R`. Its inverse is the lift of `T⁻¹`
(`hahnLift_symm`). -/
noncomputable def hahnLift (T : Γ ≃+o Γ) : HahnSeries Γ R ≃+* HahnSeries Γ R where
  toFun := embDomain (orderEmb T)
  invFun := embDomain (orderEmb T.symm)
  left_inv x := by
    ext g
    rw [coeff_embDomain_orderEmb, coeff_embDomain_orderEmb, OrderAddMonoidIso.symm_symm,
      OrderAddMonoidIso.symm_apply_apply]
  right_inv x := by
    ext g
    rw [coeff_embDomain_orderEmb, coeff_embDomain_orderEmb, OrderAddMonoidIso.symm_symm,
      OrderAddMonoidIso.apply_symm_apply]
  map_mul' := embDomain_mul (orderEmb T) (map_add T)
  map_add' := embDomain_add (orderEmb T)

theorem hahnLift_apply (T : Γ ≃+o Γ) (x : HahnSeries Γ R) :
    hahnLift T x = embDomain (orderEmb T) x := rfl

/-- `eq:hahn-lift`: the coefficient of `T̂ x` at `g` is the coefficient of `x` at `T⁻¹ g`. -/
@[simp]
theorem coeff_hahnLift (T : Γ ≃+o Γ) (x : HahnSeries Γ R) (g : Γ) :
    (hahnLift T x).coeff g = x.coeff (T.symm g) :=
  coeff_embDomain_orderEmb T x g

/-- `eq:hahn-lift`: the coefficient of `t^{T γ}` in `T̂ x` is that of `t^γ` in `x`. -/
theorem coeff_hahnLift_apply (T : Γ ≃+o Γ) (x : HahnSeries Γ R) (g : Γ) :
    (hahnLift T x).coeff (T g) = x.coeff g := by
  rw [coeff_hahnLift, OrderAddMonoidIso.symm_apply_apply]

/-- The inverse of `T̂` is the lift of `T⁻¹`. -/
theorem hahnLift_symm (T : Γ ≃+o Γ) : (hahnLift (R := R) T).symm = hahnLift T.symm := rfl

/-- `T̂` sends the monomial `r t^g` to `r t^{T g}`. -/
theorem hahnLift_single (T : Γ ≃+o Γ) (g : Γ) (r : R) :
    hahnLift T (single g r) = single (T g) r :=
  embDomain_single

/-- `prop:hahn-lift`: `T̂` fixes the constants `R ⊆ R((t^Γ))` pointwise. -/
theorem hahnLift_C (T : Γ ≃+o Γ) (r : R) : hahnLift T (C r) = C r := by
  rw [C_apply, hahnLift_single, map_zero]

/-- The support of `T̂ x` is the image of the support of `x`. -/
theorem support_hahnLift (T : Γ ≃+o Γ) (x : HahnSeries Γ R) :
    (hahnLift T x).support = T '' x.support := by
  ext g
  constructor
  · intro hg
    refine ⟨T.symm g, ?_, OrderAddMonoidIso.apply_symm_apply T g⟩
    rwa [mem_support, ← coeff_hahnLift]
  · rintro ⟨a, ha, rfl⟩
    rwa [mem_support, coeff_hahnLift_apply]

/-- `prop:hahn-lift`: `T̂` induces `T` on the natural value group, `v (T̂ x) = T (v x)` for the
valuation `v = orderTop` (with `v 0 = ⊤`). -/
theorem orderTop_hahnLift (T : Γ ≃+o Γ) (x : HahnSeries Γ R) :
    (hahnLift T x).orderTop = WithTop.map T x.orderTop :=
  orderTop_embDomain

/-- `T̂` preserves leading coefficients. -/
theorem leadingCoeff_hahnLift (T : Γ ≃+o Γ) (x : HahnSeries Γ R) :
    (hahnLift T x).leadingCoeff = x.leadingCoeff := by
  simp only [_root_.HahnSeries.leadingCoeff]
  rw [orderTop_hahnLift]
  generalize x.orderTop = o
  induction o using WithTop.recTopCoe with
  | top => rfl
  | coe g =>
    simp only [WithTop.map_coe, WithTop.recTopCoe_coe]
    exact coeff_hahnLift_apply T x g

/-- `prop:hahn-lift`: `T̂` preserves the lexicographic order of `R((t^Γ))`. -/
theorem hahnLift_le_iff [PartialOrder R] (T : Γ ≃+o Γ) {x y : HahnSeries Γ R} :
    toLex (hahnLift T x) ≤ toLex (hahnLift T y) ↔ toLex x ≤ toLex y :=
  (embDomainOrderEmbedding (orderEmb T)).le_iff_le

/-- `prop:hahn-lift`: `T̂` as an ordered ring automorphism of the lexicographically ordered Hahn
series ring; for a linearly ordered field `R` it is an ordered field automorphism. -/
noncomputable def hahnLiftOrderRingIso [PartialOrder R] (T : Γ ≃+o Γ) :
    Lex (HahnSeries Γ R) ≃+*o Lex (HahnSeries Γ R) where
  toFun x := toLex (hahnLift T (ofLex x))
  invFun x := toLex (hahnLift T.symm (ofLex x))
  left_inv x := by
    dsimp only
    rw [ofLex_toLex, ← hahnLift_symm, RingEquiv.symm_apply_apply, toLex_ofLex]
  right_inv x := by
    dsimp only
    rw [ofLex_toLex, ← hahnLift_symm, RingEquiv.apply_symm_apply, toLex_ofLex]
  map_mul' x y := by rw [ofLex_mul, map_mul, toLex_mul]
  map_add' x y := by rw [ofLex_add, map_add, toLex_add]
  map_le_map_iff' {x y} := hahnLift_le_iff T (x := ofLex x) (y := ofLex y)

theorem hahnLiftOrderRingIso_apply [PartialOrder R] (T : Γ ≃+o Γ) (x : Lex (HahnSeries Γ R)) :
    hahnLiftOrderRingIso T x = toLex (hahnLift T (ofLex x)) := rfl

variable {α : Type*}

/-- The image `(T̂ (s a))_a` of a summable family; `prop:hahn-lift` says it is summable. -/
noncomputable def liftFamily (T : Γ ≃+o Γ) (s : SummableFamily Γ R α) :
    SummableFamily Γ R α where
  toFun a := hahnLift T (s a)
  isPWO_iUnion_support' := by
    refine (s.isPWO_iUnion_support.image_of_monotone (orderEmb T).monotone).mono ?_
    intro g hg
    obtain ⟨a, ha⟩ := Set.mem_iUnion.1 hg
    refine ⟨T.symm g, Set.mem_iUnion.2 ⟨a, ?_⟩, ?_⟩
    · rwa [mem_support, ← coeff_hahnLift]
    · simp
  finite_co_support' g := by
    have h : {a | (s a).coeff (T.symm g) ≠ 0}.Finite := s.finite_co_support' (T.symm g)
    simpa only [coeff_hahnLift] using h

@[simp]
theorem liftFamily_apply (T : Γ ≃+o Γ) (s : SummableFamily Γ R α) (a : α) :
    liftFamily T s a = hahnLift T (s a) := rfl

/-- `prop:hahn-lift`: `T̂` preserves every summable Hahn family and commutes with its sum,
`∑ T̂ (s a) = T̂ (∑ s a)`. -/
theorem hsum_liftFamily (T : Γ ≃+o Γ) (s : SummableFamily Γ R α) :
    (liftFamily T s).hsum = hahnLift T s.hsum := by
  ext g
  simp only [SummableFamily.coeff_hsum, liftFamily_apply, coeff_hahnLift]

/-- `prop:hahn-lift`, bundled: for an ordered additive automorphism `T` of `Γ` and a partially
ordered semiring `R`, the ring automorphism `T̂` of `R((t^Γ))` fixes the constants, induces `T`
on values (`orderTop`), preserves leading coefficients and the lexicographic order, has inverse
`T⁻¹`-hat, and sends every summable family indexed by `α` to a summable family with sum
`T̂ (∑ s a)`. -/
theorem hahn_lift [PartialOrder R] (T : Γ ≃+o Γ) (α : Type*) :
    (∀ r : R, hahnLift T (C r) = C r) ∧
      (∀ x : HahnSeries Γ R, (hahnLift T x).orderTop = WithTop.map T x.orderTop ∧
        (hahnLift T x).leadingCoeff = x.leadingCoeff) ∧
      (∀ x y : HahnSeries Γ R,
        toLex (hahnLift T x) ≤ toLex (hahnLift T y) ↔ toLex x ≤ toLex y) ∧
      (hahnLift (R := R) T).symm = hahnLift T.symm ∧
      ∀ s : SummableFamily Γ R α, (liftFamily T s).hsum = hahnLift T s.hsum :=
  ⟨hahnLift_C T, fun x => ⟨orderTop_hahnLift T x, leadingCoeff_hahnLift T x⟩,
    fun _ _ => hahnLift_le_iff T, hahnLift_symm T, hsum_liftFamily T⟩

end HahnLift

/-! ### `thm:dilation`, bundled -/

section DilationTheorem

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
  {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] [Module ℚ Γ]

/-- `thm:dilation`: let `Γ` be a divisible linearly ordered abelian group (a `ℚ`-module), `r` a
positive rational with `r ≠ 1`, and `T_r = dilation r hr` (an ordered additive automorphism of
`Γ` by construction). Then `(T_r - id)(Γ) = Γ`; `T_r` has the canonical lift `T̂_r`
(`eq:hahn-lift`) to every Hahn series ring `R((t^Γ))`, which induces `T_r` on values; and yet,
for every ordered field `F` with an ordered exponential `E` and a nontrivial convex valuation
`w` into `Γ`, no unital endomorphism of `F` commuting with `E` induces `T_r` on values. -/
theorem dilation_theorem (R : Type*) [Semiring R] (E : OrderedExp F)
    {w : AddValuation F (WithTop Γ)} (hw : IsConvexValuation w)
    (hnt : ∃ x : F, x ≠ 0 ∧ w x ≠ 0) {r : ℚ} (hr : 0 < r) (hr1 : r ≠ 1) :
    Set.range (fun g : Γ => dilation r hr g - g) = Set.univ ∧
      (∀ x : HahnSeries Γ R,
        (hahnLift (dilation r hr) x).orderTop = WithTop.map (dilation r hr) x.orderTop) ∧
      ¬ ∃ σ : F →+* F, (∀ x, σ (E x) = E (σ x)) ∧
        ∀ (y : F) (g : Γ), w y = g → w (σ y) = dilation r hr g :=
  ⟨range_dilation_sub hr hr1, orderTop_hahnLift (dilation r hr),
    not_lift_dilation E hw hnt hr hr1⟩

end DilationTheorem

/-! ### The value group `(No, +, <)` of the actual surreals -/

section Surreals

universe u

open Surreal.Foundations

/-- `thm:dilation`, value-group clauses at `Γ = (No, +, <)`, the additive group of the actual
surreal field `SignSequence`: for a positive rational `r ≠ 1`, `T_r (γ) = r γ` is a nonidentity
ordered additive automorphism of `No` whose displacement image is all of `No`. -/
theorem surreal_dilation {r : ℚ} (hr : 0 < r) (hr1 : r ≠ 1) :
    (∀ g : SignSequence.{u}, dilation r hr g = (r : SignSequence.{u}) * g) ∧
      dilation (Γ := SignSequence.{u}) r hr ≠ OrderAddMonoidIso.refl _ ∧
      Set.range (fun g : SignSequence.{u} => dilation r hr g - g) = Set.univ :=
  ⟨fun g => by rw [dilation_apply, Rat.smul_def], dilation_ne_refl hr hr1,
    range_dilation_sub hr hr1⟩

/-- The natural valuation `SignSequence.valuation` of the actual surreals is convex. -/
theorem isConvexValuation_signSequence :
    IsConvexValuation (SignSequence.valuation.{u}) :=
  fun _ _ hx hxy => SignSequence.valuation_antitone_nonneg hx.le hxy

/-- The natural valuation of the actual surreals is nontrivial: `v (ω) = -1 ≠ 0`. -/
theorem exists_valuation_ne_zero_signSequence :
    ∃ x : SignSequence.{u}, x ≠ 0 ∧ SignSequence.valuation x ≠ 0 :=
  ⟨SignSequence.omegaPower 1, SignSequence.omegaPower_ne_zero 1, by
    rw [SignSequence.valuation_omegaPower]
    exact WithTop.coe_ne_zero.2 (neg_ne_zero.2 one_ne_zero)⟩

/-- `thm:dilation`, non-lifting clause at `No`, conditional on the exponential: for any ordered
exponential `E` on the actual surreal field `SignSequence` (supplied as a hypothesis) and a
positive rational `r ≠ 1`, no unital endomorphism `σ` of `SignSequence` commuting with `E`
induces `T_r` on the natural valuation, that is, satisfies `v (σ y) = r • v y` for `y ≠ 0`. -/
theorem surreal_not_lift_dilation (E : OrderedExp SignSequence.{u}) {r : ℚ} (hr : 0 < r)
    (hr1 : r ≠ 1) :
    ¬ ∃ σ : SignSequence.{u} →+* SignSequence.{u}, (∀ x, σ (E x) = E (σ x)) ∧
      ∀ (y : SignSequence.{u}) (g : SignSequence.{u}),
        SignSequence.valuation y = g → SignSequence.valuation (σ y) = dilation r hr g :=
  not_lift_dilation E isConvexValuation_signSequence exists_valuation_ne_zero_signSequence hr
    hr1

end Surreals

/-! ### A bounded additive automorphism of the Laurent field -/

section AdditiveBounded

variable {R : Type*} [CommRing R]

/-- The nilpotent operator `N f = [t¹]f · t²` of `prop:additive-bounded` on `R((t))`. -/
noncomputable def nilShift (f : HahnSeries ℤ R) : HahnSeries ℤ R :=
  single 2 (f.coeff 1)

theorem nilShift_add (f g : HahnSeries ℤ R) : nilShift (f + g) = nilShift f + nilShift g := by
  rw [nilShift, nilShift, nilShift, coeff_add, single_add]

theorem nilShift_sub (f g : HahnSeries ℤ R) : nilShift (f - g) = nilShift f - nilShift g := by
  rw [nilShift, nilShift, nilShift, coeff_sub, single_sub]

/-- `N` is `R`-linear. -/
theorem nilShift_smul (c : R) (f : HahnSeries ℤ R) : nilShift (c • f) = c • nilShift f := by
  ext n
  simp only [nilShift, coeff_smul, coeff_single]
  split_ifs <;> simp

/-- `N² = 0`, since the coefficient of `t` in `N f` vanishes. -/
theorem nilShift_nilShift (f : HahnSeries ℤ R) : nilShift (nilShift f) = 0 := by
  rw [nilShift, nilShift, coeff_single_of_ne (by decide), single_eq_zero]

/-- `f + N f` has the same order as `f`. -/
theorem orderTop_add_nilShift (f : HahnSeries ℤ R) :
    (f + nilShift f).orderTop = f.orderTop := by
  by_cases h : f.coeff 1 = 0
  · rw [nilShift, h, single_eq_zero, add_zero]
  · refine orderTop_add_eq_left ?_
    rw [nilShift, orderTop_single h]
    exact (orderTop_le_of_coeff_ne_zero h).trans_lt (WithTop.coe_lt_coe.2 (by norm_num))

/-- `f + N f` has the same leading coefficient as `f`. -/
theorem leadingCoeff_add_nilShift (f : HahnSeries ℤ R) :
    (f + nilShift f).leadingCoeff = f.leadingCoeff := by
  by_cases h : f.coeff 1 = 0
  · rw [nilShift, h, single_eq_zero, add_zero]
  · refine _root_.HahnSeries.leadingCoeff_add_eq_left ?_
    rw [nilShift, orderTop_single h]
    exact (orderTop_le_of_coeff_ne_zero h).trans_lt (WithTop.coe_lt_coe.2 (by norm_num))

/-- The map `T = id + N` on `L = R((t))`, with the lexicographic order of `Lex R((t))`. -/
noncomputable def shiftFun (f : Lex (HahnSeries ℤ R)) : Lex (HahnSeries ℤ R) :=
  f + toLex (nilShift (ofLex f))

theorem ofLex_shiftFun (f : Lex (HahnSeries ℤ R)) :
    ofLex (shiftFun f) = ofLex f + nilShift (ofLex f) := by
  rw [shiftFun, ofLex_add, ofLex_toLex]

theorem shiftFun_add (f g : Lex (HahnSeries ℤ R)) :
    shiftFun (f + g) = shiftFun f + shiftFun g := by
  simp only [shiftFun, ofLex_add, nilShift_add, toLex_add]
  abel

theorem shiftFun_sub (f g : Lex (HahnSeries ℤ R)) :
    shiftFun (f - g) = shiftFun f - shiftFun g := by
  simp only [shiftFun, ofLex_sub, nilShift_sub, toLex_sub]
  abel

variable [LinearOrder R] [IsStrictOrderedRing R]

omit [IsStrictOrderedRing R] in
/-- `T` preserves signs, since it preserves leading coefficients. -/
theorem shiftFun_nonneg_iff (f : Lex (HahnSeries ℤ R)) : 0 ≤ shiftFun f ↔ 0 ≤ f := by
  rw [← _root_.HahnSeries.leadingCoeff_nonneg_iff,
    ← _root_.HahnSeries.leadingCoeff_nonneg_iff (x := f), ofLex_shiftFun,
    leadingCoeff_add_nilShift]

theorem shiftFun_le_iff {f g : Lex (HahnSeries ℤ R)} : shiftFun f ≤ shiftFun g ↔ f ≤ g := by
  rw [← sub_nonneg, ← shiftFun_sub, shiftFun_nonneg_iff, sub_nonneg]

/-- `prop:additive-bounded`: the map `T = id + N`, `N f = [t¹]f · t²`, as an order-preserving
additive automorphism of `L = R((t))` (lexicographically ordered, so that `t > 0` is
infinitesimal); its inverse is `id - N`. The source takes `R = ℝ`. -/
noncomputable def addShift : Lex (HahnSeries ℤ R) ≃+o Lex (HahnSeries ℤ R) where
  toFun := shiftFun
  invFun f := f - toLex (nilShift (ofLex f))
  left_inv f := by
    simp only [shiftFun, ofLex_add, ofLex_toLex, nilShift_add, nilShift_nilShift, add_zero,
      add_sub_cancel_right]
  right_inv f := by
    simp only [shiftFun, ofLex_sub, ofLex_toLex, nilShift_sub, nilShift_nilShift, sub_zero,
      sub_add_cancel]
  map_add' := shiftFun_add
  map_le_map_iff' := shiftFun_le_iff

theorem addShift_apply (f : Lex (HahnSeries ℤ R)) :
    addShift f = f + toLex (nilShift (ofLex f)) := rfl

/-- `prop:additive-bounded`: `T` fixes `1`. -/
theorem addShift_one : addShift (1 : Lex (HahnSeries ℤ R)) = 1 := by
  rw [addShift_apply, ofLex_one, nilShift, coeff_one, if_neg one_ne_zero, single_eq_zero,
    toLex_zero, add_zero]

/-- `prop:additive-bounded`: `T` fixes the order of every element. -/
theorem orderTop_addShift (f : Lex (HahnSeries ℤ R)) :
    (ofLex (addShift f)).orderTop = (ofLex f).orderTop := by
  rw [addShift_apply, ofLex_add, ofLex_toLex, orderTop_add_nilShift]

/-- `prop:additive-bounded`: `T` fixes the leading coefficient of every element; with
`orderTop_addShift`, it fixes the leading term of every nonzero element. -/
theorem leadingCoeff_addShift (f : Lex (HahnSeries ℤ R)) :
    (ofLex (addShift f)).leadingCoeff = (ofLex f).leadingCoeff := by
  rw [addShift_apply, ofLex_add, ofLex_toLex, leadingCoeff_add_nilShift]

/-- `t = t¹` is positive. -/
theorem single_one_pos : 0 < toLex (single (1 : ℤ) (1 : R)) := by
  rw [← _root_.HahnSeries.leadingCoeff_pos_iff, ofLex_toLex, leadingCoeff_of_single]
  exact one_pos

/-- `t` is infinitesimal: `t < c` for every positive constant `c`. -/
theorem single_one_lt_C {c : R} (hc : 0 < c) :
    toLex (single (1 : ℤ) (1 : R)) < toLex (C c) := by
  have hC : 0 < toLex (C c : HahnSeries ℤ R) := by
    rw [← _root_.HahnSeries.leadingCoeff_pos_iff, ofLex_toLex, C_apply, leadingCoeff_of_single]
    exact hc
  have h := abs_lt_abs_of_orderTop_ofLex (x := toLex (single (1 : ℤ) (1 : R)))
    (y := toLex (C c)) (by
      rw [ofLex_toLex, ofLex_toLex, C_apply, orderTop_single hc.ne',
        orderTop_single one_ne_zero]
      exact WithTop.coe_lt_coe.2 one_pos)
  rwa [abs_of_pos single_one_pos, abs_of_pos hC] at h

/-- `prop:additive-bounded`: the displacement of `T` is uniformly bounded, `|T f - f| < t`. -/
theorem abs_addShift_sub_lt (f : Lex (HahnSeries ℤ R)) :
    |addShift f - f| < toLex (single (1 : ℤ) (1 : R)) := by
  calc |addShift f - f| < |toLex (single (1 : ℤ) (1 : R))| := by
        rw [addShift_apply, add_sub_cancel_left]
        apply abs_lt_abs_of_orderTop_ofLex
        rw [ofLex_toLex, ofLex_toLex, orderTop_single one_ne_zero, nilShift]
        exact (WithTop.coe_lt_coe.2 (by norm_num : (1 : ℤ) < 2)).trans_le orderTop_single_le
    _ = toLex (single (1 : ℤ) (1 : R)) := abs_of_pos single_one_pos

/-- `T t = t + t²`. -/
theorem addShift_single_one :
    addShift (toLex (single (1 : ℤ) (1 : R))) = toLex (single 1 1 + single 2 1) := by
  rw [addShift_apply, ofLex_toLex, nilShift, coeff_single_same, toLex_add]

/-- `T t² = t²`. -/
theorem addShift_single_two :
    addShift (toLex (single (2 : ℤ) (1 : R))) = toLex (single 2 1) := by
  rw [addShift_apply, ofLex_toLex, nilShift, coeff_single_of_ne (by decide), single_eq_zero,
    toLex_zero, add_zero]

/-- `prop:additive-bounded`: `T` is not the identity, since `T t = t + t²`. -/
theorem addShift_ne_refl : addShift (R := R) ≠ OrderAddMonoidIso.refl _ := by
  intro h
  have h1 := congrArg (fun T : Lex (HahnSeries ℤ R) ≃+o Lex (HahnSeries ℤ R) =>
    (ofLex (T (toLex (single (1 : ℤ) (1 : R))))).coeff 2) h
  simp only [addShift_single_one, ofLex_toLex, coeff_add, coeff_single_same,
    coeff_single_of_ne (show (2 : ℤ) ≠ 1 by decide), OrderAddMonoidIso.coe_refl, id] at h1
  norm_num at h1

/-- `prop:additive-bounded`: `T` is not multiplicative, `T (t²) = t² ≠ (t + t²)² = T(t)²`. -/
theorem addShift_single_two_ne :
    addShift (toLex (single (2 : ℤ) (1 : R))) ≠
      addShift (toLex (single 1 1)) * addShift (toLex (single 1 1)) := by
  rw [addShift_single_two, addShift_single_one, ← toLex_mul]
  intro h
  have h3 := congrArg (fun x => (ofLex x).coeff (3 : ℤ)) h
  simp only [ofLex_toLex, add_mul, mul_add, single_mul_single, coeff_add, coeff_single] at h3
  norm_num at h3

/-- `prop:additive-bounded`: `T` is not multiplicative. -/
theorem addShift_not_map_mul :
    ¬ ∀ x y : Lex (HahnSeries ℤ R), addShift (x * y) = addShift x * addShift y := by
  intro h
  apply addShift_single_two_ne (R := R)
  rw [← h, ← toLex_mul, single_mul_single, one_mul]
  norm_num

/-- `prop:additive-bounded`, bundled: `T = id + N` is a nonidentity order-preserving additive
automorphism of `L = R((t))` that fixes `1` and the order and leading coefficient of every
element, with `|T f - f| < t` for all `f`, and it is not multiplicative. -/
theorem additive_bounded :
    addShift (R := R) ≠ OrderAddMonoidIso.refl _ ∧ addShift (1 : Lex (HahnSeries ℤ R)) = 1 ∧
      (∀ f : Lex (HahnSeries ℤ R), (ofLex (addShift f)).orderTop = (ofLex f).orderTop ∧
        (ofLex (addShift f)).leadingCoeff = (ofLex f).leadingCoeff) ∧
      (∀ f : Lex (HahnSeries ℤ R), |addShift f - f| < toLex (single (1 : ℤ) (1 : R))) ∧
      ¬ ∀ x y : Lex (HahnSeries ℤ R), addShift (x * y) = addShift x * addShift y :=
  ⟨addShift_ne_refl, addShift_one, fun f => ⟨orderTop_addShift f, leadingCoeff_addShift f⟩,
    abs_addShift_sub_lt, addShift_not_map_mul⟩

/-- `prop:additive-bounded` for the source's field `L = ℝ((t))`. -/
theorem additive_bounded_real :
    addShift (R := ℝ) ≠ OrderAddMonoidIso.refl _ ∧ addShift (1 : Lex (HahnSeries ℤ ℝ)) = 1 ∧
      (∀ f : Lex (HahnSeries ℤ ℝ), (ofLex (addShift f)).orderTop = (ofLex f).orderTop ∧
        (ofLex (addShift f)).leadingCoeff = (ofLex f).leadingCoeff) ∧
      (∀ f : Lex (HahnSeries ℤ ℝ), |addShift f - f| < toLex (single (1 : ℤ) (1 : ℝ))) ∧
      ¬ ∀ x y : Lex (HahnSeries ℤ ℝ), addShift (x * y) = addShift x * addShift y :=
  additive_bounded

end AdditiveBounded

/-! ### A contracting derivation of the Laurent field -/

section LaurentDerivation

variable {R : Type*} [Field R]

/-- `eq:laurent-derivation`: the derivation `∂ = t² d/dt = t · (t d/dt)` of `R((t))`, written as
`t` times the Euler derivation `t d/dt`. -/
noncomputable def laurentDer : Derivation R (HahnSeries ℤ R) (HahnSeries ℤ R) :=
  single (1 : ℤ) (1 : R) • Surreal.EulerDerivation.euler (Int.castAddHom R)

theorem laurentDer_apply (f : HahnSeries ℤ R) :
    laurentDer f =
      single (1 : ℤ) (1 : R) * Surreal.EulerDerivation.euler (Int.castAddHom R) f := by
  rw [laurentDer, Derivation.smul_apply, smul_eq_mul]

/-- `eq:laurent-derivation`: `∂ (∑ a_n t^n) = ∑ n a_n t^{n+1}`, coefficientwise. -/
theorem coeff_laurentDer (f : HahnSeries ℤ R) (n : ℤ) :
    (laurentDer f).coeff (n + 1) = n * f.coeff n := by
  rw [laurentDer_apply, coeff_single_mul_add, one_mul, Surreal.EulerDerivation.coeff_euler,
    Int.coe_castAddHom]

/-- `eq:laurent-derivation` on monomials: `∂ (a t^n) = n a t^{n+1}`. -/
theorem laurentDer_single (n : ℤ) (a : R) :
    laurentDer (single n a) = single (n + 1) (n * a) := by
  rw [laurentDer_apply, Surreal.EulerDerivation.euler_single, single_mul_single, one_mul,
    add_comm, Int.coe_castAddHom]

/-- `∂` is a nonzero derivation: `∂ t = t²`. -/
theorem laurentDer_ne_zero : laurentDer (R := R) ≠ 0 := by
  intro h
  have h1 := congrArg (fun D : Derivation R (HahnSeries ℤ R) (HahnSeries ℤ R) =>
    (D (single (1 : ℤ) (1 : R))).coeff 2) h
  simp only [laurentDer_single, Derivation.zero_apply, coeff_zero] at h1
  norm_num at h1

/-- `eq:laurent-contraction`: `v_t (∂ f) ≥ v_t f + 1` for every `f` (for `f = 0` both sides are
`⊤`), with `v_t = addVal ℤ R` the `t`-adic valuation. -/
theorem addVal_add_one_le (f : HahnSeries ℤ R) :
    addVal ℤ R f + ((1 : ℤ) : WithTop ℤ) ≤ addVal ℤ R (laurentDer f) := by
  rw [laurentDer_apply, (addVal ℤ R).map_mul, addVal_apply, addVal_apply, addVal_apply,
    orderTop_single one_ne_zero, add_comm (((1 : ℤ) : WithTop ℤ))]
  exact add_le_add (Surreal.EulerDerivation.orderTop_le_orderTop_euler _ f) le_rfl

/-- The consequence of `eq:laurent-contraction` drawn after `eq:laurent-derivation` from
`thm:derivation-valued`: no map `E : L → L^×` satisfies `∂ (E x) = E x ∂ x` for every
`x ∈ L`. -/
theorem not_exists_compatible_exp :
    ¬ ∃ E : HahnSeries ℤ R → HahnSeries ℤ R,
      (∀ x, E x ≠ 0) ∧ ∀ x, laurentDer (E x) = E x * laurentDer x := by
  rintro ⟨E, hE0, hcomp⟩
  have hsurj : ∀ γ : ℤ, ∃ x : HahnSeries ℤ R, addVal ℤ R x = γ := fun γ =>
    ⟨single γ 1, by rw [addVal_apply, orderTop_single one_ne_zero]⟩
  have hnt : ∃ x : HahnSeries ℤ R, x ≠ 0 ∧ addVal ℤ R x ≠ 0 :=
    ⟨single 1 1, single_ne_zero one_ne_zero, by
      rw [addVal_apply, orderTop_single one_ne_zero]
      exact WithTop.coe_ne_zero.2 one_ne_zero⟩
  exact laurentDer_ne_zero (Surreal.SigmaDerivation.derivation_eq_zero_of_loss (addVal ℤ R)
    hsurj hnt laurentDer hE0 hcomp fun y _ => addVal_add_one_le y)

end LaurentDerivation

end Surreal.ValueGroupLifts
