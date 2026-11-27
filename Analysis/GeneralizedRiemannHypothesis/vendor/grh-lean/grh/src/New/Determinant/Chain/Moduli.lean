import New.Determinant.AuxiliaryForms.GridPaths
import New.OneLift.ComparisonOperator.ExchangeData
import New.OneLift.HeckeValues.TwistedRatio

/-!
# Ratios of Hecke values and heights of functions of the twist

This file treats functions of an `m`-fold twist `ϑ` with modulus Q. Here `ϖ` generates the product
of the chosen places, and `D.twistModulus ϑ e` is the modulus `ϖ ^ e Q`, with exponent e at the
chosen places and 1 at the places of Q. It defines the ratios of Hecke values and the absolute
value of a function of the twist up to a constant and a power of the norm of Q. Heights are
stated with `New.HeightLe c y`: the family y, indexed by the ι : ℂ ≅ ℚ̄_l, has height at most c.

## Main definitions and results

* `New.Data.lRatioProd`, `New.Data.HasAbsUpToNormPower`: ratios of Hecke values, and the absolute
  value of a function of the twist up to a constant and a power of the norm of Q.
* `New.Data.CriticalPair.isTameFor_mul_and_lValueProd_eq`: for a ramified pair with character ν and
  a twist ξ, the character νξ and its inverse are tame, and their products of `L`-values are
  expressed by the ratios of Hecke values.

Notions from other files:
* `New.Data.MFoldTwist`: a twist ϑ whose tame part has ψ_wⁿ non-trivial for all w in Q and
  1 ≤ n ≤ m.
* `New.Data.CriticalPair`: an integer 1 ≤ z ≤ t and a character ν of weight −c, z ≤ c ≤ 4b, with
  tame part supported on the chosen places.
-/

noncomputable section

namespace New.Data

open Finset Fintype Exchange Rows Modulus MulChar

variable {P : Parameters} {D : Data P} {c c' : D.MFoldTwist → ℂ}

/-- The residue ring of the modulus ϖ^e·Q attached to ϑ, with (ϖ) the product of the chosen places,
has order (∏ N w)^e · ∏_{w ∈ Q} N w, the first product running over the chosen places w. -/
lemma card_residueRing_twistModulus (e : ℕ) (ϑ : D.TameChar) :
    Fintype.card (D.twistModulus ϑ e).ResidueRing =
      (∏ i : (i : Fin 2) × D.ChosenPlace i, (D.chosenPlace i).q) ^ e * ϑ.normQ := by
  -- the places of `Q` in `D.levelPlaces ϑ` are the elements of `ϑ.Q`
  have h_twist :
      ∏ i : (D.levelPlaces ϑ).TwistIndex, ((D.levelPlaces ϑ).twistPlace i).q = ϑ.normQ :=
    prod_coe_sort ϑ.Q FinPlace.q
  rw [LevelPlaces.card_levelModulus_residueRing, h_twist]
  rfl

section Moduli

variable {f f' : D.MFoldTwist → ℝ}

variable (D) in
/-- The product over `1 ≤ z ≤ s` of the ratios `|L^{MQ}(z, (ν ϑ)⁻¹) / L^M(z, ν⁻¹)|` of Hecke values,
where `L^M` omits the chosen places and their conjugates, and `L^{MQ}` also the places of the
modulus `Q` of `ϑ` and their conjugates. -/
noncomputable def lRatioProd (ν : AutChar D.E) (s : ℕ) (ϑ : D.TameChar) : ℝ :=
  ∏ z ∈ Icc 1 s, ‖(ν * ϑ.toAutChar)⁻¹.L ({w : FinPlace D.E | D.IsChosen w} ∪ ϑ.Q) z‖ /
    ‖ν⁻¹.L {w : FinPlace D.E | D.IsChosen w} z‖

/-- The character `ν` of a pair and its inverse have the same `L`-function away from the chosen
places and their conjugates. -/
lemma CriticalPair.L_inv (p : D.CriticalPair) :
    p.character⁻¹.L {w : FinPlace D.E | D.IsChosen w} =
      p.character.L {w : FinPlace D.E | D.IsChosen w} :=
  p.hasWeight.L_inv p.tamePart_eq_one

/-- For the character `ν` of a critical pair and a tame character `ϑ` of modulus `Q`, the character
`ν ϑ` and its inverse have the same `L`-function away from the chosen places, the places of `Q` and
their conjugates. -/
lemma CriticalPair.L_mul_inv (p : D.CriticalPair) (ϑ : D.TameChar) :
    (p.character * ϑ.toAutChar)⁻¹.L ({w : FinPlace D.E | D.IsChosen w} ∪ ϑ.Q) =
      (p.character * ϑ.toAutChar).L ({w : FinPlace D.E | D.IsChosen w} ∪ ϑ.Q) := by
  refine (p.hasWeight.mul ϑ.hasWeight).L_inv fun w hw ↦ ?_
  simp [p.tamePart_eq_one w (fun h ↦ hw (.inl h)), ϑ.tamePart_eq_one w (fun h ↦ hw (.inr h))]

lemma lRatioProd_nonneg (ν : AutChar D.E) (s : ℕ) (ϑ : D.TameChar) : 0 ≤ D.lRatioProd ν s ϑ :=
  prod_nonneg fun _ _ ↦ div_nonneg (norm_nonneg _) (norm_nonneg _)

/-- For a pair `p = (ν, z)`, the number `lRatioProd` is the product over `1 ≤ i ≤ z` of the ratios
`CriticalPair.ratio` `= |L(i, (ν ϑ)⁻¹)| / |L(i, ν⁻¹)|` of the pairs `p.lowerPoint i = (ν, i)`; the
sign argument of `CriticalPair.ratio` has its default value `1`. -/
lemma CriticalPair.ofReal_lRatioProd (p : D.CriticalPair) (ϑ : D.TameChar) :
    (D.lRatioProd p.character p.z ϑ : ℂ) = ∏ z ∈ Icc 1 p.z, (p.lowerPoint z).ratio ϑ := by
  rw [lRatioProd, Complex.ofReal_prod]
  exact prod_congr rfl fun z hz ↦ by simp [CriticalPair.ratio, CriticalPair.lowerPoint,
    mem_Icc.1 hz]

/-- For the character `ν` of a critical pair and a tame character `ϑ` of modulus `Q`, the product
`lRatioProd` of the ratios of Hecke values can be written without inverses, as the product over
`1 ≤ i ≤ s` of `|L^{MQ}(i, ν ϑ) / L^M(i, ν)|`. -/
lemma CriticalPair.lRatioProd_eq_prod_norm_div (p : D.CriticalPair) (s : ℕ) (ϑ : D.TameChar) :
    D.lRatioProd p.character s ϑ =
      ∏ i ∈ Icc 1 s,
        ‖(p.character * ϑ.toAutChar).L ({w : FinPlace D.E | D.IsChosen w} ∪ ϑ.Q) i /
          p.character.L {w : FinPlace D.E | D.IsChosen w} i‖ := by
  simp only [lRatioProd, p.L_mul_inv ϑ, p.L_inv, norm_div]

/-- For a critical pair `p` (a character `ν = p.character` and an integer `z = p.z`) and a tame
character `ϑ` with places `ϑ.Q`, the number `lValueProd` up to `z` for `(ν ϑ)⁻¹` and the chosen
places together with `ϑ.Q` is a product of three factors. They are `lValueProd` for `ν` and the
chosen places, `ϑ.normQ ^ z ^ 2`, and `D.lRatioProd ν z ϑ ^ 2`, the square of the product of ratios
of Hecke L-values. -/
lemma CriticalPair.lValueProd_mul_inv_eq (p : D.CriticalPair) (ϑ : D.TameChar) :
    lValueProd ({w : FinPlace D.E | D.IsChosen w} ∪ ϑ.Q) (p.character * ϑ.toAutChar)⁻¹ p.z =
      lValueProd {w : FinPlace D.E | D.IsChosen w} p.character p.z * (ϑ.normQ : ℝ) ^ p.z ^ 2 *
        D.lRatioProd p.character p.z ϑ ^ 2 := by
  have h_inv : lValueProd {w : FinPlace D.E | D.IsChosen w} p.character⁻¹ p.z =
      lValueProd {w : FinPlace D.E | D.IsChosen w} p.character p.z := by simp [lValueProd, p.L_inv]
  have h_eq :
      (lValueProd ({w : FinPlace D.E | D.IsChosen w} ∪ ϑ.Q) (p.character * ϑ.toAutChar)⁻¹ p.z : ℂ) =
        (ϑ.normQ : ℂ) ^ p.z ^ 2 *
          (lValueProd {w : FinPlace D.E | D.IsChosen w} p.character p.z *
            (D.lRatioProd p.character p.z ϑ : ℂ) ^ 2) := by
    simpa [prod_pow, ← p.ofReal_lRatioProd, h_inv] using p.lValueProd_eq_mul_prod_ratio_sq 1 ϑ
  rw [mul_left_comm, ← mul_assoc] at h_eq
  exact_mod_cast h_eq

/-- At the powers of the trivial twist the product of the ratios of Hecke values is `1`. -/
lemma CriticalPair.lRatioProd_one_pow (p : D.CriticalPair) (n : ℕ) :
    D.lRatioProd p.character p.z ((1 : D.MFoldTwist).pow n) = 1 := by
  refine prod_eq_one fun z hz ↦ ?_
  -- the ratio at the trivial twist is `L / L`, and it is not zero
  have h_ne : p.character⁻¹.L {w : FinPlace D.E | D.IsChosen w} z ≠ 0 := by
    simpa [CriticalPair.ratio, CriticalPair.lowerPoint, mem_Icc.1 hz, TameChar.pow,
      toAutChar_one_and_toTwist_one_and_Q_one]
      using (p.lowerPoint z).ratio_ne_zero ((1 : D.MFoldTwist).pow n) 1
  simp [TameChar.pow, toAutChar_one_and_toTwist_one_and_Q_one, h_ne]

variable (D c f) in
/-- `c` has absolute value `f` up to a norm power: `‖c ϑ‖² = C (Nm Q)ᵏ (f ϑ)²` for all `m`-fold
twists `ϑ`, with `Q` the modulus of `ϑ` and with a real `C` and an integer `k` that do not depend on
`ϑ`. The case `C = 0`, where `c` vanishes for all twists, is allowed. -/
def HasAbsUpToNormPower : Prop :=
  ∃ (C : ℝ) (k : ℤ), ∀ ϑ : D.MFoldTwist, ‖c ϑ‖ ^ 2 = C * (ϑ.normQ : ℝ) ^ k * f ϑ ^ 2

/-- If `c` has absolute value `f` up to a norm power and `c'` has absolute value `f'` up to a norm
power, then `c * c'` has absolute value `f * f'` up to a norm power. -/
lemma HasAbsUpToNormPower.mul (hcf : D.HasAbsUpToNormPower c f)
    (hcf' : D.HasAbsUpToNormPower c' f') : D.HasAbsUpToNormPower (c * c') (f * f') := by
  obtain ⟨C, k, hc⟩ := hcf
  obtain ⟨C', k', hc'⟩ := hcf'
  refine ⟨C * C', k + k', fun ϑ ↦ ?_⟩
  have h_ne : (ϑ.normQ : ℝ) ≠ 0 := by
    simp [prod_eq_zero_iff]
  rw [Pi.mul_apply, Pi.mul_apply, norm_mul, mul_pow, hc, hc', zpow_add₀ h_ne]
  ring

/-- A function of the twist whose squared norm is a constant times a power of the norm of `𝔪 = ϖᵉ Q`
has absolute value `1` up to a norm power. -/
lemma HasAbsUpToNormPower.of_norm_sq_eq_mul_card_zpow (e : ℕ) (C : ℝ) (k : ℤ)
    (hc : ∀ ϑ : D.MFoldTwist, ‖c ϑ‖ ^ 2 = C * card (D.twistModulus ϑ e).ResidueRing ^ k) :
    D.HasAbsUpToNormPower c 1 := by
  refine ⟨C * (((∏ i, (D.chosenPlace i).q) ^ e : ℕ) : ℝ) ^ k, k, fun ϑ ↦ ?_⟩
  simp [hc, card_residueRing_twistModulus, mul_zpow, mul_assoc]

lemma HasAbsUpToNormPower.one : D.HasAbsUpToNormPower 1 1 := ⟨1, 0, by simp⟩

lemma HasAbsUpToNormPower.const (a : ℂ) : D.HasAbsUpToNormPower (fun _ : D.MFoldTwist ↦ a) 1 :=
  ⟨‖a‖ ^ 2, 0, by simp⟩

lemma HasAbsUpToNormPower.inv (h : D.HasAbsUpToNormPower c f) : D.HasAbsUpToNormPower c⁻¹ f⁻¹ := by
  obtain ⟨C, k, hc⟩ := h
  exact ⟨C⁻¹, -k, fun ϑ ↦ by simp [hc, zpow_neg, mul_comm, mul_left_comm]⟩

/-- If each `γ a` has absolute value `F a` up to a norm power, then the product of the `γ a` has as
absolute value up to a norm power the product of the `F a`. -/
lemma HasAbsUpToNormPower.prod {A : Type} {s : Finset A} {γ : A → D.MFoldTwist → ℂ}
    {F : A → D.MFoldTwist → ℝ} (h : ∀ a ∈ s, D.HasAbsUpToNormPower (γ a) (F a)) :
    D.HasAbsUpToNormPower (∏ a ∈ s, γ a) (∏ a ∈ s, F a) := by
  induction s using Finset.cons_induction with
  | empty => simpa using HasAbsUpToNormPower.one
  | cons a s ha ih =>
    simpa only [prod_cons] using
      (h a (mem_cons_self a s)).mul (ih fun b hb ↦ h b (mem_cons_of_mem hb))

/-- Let `c` and `f` be a complex and a real function of the `m`-fold twist `ϑ`, and write
`N(Q) = ϑ.normQ` for the norm of the modulus `Q` of `ϑ`. Suppose `c` has absolute value `f` up to a
norm power, that is `‖c ϑ‖² = C N(Q)ᵏ (f ϑ)²` with `C` and `k` independent of `ϑ`, and that `f ≥ 0`,
`f 1 = 1` and `c 1 ≠ 0` at the trivial twist `1`. Then there is an integer `e` with
`‖c ϑ / c 1‖ = N(Q) ^ (e / 2) * f ϑ` for all `ϑ`. -/
lemma HasAbsUpToNormPower.exists_norm_div_eq {c : D.MFoldTwist → ℂ} {f : D.MFoldTwist → ℝ}
    (h_abs : D.HasAbsUpToNormPower c f) (hf_one : f 1 = 1) (hf : ∀ ϑ : D.MFoldTwist, 0 ≤ f ϑ)
    (hc : c 1 ≠ 0) :
    ∃ e : ℤ, ∀ ϑ : D.MFoldTwist, ‖c ϑ / c 1‖ = (ϑ.normQ : ℝ) ^ (e / 2 : ℝ) * f ϑ := by
  obtain ⟨C, k, h_norm⟩ := h_abs
  have hC : ‖c 1‖ ^ 2 = C := by simp [h_norm, hf_one, toAutChar_one_and_toTwist_one_and_Q_one]
  refine ⟨k, fun ϑ ↦ ?_⟩
  have h_sq : ((ϑ.normQ : ℝ) ^ (k / 2 : ℝ)) ^ 2 = (ϑ.normQ : ℝ) ^ k := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _), Nat.cast_ofNat,
      div_mul_cancel₀ _ two_ne_zero, Real.rpow_intCast]
  refine (pow_left_inj₀ (norm_nonneg _) (mul_nonneg (by positivity) (hf ϑ)) two_ne_zero).1 ?_
  rw [norm_div, div_pow, div_eq_iff (pow_ne_zero 2 (norm_ne_zero_iff.2 hc)), h_norm ϑ, mul_pow,
    h_sq, hC]
  ring

/-- Let `p = (ν, z)` be a critical pair, `e ≠ 0`, and `c` a complex function of the `m`-fold twist
`ϑ`. Write `Q` for the modulus of `ϑ` and `𝔪 = ϖᵉ Q`, with `(ϖ)` the product of the chosen places.
Suppose `‖c ϑ‖²` is a constant `C` times `lValueProd` up to `z` for `(ν ϑⁿ)⁻¹` and the places of
`𝔪`. Then `‖c ϑ‖² = C' N(Q)ᵏ (f ϑ)²` with `C'` and `k` independent of `ϑ`, where `f ϑ` is the
product `lRatioProd` of the ratios of Hecke values at `ϑⁿ`. -/
lemma CriticalPair.hasAbsUpToNormPower_of_norm_sq_eq_lValueProd {c : D.MFoldTwist → ℂ}
    (p : D.CriticalPair) (e : ℕ) [NeZero e] (n : ℕ) {C : ℝ}
    (hc : ∀ ϑ : D.MFoldTwist, ‖c ϑ‖ ^ 2 =
      C * lValueProd (D.twistModulus ϑ e).places (p.character * ϑ.toAutChar ^ n)⁻¹ p.z) :
    D.HasAbsUpToNormPower c fun ϑ : D.MFoldTwist ↦ D.lRatioProd p.character p.z (ϑ.pow n) := by
  refine ⟨C * lValueProd {w | D.IsChosen w} p.character p.z, (p.z ^ 2 : ℕ), fun ϑ ↦ ?_⟩
  have h_prod : lValueProd ({w | D.IsChosen w} ∪ ϑ.Q) (p.character * ϑ.toAutChar ^ n)⁻¹ p.z =
      lValueProd {w | D.IsChosen w} p.character p.z * (ϑ.normQ : ℝ) ^ p.z ^ 2 *
        D.lRatioProd p.character p.z (ϑ.pow n) ^ 2 :=
    p.lValueProd_mul_inv_eq (ϑ.pow n)
  rw [hc, places_twistModulus, h_prod, zpow_natCast]
  ring

variable (D) in
/-- `F` is the product of the ratios of Hecke values of a ramified pair at the `n`-th powers of the
twists, for some `1 ≤ n ≤ m`. -/
def IsRamifiedRatio (F : D.MFoldTwist → ℝ) : Prop :=
  ∃ (p : D.CriticalPair) (n : D.LiftIndex), p.IsRamified ∧
    ∀ ϑ : D.MFoldTwist, F ϑ = D.lRatioProd p.character p.z (ϑ.pow n)

/-- Let `θ ι` be twists with small ratios: their moduli have norm `N ι = (θ ι).normQ` prime to `ℓ`,
and the inverse ratios of L-values of ramified pairs at their powers have height at most the cut-off
`D.x₁`. For `a` in a finite set `s`, let `F a` be a ramified ratio: `F a ϑ` is the product
`lRatioProd` of the ratios of Hecke values of a ramified pair at `ϑⁿ`, for a fixed `1 ≤ n ≤ m`. Then
the family `((N ι) ^ (e / 2) ∏_{a ∈ s} F a (θ ι))⁻¹` has height at most `#s · t · x₁`. -/
theorem HasSmallRatios.heightLe_inv_rpow_mul_prod {A : Type} {s : Finset A}
    {F : A → D.MFoldTwist → ℝ} {θ : PrimePadicIso → D.MFoldTwist}
    (hθ : D.HasSmallRatios θ) (e : ℤ) (hF : ∀ a ∈ s, D.IsRamifiedRatio (F a)) :
    HeightLe (#s * (D.t * D.x₁)) fun ι : PrimePadicIso ↦
      ((((θ ι).normQ : ℝ) ^ (e / 2 : ℝ) * ∏ a ∈ s, F a (θ ι) : ℝ) : ℂ)⁻¹ := by
  -- Each factor is a product of at most `t` ratios, whose inverses have height at most `x₁`.
  have h_factor (a : A) (ha : a ∈ s) :
      HeightLe (D.t * D.x₁) fun ι : PrimePadicIso ↦ ((F a (θ ι) : ℝ) : ℂ)⁻¹ := by
    obtain ⟨p, n, hp, h_eq⟩ := hF a ha
    have h_ratios : HeightLe (∑ _z ∈ Icc 1 p.z, D.x₁)
        (∏ z ∈ Icc 1 p.z,
          fun ι : PrimePadicIso ↦ ((p.lowerPoint z).ratio ((θ ι).powTwist n) 1)⁻¹) :=
      .prod fun z _ ↦ hθ.height_le n (p.lowerPoint z) 1 hp
    refine h_ratios.mono ?_ fun ι ↦ le_of_eq ?_
    · rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
      grw [p.z_mem.2]
    · rw [h_eq, p.ofReal_lRatioProd, Finset.prod_apply, prod_inv_distrib]
      rfl
  have h_prod : HeightLe (#s * (D.t * D.x₁))
      (∏ a ∈ s, fun ι : PrimePadicIso ↦ ((F a (θ ι) : ℝ) : ℂ)⁻¹) :=
    (HeightLe.prod h_factor).mono (by simp) fun _ ↦ le_rfl
  -- The norm of the modulus is prime to the prime of `ι`, so its power does not raise the height.
  refine (h_prod.rpow_mul le_rfl hθ.coprime fun _ ↦ -(e / 2)).mono le_rfl fun ι ↦ le_of_eq ?_
  rw [Rat.cast_neg, Real.rpow_neg (Nat.cast_nonneg _), Complex.ofReal_inv, Finset.prod_apply,
    prod_inv_distrib, ← mul_inv, Complex.ofReal_mul, Complex.ofReal_prod]
  norm_cast

/-- A function `G` of the twist that is a ramified ratio (`IsRamifiedRatio`) is nonnegative at every
`m`-fold twist `ϑ`. -/
lemma IsRamifiedRatio.nonneg {G : D.MFoldTwist → ℝ} (h : D.IsRamifiedRatio G)
    (ϑ : D.MFoldTwist) : 0 ≤ G ϑ := by
  obtain ⟨p, n, -, h_eq⟩ := h
  simpa [h_eq] using lRatioProd_nonneg p.character p.z (ϑ.pow n)

lemma IsRamifiedRatio.apply_one {G : D.MFoldTwist → ℝ} (h : D.IsRamifiedRatio G) : G 1 = 1 := by
  obtain ⟨p, n, -, h_eq⟩ := h
  rw [h_eq, p.lRatioProd_one_pow]

variable (D) in
/-- The pair of the character `ν = (υ ^ (-Δ) χ) ^ n` and the integer `t`. Here
`υ = WeilData.upsilonU1` is the splitting character on the norm-one ideles, `Δ = D.gap`, and
`χ = D.chiM` has weight `0` and tame part `D.chiMLocal`, so `ν` has weight `-n Δ` and tame part
`D.chiMLocal ^ n`. As `D.untwistedLiftChar j = D.chiZero * (υ ^ (-Δ) χ) ^ j`, one has
`ν = D.untwistedLiftChar (i + n) / D.untwistedLiftChar i` for every `i`. -/
noncomputable def quotientPair (n : D.LiftIndex) : D.CriticalPair where
  character := (WeilData.upsilonU1 ^ (-D.gap : ℤ) * D.chiM) ^ n.val
  negWeight (_ : D.Φ) := n.val * D.gap
  tamePart := D.chiMLocal ^ (n.val : ℤ)
  z := D.t
  hasWeight := by
    convert! ((WeilData.hasWeight_upsilonU1_zpow (-D.gap : ℤ)).mul D.chiM_hasWeight).zpow n.val <;>
      simp
  tamePart_eq_one w hw := by simp_all
  z_mem := ⟨D.nat_le_of_hasLogBound, le_rfl⟩
  le_negWeight _ := (D.nat_le_of_hasLogBound : D.t ≤ D.gap).trans (Nat.le_mul_of_pos_left _ n.2.1)
  negWeight_le _ := by
    grw [(Set.mem_Icc.1 n.2).2]
    exact D.le_of_hasLogBound

lemma quotientPair_character (n : D.LiftIndex) (i : ℕ) :
    (D.quotientPair n).character = D.untwistedLiftChar (i + n) / D.untwistedLiftChar i := by
  simp [quotientPair, untwistedLiftChar, pow_add, ← mul_assoc]

/-- The tame part of `quotientPair n` is nontrivial exactly at the chosen places, since
`1 ≤ n ≤ m`. -/
lemma isRamified_quotientPair (n : D.LiftIndex) : (D.quotientPair n).IsRamified := by
  intro w
  exact D.chiMLocal_zpow_ne_one_iff_isChosen (n.val : ℤ) (by grind [n.2]) (by grind [n.2]) w

variable (D) in
/-- The product of the ratios of Hecke values of the character
`D.untwistedLiftChar j / D.untwistedLiftChar i` at the twist `ϑ ^ (j - i)` (truncated subtraction),
over the points `1 ≤ z ≤ t`. The characters `D.untwistedLiftChar j = D.chiZero * (υ ^ (-D.gap) *
D.chiM) ^ j` of U(1)(𝔸), with `υ = WeilData.upsilonU1`, form a geometric progression. -/
noncomputable def quotientRatio (i j : ℕ) (ϑ : D.MFoldTwist) : ℝ :=
  D.lRatioProd (D.untwistedLiftChar j / D.untwistedLiftChar i) D.t (ϑ.pow (j - i))

lemma quotientRatio_add_eq_lRatioProd (n : D.LiftIndex) (i : ℕ) (ϑ : D.MFoldTwist) :
    D.quotientRatio i (i + n) ϑ =
      D.lRatioProd (D.quotientPair n).character (D.quotientPair n).z (ϑ.pow n) := by
  rw [quotientRatio, Nat.add_sub_cancel_left, quotientPair_character n i]
  rfl

/-- For `i < j ≤ m`, `D.quotientRatio i j` is a ramified ratio (`IsRamifiedRatio`), with
`n = j − i`. It is the product of the ratios of Hecke values of
`D.untwistedLiftChar j / D.untwistedLiftChar i` at the powers ϑ^(j − i). -/
lemma isRamifiedRatio_quotientRatio {i j : ℕ} (hij : i < j) (hj : j ≤ D.m) :
    D.IsRamifiedRatio (D.quotientRatio i j) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hij
  let dist : D.LiftIndex := ⟨n + 1, n.succ_pos, by omega⟩
  exact ⟨D.quotientPair dist, dist, isRamified_quotientPair dist,
    quotientRatio_add_eq_lRatioProd dist i⟩

end Moduli

/-- Let ν be tame for the squarefree modulus 𝔪₀ = ϖQ with weight γ and character χ of O_E/𝔪₀: ν has
weight γ and a tame part (ψ_w) that is non-trivial exactly at the w ∣ 𝔪₀, and χ = ∏_{w ∣ 𝔪₀} ψ_w.
Then χ is primitive: for each a ≠ 0 in O_E/𝔪₀ some χ(1 + ca) is neither 0 nor 1. -/
lemma isPrimitiveMulChar_of_isTameFor {ϑ : D.TameChar} {ν : AutChar D.E}
    {γ : NumberField.InfinitePlace D.E → ℤ} {χ : MulChar (D.twistModulus ϑ 1).ResidueRing ℂ}
    (h_tame : IsTameFor (D.twistModulus ϑ 1) ν γ χ) : IsPrimitiveMulChar χ := by
  -- Some residue of `a` is nonzero, say at `w`, and `ψ w x ≠ 1` for some unit `x`. Choose `c` so
  -- that `1 + c * a` is `x` at `w` and `1` at the other places.
  intro a ha
  obtain ⟨-, ψ, -, hψ, hχ⟩ := h_tame
  obtain ⟨w, hw, ha'⟩ : ∃ᵉ (w : FinPlace D.E) (hw : w ∈ (D.twistModulus ϑ 1).places),
      modulusResidue (D.twistModulus ϑ 1) hw a ≠ 0 := by
    -- The modulus is a product of distinct primes: Chinese remainder theorem, for `a` as a
    -- `1 × 1` matrix.
    by_contra! h_zero
    simpa [← Matrix.ext_iff, ha, h_zero] using
      matrix_eq_iff_map_modulusResidue_eq (x := !![a]) (y := 0) (D.levelPlaces ϑ).apart.injective
        (D.levelPlaces ϑ).ideal_levelModulus_one
  obtain ⟨x, hx⟩ : ∃ x : (ResField w)ˣ, ψ w x ≠ 1 := ne_one_iff.1 ((hψ w).2 hw)
  obtain ⟨b, hb⟩ : ∃ b : NumberField.RingOfIntegers D.E,
      modulusResidue (D.twistModulus ϑ 1) hw (Ideal.Quotient.mk (D.twistModulus ϑ 1).ideal b) =
        (x - 1) / modulusResidue (D.twistModulus ϑ 1) hw a :=
    algebraMap_ResField_surjective w ((x - 1) / modulusResidue (D.twistModulus ϑ 1) hw a)
  -- `c` is `b` times the idempotent that is `1` at `w` and `0` elsewhere.
  let c : (D.twistModulus ϑ 1).ResidueRing :=
    Modulus.reduction (D.twistModulus ϑ 1) ⟨idem {w}, idem_mem_Ô {w}⟩ *
      Ideal.Quotient.mk (D.twistModulus ϑ 1).ideal b
  have h_self : modulusResidue (D.twistModulus ϑ 1) hw (1 + c * a) = x := by simp [c, hb, ha']
  have h_other (v : (D.twistModulus ϑ 1).places) (hv : v ≠ ⟨w, hw⟩) :
      modulusResidue (D.twistModulus ϑ 1) v.2 (1 + c * a) = 1 := by
    have h_ne : v.1 ≠ w := fun h ↦ hv (Subtype.ext h)
    simp [c, h_ne]
  have h_apply : χ (1 + c * a) = ψ w x := by
    rw [hχ, charOfTamePart_apply, finprod_eq_single _ (Subtype.mk w hw), h_self]
    intro v hv
    simp [h_other v hv]
  exact ⟨c, by simp [h_apply, apply_eq_zero_iff], by rwa [h_apply]⟩

/-- For a ramified critical pair with character `ν` of weight `-negWeight`, a twist `ξ` of modulus
`Q` and `e ≠ 0`, the character `ν ξ` is tame for `𝔪 = ϖᵉ Q` with weight `-negWeight`: its tame part
`ψ = p.tamePart * ξ.tamePart` is non-trivial exactly at the places of `𝔪`, and its character on
`O_E / 𝔪` is `charOfTamePart 𝔪 ψ = ∏_{w ∣ 𝔪} ψ_w`. -/
lemma CriticalPair.isTameFor_mul (p : D.CriticalPair) (hp : p.IsRamified) (ξ : D.Twist) (e : ℕ)
    [NeZero e] :
    IsTameFor (D.twistModulus ξ.toTameChar e) (p.character * ξ.toAutChar)
      (fun τ : NumberField.InfinitePlace D.E ↦ -p.negWeight τ)
      (charOfTamePart (D.twistModulus ξ.toTameChar e) (p.tamePart * ξ.tamePart)) := by
  exact isTameFor_of_hasWeight ξ (by simpa using p.hasWeight.mul ξ.hasWeight) hp

/-- For a ramified critical pair with character `ν` of weight `-negWeight`, a twist `ξ` of modulus
`Q` and `e ≠ 0`, the character `(ν ξ)⁻¹` is tame for `𝔪 = ϖᵉ Q` with weight `negWeight`. -/
lemma CriticalPair.isTameFor_mul_inv (p : D.CriticalPair) (hp : p.IsRamified) (ξ : D.Twist) (e : ℕ)
    [NeZero e] :
    IsTameFor (D.twistModulus ξ.toTameChar e) (p.character * ξ.toAutChar)⁻¹
      (fun τ : NumberField.InfinitePlace D.E ↦ p.negWeight τ)
      (charOfTamePart (D.twistModulus ξ.toTameChar e) (p.tamePart * ξ.tamePart))⁻¹ := by
  simpa [Pi.neg_def] using (p.isTameFor_mul hp ξ e).inv

/-- For a critical pair `(ν, z)`, a twist `ξ` of modulus `Q`, `e ≠ 0` and a sign, the number
`lValueProd` up to `z` for `(ν ξ) ^ sign` and the places of `𝔪 = ϖᵉ Q` equals the number for `ν` and
the chosen places, times `N(Q) ^ z ^ 2` and the square of the product of the ratios of Hecke
values. -/
lemma CriticalPair.lValueProd_mul_zpow_eq (p : D.CriticalPair) (ξ : D.Twist) (e : ℕ) [NeZero e]
    (sign : ℤˣ) :
    lValueProd (D.twistModulus ξ.toTameChar e).places ((p.character * ξ.toAutChar) ^ sign.val) p.z =
      lValueProd {w : FinPlace D.E | D.IsChosen w} p.character p.z *
        (ξ.normQ : ℝ) ^ p.z ^ 2 * D.lRatioProd p.character p.z ξ.toTameChar ^ 2 := by
  rw [places_twistModulus, ← p.lValueProd_mul_inv_eq]
  obtain rfl | rfl := Int.units_eq_one_or sign
  · simp only [Units.val_one, zpow_one, lValueProd, p.L_mul_inv]
  · simp

/-- Let `p = (ν, z)` be a ramified critical pair of `D` of weight `-negWeight`, so the tame part of
`ν` is non-trivial exactly at the chosen places. Let `ξ` be a twist, a tame character whose tame
part is non-trivial at each place of its modulus `Q`. Let `𝔪 = ϖᵉ Q` with `e ≠ 0`, where `ϖ` is the
product of the chosen places. Then `ν ξ` and its inverse are tame for `𝔪`: they have weights
`-negWeight` and `negWeight`, tame part non-trivial exactly at the places of `𝔪`, and character
`charOfTamePart` (or its inverse). For both of them, `lValueProd` equals that for `ν` and the chosen
places, times `ξ.normQ ^ z ^ 2` and the square of `lRatioProd`, the product of the ratios of Hecke
values. -/
theorem CriticalPair.isTameFor_mul_and_lValueProd_eq (p : D.CriticalPair) (hp : p.IsRamified)
    (ξ : D.Twist) (e : ℕ) [NeZero e] :
    IsTameFor (D.twistModulus ξ.toTameChar e) (p.character * ξ.toAutChar)
      (fun τ : NumberField.InfinitePlace D.E ↦ -p.negWeight τ)
      (charOfTamePart (D.twistModulus ξ.toTameChar e) (p.tamePart * ξ.tamePart)) ∧
    IsTameFor (D.twistModulus ξ.toTameChar e) (p.character * ξ.toAutChar)⁻¹
      (fun τ : NumberField.InfinitePlace D.E ↦ p.negWeight τ)
      (charOfTamePart (D.twistModulus ξ.toTameChar e) (p.tamePart * ξ.tamePart))⁻¹ ∧
    ∀ sign : ℤˣ,
      lValueProd (D.twistModulus ξ.toTameChar e).places ((p.character * ξ.toAutChar) ^ sign.val) p.z
        =
        lValueProd {w : FinPlace D.E | D.IsChosen w} p.character p.z *
          (ξ.normQ : ℝ) ^ p.z ^ 2 * D.lRatioProd p.character p.z ξ.toTameChar ^ 2 :=
  ⟨p.isTameFor_mul hp ξ e, p.isTameFor_mul_inv hp ξ e, p.lValueProd_mul_zpow_eq ξ e⟩

/-- For a ramified critical pair `(ν, z)`, `1 ≤ n ≤ m` and `e ≠ 0`, the character `(ν ϑⁿ)⁻¹` is tame
for the modulus `twistModulus ϑ e = ϖᵉ Q` ((ϖ) the product of the chosen places, Q the modulus of
ϑ), with weight `negWeight`. -/
lemma CriticalPair.isTameFor_inv_mul_pow (p : D.CriticalPair) (hp : p.IsRamified) (e : ℕ) [NeZero e]
    (n : D.LiftIndex) (ϑ : D.MFoldTwist) :
    IsTameFor (D.twistModulus ϑ e) (p.character * ϑ.toAutChar ^ n.val)⁻¹
      (fun τ : NumberField.InfinitePlace D.E ↦ p.negWeight τ)
      (charOfTamePart (D.twistModulus ϑ e) (p.tamePart * ϑ.tamePart ^ n.val))⁻¹ := by
  obtain ⟨-, h_inv, -⟩ := p.isTameFor_mul_and_lValueProd_eq hp (ϑ.powTwist n) e
  exact h_inv

end New.Data

end
