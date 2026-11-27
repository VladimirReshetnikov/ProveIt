import Lib.SiegelWeil.Tower.FiniteTateIntegral
import New.Determinant.Twist.FitTwists

/-!
# The algebraic part as a Hecke L-value, and products of L-values of twists

Let `p = (ν, z)` be a critical pair and `ϑ` a tame character of modulus `Q`. For the statements on
`algPart` and `integralAlgebraicPart` assume `z ≥ 2` and fix an index set with `2 z` elements
(`New.Data.CriticalPair.HasLiftRank`). The number `New.Data.CriticalPair.algPart` is the normalised
squared norm of the lift `New.Data.CriticalPair.trivialLift` of `ν ϑ`. It is positive and equals a
constant independent of `ϑ` times an `L`-value of `ν ϑ`, so the ratio of the absolute values of the
twisted and untwisted `L`-values, which is nonzero, is a ratio of values of `algPart`.

## Main definitions and results

* `New.Data.CriticalPair.algPart_pos`, `New.Data.CriticalPair.exists_ne_zero_algPart_eq_mul_L`: the
  number `New.Data.CriticalPair.algPart` is positive, and it is a nonzero constant independent of
  `ϑ` times an `L`-value of `ν ϑ`. `New.Data.CriticalPair.exists_algPart_eq_mul_L` states the value
  with the positivity.
* `New.Data.CriticalPair.ratio_eq_algPart_div`: the ratio `New.Data.CriticalPair.ratio` of the
  absolute values of twisted and untwisted `L`-values is a ratio of values of `algPart`.
* `New.Data.CriticalPair.exists_integralAlgebraicPart_eq_mul_L`,
  `New.Data.CriticalPair.ratio_eq_integralAlgebraicPart_div`: the same value and ratio for the
  multiple `New.Data.CriticalPair.integralAlgebraicPart`, with the `L`-value of `(ν ϑ)⁻¹`.
* `New.Data.CriticalPair.exists_ofAlgForm_trivialLift_eq_smul_lift`,
  `New.Data.CriticalPair.formAction_trivialLift`: the lift is a nonzero multiple of the theta lift
  of the constant function `1`, and the finite group of rank one at the chosen places fixes it.
* `New.Data.CriticalPair.lValueProd_eq_mul_prod_ratio_sq`: the product `New.Exchange.lValueProd` of
  squared L-values for the twist is the untwisted one times a power of the norm of `Q` and the
  squared ratios at `1, …, p.z`.

Notions from other files:
* `New.Data.CriticalPair`: a critical pair `p = (ν, z)`, of an integer `1 ≤ z ≤ D.t` and a character
  `ν` of U(1)(𝔸) of weight `-c` with `z ≤ c ≤ 4 D.b`, whose tame part is supported on the chosen
  places (`New.Data.IsChosen`).
* `New.Data.TameChar`: a character `ϑ` of U(1)(𝔸) of weight 0 with tame part supported on a finite
  set `Q` of places; `ϑ.normQ` is the product `N(Q)` of the norms of the places of `Q`.
* `New.AutChar.L`: `ν.L S` is the `L`-function of `x ↦ ν (x / x̄)` without the Euler factors at `S`
  and at the conjugates of the places of `S`, as an Euler product at real points `s > 1` and as
  its limit from the right at `s = 1`.
* `New.Data.CriticalPair.lValueData`: the data (`New.LValueData`) of the theta lift from U(1) to the
  definite `U(2 z)` for the character `ν ϑ`.
* `New.Data.CriticalPair.trivialLift`: the lift of `ν ϑ`, a nonzero multiple of the unscaled lift
  `New.LValueData.trivialLift`, which is the sum of the theta kernels over the classes of U(1).
* `New.Data.CriticalPair.algPart`: the number `‖φ‖ ^ 2 / N(Q) ^ (2 z - 1)`, where `φ` is the lift of
  `ν ϑ`; `integralAlgebraicPart` is a multiple of it by a natural number that does not depend on
  `ϑ`.

## Relation to the literature

Known; see `Lib.SiegelWeil.RallisInner.SharpData` for sources.
-/

/-!
## The algebraic part as a multiple of a Hecke L-value

Fix an index set `n` with `2 z` elements, where `z ≥ 2` (`New.Data.CriticalPair.HasLiftRank`).
`TameChar.one` is the trivial character, with `Q = ∅`.
-/

namespace New.Data.CriticalPair

open Fintype

variable {P : Parameters} {D : Data P} {p : D.CriticalPair} {n : Type} [Fintype n] [DecidableEq n]

/-- The unscaled lift `(lValueData H ϑ).trivialLift` of a tame character `ϑ` is the algebraic form
on the definite unitary group `U(n)` obtained from `ν ϑ` on U(1) as the sum of the theta kernels
over the classes of U(1). There is a constant `C ≠ 0` such that, for every `ϑ` of modulus `Q`, the
square of the norm of this lift is `C` times the `L`-value of `(ν ϑ)⁻¹` at `z`, away from the chosen
places, `Q` and their conjugates, times `N(Q) ^ (card n - 1)`. -/
lemma exists_norm_sq_trivialLift_eq_mul_L (H : p.HasLiftRank n) :
    ∃ C ≠ (0 : ℂ), ∀ ϑ : D.TameChar,
      (‖(lValueData H ϑ).trivialLift‖ : ℂ) ^ 2 =
        C * (p.character * ϑ.toAutChar)⁻¹.L ({w : FinPlace D.E | D.IsChosen w} ∪ ϑ.Q) p.z *
          ϑ.normQ ^ (card n - 1) := by
  -- In `LValueData.inner_trivialLift_self_eq_L` the masses, the chosen places and the weight `κ`
  -- do not depend on `ϑ`.
  have h_card : 2 * p.z = card n := H.left.symm
  have hz : 1 < p.z := H.right
  let κ : NumberField.InfinitePlace D.E → ℕ → ℕ := (lValueData H .one).descentPair.columnCount
  let mass : ℂ := (stdSpace D.E n).quotMeasure.real ⊤ * (stdSpace D.E Unit).quotMeasure.real ⊤ /
    eulerProd (K := D.E) placeSign (card n / 2 : ℕ)
  let C : ℂ := mass * (∏ i : (j : Fin 2) × D.ChosenPlace j, ((D.chosenPlace i).q - 1) : ℕ) *
    hookNumber κ (rankAt fun _ ↦ n) * card (WeylIndex n κ)
  have h_mass : mass ≠ 0 := ((lValueData H .one).inner_trivialLift_self_eq_L h_card hz).left
  have hC : C ≠ 0 := by
    -- `card_pi` would split the positive number `card (WeylIndex n κ)` into a product.
    simp [C, h_mass, ne_of_gt, -card_pi, Finset.prod_eq_zero_iff, sub_eq_zero]
  refine ⟨C, hC, fun ϑ ↦ ?_⟩
  have h_inner : inner ℂ (lValueData H ϑ).trivialLift (lValueData H ϑ).trivialLift =
      C * (p.character * ϑ.toAutChar)⁻¹.L (lValueData H ϑ).places p.z *
        (∏ w : ϑ.Q, FinPlace.q w.val : ℕ) ^ (card n - 1) :=
    ((lValueData H ϑ).inner_trivialLift_self_eq_L h_card hz).right
  have h_places : (lValueData H ϑ).places = {w | D.IsChosen w} ∪ ϑ.Q := by
    simp [levelPlaces, range_chosenPlace]
  rw [← h_places, TameChar.normQ, ← ϑ.Q.prod_coe_sort]
  exact (inner_self_eq_norm_sq_to_K _).symm.trans h_inner

/-- The factor `D.chosenGroupOrder * p.denomBound ^ 2` by which `integralAlgebraicPart` is a
multiple of `algPart` is nonzero in `ℂ`. Here `D.chosenGroupOrder` is the product of the orders of
the groups `GL (r t)` over the residue fields at the chosen places, and `p.denomBound` is a
denominator for the values of the lift. -/
lemma cast_chosenGroupOrder_mul_denomBound_sq_ne_zero (p : D.CriticalPair) :
    ((D.chosenGroupOrder * p.denomBound ^ 2 : ℕ) : ℂ) ≠ 0 := by
  simp [denomBound, NeZero.ne]

/-- The scalar `P.vacuumScale D.towerExp ^ k * (star D.piMBar * P.jetScale D.towerExp) ^
p.rowLengthSum` is nonzero. It is the scalar by which `trivialLift` is a multiple of the unscaled
lift, for an index set with `k` elements. -/
lemma vacuumScale_pow_mul_pow_rowLengthSum_ne_zero (p : D.CriticalPair) (k : ℕ) :
    P.vacuumScale D.towerExp ^ k * (star (D.piMBar : ℂ) * P.jetScale D.towerExp) ^ p.rowLengthSum ≠
      0 := by
  simp

/-- Let `p = (ν, z)` be a pair and `ϑ` a tame character. Without the Euler factors at the chosen
places, the modulus `ϑ.Q` and their conjugates, the `L`-functions of `ν ϑ` and of its inverse
agree. -/
lemma L_inv_mul (ϑ : D.TameChar) :
    (p.character * ϑ.toAutChar)⁻¹.L ({w : FinPlace D.E | D.IsChosen w} ∪ ϑ.Q) =
      (p.character * ϑ.toAutChar).L ({w : FinPlace D.E | D.IsChosen w} ∪ ϑ.Q) := by
  refine (p.hasWeight.mul ϑ.hasWeight).L_inv fun w hw ↦ ?_
  rw [Pi.mul_apply, p.tamePart_eq_one w fun h ↦ hw (.inl h), ϑ.tamePart_eq_one w fun h ↦
    hw (.inr h), one_mul]

lemma one_le_cast_z (p : D.CriticalPair) : (1 : ℝ) ≤ p.z := mod_cast p.z_mem.left

/-- The weight `-c` of the character `ν` of a pair `p = (ν, z)`, that is, the function
`v ↦ -(p.negWeight v)` on `D.Φ` with `c = p.negWeight`, is not zero, as `1 ≤ z ≤ c(v)` for every
`v`. -/
lemma neg_negWeight_ne_zero (p : D.CriticalPair) : (fun v : D.Φ ↦ -(p.negWeight v : ℤ)) ≠ 0 := by
  refine Function.ne_iff.2 ⟨1, ?_⟩
  simpa [Nat.one_le_iff_ne_zero] using p.z_mem.left.trans (p.le_negWeight 1)

/-- Let `p = (ν, z)` be a pair and `ϑ` a tame character. The `L`-function of `ν ϑ`, without the
Euler factors at the chosen places, the modulus `ϑ.Q` and their conjugates, is not zero at `z`. -/
lemma L_mul_ne_zero (p : D.CriticalPair) (ϑ : D.TameChar) :
    (p.character * ϑ.toAutChar).L ({w : FinPlace D.E | D.IsChosen w} ∪ ϑ.Q) p.z ≠ 0 := by
  -- As `ϑ` has weight zero, `ν ϑ` has the weight `-c` of `ν`, which is not zero.
  refine (p.hasWeight.mul ϑ.hasWeight).L_ne_zero (D.finite_isChosen.union ϑ.Q.finite_toSet)
    ?_ p.one_le_cast_z
  simpa using p.neg_negWeight_ne_zero

/-- Let `p = (ν, z)` be a critical pair with `z ≥ 2` and `ϑ` a tame character. The lift
`trivialLift H ϑ` of the character `ν ϑ`, from U(1) to the definite `U(2 z)`, is nonzero. -/
@[simp]
lemma trivialLift_ne_zero (H : p.HasLiftRank n) (ϑ : D.TameChar) : trivialLift H ϑ ≠ 0 := by
  obtain ⟨C, hC, h_norm_sq⟩ := exists_norm_sq_trivialLift_eq_mul_L H
  -- The squared norm of the unscaled lift is a product of nonzero numbers.
  have h_ne : (‖(lValueData H ϑ).trivialLift‖ : ℂ) ^ 2 ≠ 0 := by
    rw [h_norm_sq, L_inv_mul]
    simp [hC, p.L_mul_ne_zero ϑ, Finset.prod_eq_zero_iff]
  rw [trivialLift]
  exact smul_ne_zero (p.vacuumScale_pow_mul_pow_rowLengthSum_ne_zero (card n)) (by simpa using h_ne)

open scoped ComplexOrder in
/-- Let `p = (ν, z)` be a critical pair and `H` the hypothesis that the index set `n` has `2 z`
elements, with `z ≥ 2`, and let `ϑ` be a tame character. The algebraic part `algPart H
ϑ = ‖trivialLift H ϑ‖ ^ 2 / N(Q) ^ (card n - 1)` is a positive real number. -/
lemma algPart_pos (H : p.HasLiftRank n) (ϑ : D.TameChar) : 0 < algPart H ϑ := by
  have h_norm : 0 < ‖trivialLift H ϑ‖ := norm_pos_iff.2 (trivialLift_ne_zero H ϑ)
  have h_level : 0 < ϑ.normQ := Nat.pos_of_ne_zero (by simp [Finset.prod_eq_zero_iff])
  rw [algPart]
  exact_mod_cast (show (0 : ℝ) < ‖trivialLift H ϑ‖ ^ 2 / ϑ.normQ ^ (card n - 1) by positivity)

/-- Let `p = (ν, z)` be a critical pair and `H : p.HasLiftRank n` the hypothesis that the index set
`n` has `2 z` elements, with `z ≥ 2`. For a tame character `ϑ` of modulus `Q`, `algPart H ϑ` is the
algebraic part of the `L`-value of `ν ϑ` at `z`, defined as `‖φ‖ ^ 2 / N(Q) ^ (card n - 1)`. Here
`φ = trivialLift H ϑ` is the scaled lift of `ν ϑ` to `U(n)`, and `N(Q)` is the product of the norms
of the places of `Q`. There is a constant `A ≠ 0` such that, for every `ϑ`, this number is `A` times
the `L`-value of `ν ϑ` at `z`, without the Euler factors at the chosen places, the modulus `Q` and
their conjugates. -/
theorem exists_ne_zero_algPart_eq_mul_L (H : p.HasLiftRank n) :
    ∃ A ≠ (0 : ℂ), ∀ ϑ : D.TameChar,
      algPart H ϑ = A * (p.character * ϑ.toAutChar).L ({w : FinPlace D.E | D.IsChosen w} ∪ ϑ.Q)
        p.z := by
  -- The constant is that of the unscaled lift times the squared absolute value of the scale.
  obtain ⟨C, hC, h_norm_sq⟩ := exists_norm_sq_trivialLift_eq_mul_L H
  let scale : ℂ := P.vacuumScale D.towerExp ^ card n * (star (D.piMBar : ℂ) * P.jetScale D.towerExp)
    ^ p.rowLengthSum
  have h_scale : scale ≠ 0 := p.vacuumScale_pow_mul_pow_rowLengthSum_ne_zero (card n)
  refine ⟨‖scale‖ ^ 2 * C, mul_ne_zero (by simpa using h_scale) hC, fun ϑ ↦ ?_⟩
  have h_level : (ϑ.normQ : ℂ) ≠ 0 := by simp [Finset.prod_eq_zero_iff]
  calc algPart H ϑ
      = ‖scale‖ ^ 2 * (‖(lValueData H ϑ).trivialLift‖ ^ 2 / ϑ.normQ ^ (card n - 1)) := by
        rw [algPart, trivialLift, norm_smul, Complex.ofReal_mul]
        ring
    _ = ‖scale‖ ^ 2 * C * (p.character * ϑ.toAutChar).L ({w | D.IsChosen w} ∪ ϑ.Q) p.z := by
        rw [h_norm_sq, L_inv_mul, mul_div_cancel_right₀ _ (pow_ne_zero _ h_level), ← mul_assoc]

open scoped ComplexOrder in
/-- For every tame character `ϑ` of modulus `Q`, the algebraic part `algPart H ϑ = ‖trivialLift H ϑ‖
^ 2 / N(Q) ^ (card n - 1)`, the normalised squared norm of the lift of `ν ϑ`, is positive. It is the
`L`-value of `ν ϑ` at `z`, without the factors at the chosen places, the modulus and their
conjugates, times a number `A` that depends neither on `ϑ` nor on its modulus. -/
theorem exists_algPart_eq_mul_L (H : p.HasLiftRank n) :
    ∃ A : ℂ, ∀ ϑ : D.TameChar,
      algPart H ϑ = A * (p.character * ϑ.toAutChar).L ({w : FinPlace D.E | D.IsChosen w} ∪ ϑ.Q) p.z
        ∧
      0 < algPart H ϑ := by
  obtain ⟨A, -, h_value⟩ := exists_ne_zero_algPart_eq_mul_L H
  exact ⟨A, fun ϑ ↦ ⟨h_value ϑ, algPart_pos H ϑ⟩⟩

open scoped ComplexOrder in
/-- The sign in `p.ratio ϑ` is the default `1`, so this is the ratio of the absolute values of the
`L`-values at `z` of `(ν ϑ)⁻¹` and of `ν⁻¹`. It is equal to the algebraic part `algPart H
ϑ = ‖trivialLift H ϑ‖ ^ 2 / N(Q) ^ (card n - 1)`, the normalised squared norm of the lift of `ν ϑ`,
divided by the same number for the trivial character. -/
theorem ratio_eq_algPart_div (H : p.HasLiftRank n) (ϑ : D.TameChar) :
    p.ratio ϑ = algPart H ϑ / algPart H TameChar.one := by
  obtain ⟨A, hA⟩ := exists_algPart_eq_mul_L H
  obtain ⟨h_value, h_pos⟩ := hA ϑ
  obtain ⟨h_value_one, h_pos_one⟩ := hA TameChar.one
  -- The constant `A` is a factor of a positive number, so it cancels in the quotient.
  have hA_ne : A ≠ 0 := left_ne_zero_of_mul (h_value.symm.trans_ne h_pos.ne')
  have h_div : algPart H ϑ / algPart H TameChar.one =
      (p.character * ϑ.toAutChar)⁻¹.L ({w | D.IsChosen w} ∪ ϑ.Q) p.z / p.character⁻¹.L
        {w | D.IsChosen w} p.z := by
    rw [h_value, h_value_one, mul_div_mul_left _ _ hA_ne, ← L_inv_mul, ← L_inv_mul]
    simp [toAutChar_one_and_toTwist_one_and_Q_one]
  -- The quotient is a positive real number, so it is equal to its norm.
  calc p.ratio ϑ = ‖algPart H ϑ / algPart H TameChar.one‖ := by
        rw [h_div]
        simp [ratio]
    _ = algPart H ϑ / algPart H TameChar.one :=
        Complex.norm_of_nonneg' (div_pos h_pos h_pos_one).le

open scoped ComplexOrder in
/-- Let `p = (ν, z)` be a critical pair with `z ≥ 2` and `ϑ` a tame character. The number
`integralAlgebraicPart H ϑ`, a natural multiple of the normalised squared norm of the lift of `ν ϑ`,
is nonzero. -/
@[simp]
lemma integralAlgebraicPart_ne_zero (H : p.HasLiftRank n) (ϑ : D.TameChar) :
    integralAlgebraicPart H ϑ ≠ 0 := by
  rw [integralAlgebraicPart]
  exact mul_ne_zero p.cast_chosenGroupOrder_mul_denomBound_sq_ne_zero (algPart_pos H ϑ).ne'

/-- There is a constant `A ≠ 0` such that, for every tame character `ϑ`, `integralAlgebraicPart H ϑ`
is `A` times the `L`-function of `(ν ϑ)⁻¹` at `z`, without the Euler factors at the chosen places
(`New.Data.IsChosen`), the places of the modulus `ϑ.Q` and their conjugates. -/
lemma exists_integralAlgebraicPart_eq_mul_L (H : p.HasLiftRank n) :
    ∃ A ≠ (0 : ℂ), ∀ ϑ : D.TameChar,
      integralAlgebraicPart H ϑ =
        A * (p.character * ϑ.toAutChar)⁻¹.L ({w : FinPlace D.E | D.IsChosen w} ∪ ϑ.Q) p.z := by
  obtain ⟨A, hA, h_value⟩ := exists_ne_zero_algPart_eq_mul_L H
  let N : ℂ := (D.chosenGroupOrder * p.denomBound ^ 2 : ℕ)
  refine ⟨N * A, mul_ne_zero p.cast_chosenGroupOrder_mul_denomBound_sq_ne_zero hA, fun ϑ ↦ ?_⟩
  rw [integralAlgebraicPart, h_value ϑ, L_inv_mul, mul_assoc]

/-- Let `p = (ν, z)` be a critical pair, `H : p.HasLiftRank n` and `ϑ` a tame character. The ratio
`p.ratio ϑ` of the absolute values of the `L`-values at `z` of `(ν ϑ)⁻¹` and of `ν⁻¹` equals
`integralAlgebraicPart H ϑ / integralAlgebraicPart H TameChar.one`. -/
lemma ratio_eq_integralAlgebraicPart_div (H : p.HasLiftRank n) (ϑ : D.TameChar) :
    p.ratio ϑ = integralAlgebraicPart H ϑ / integralAlgebraicPart H TameChar.one := by
  rw [ratio_eq_algPart_div H, integralAlgebraicPart, integralAlgebraicPart,
    mul_div_mul_left _ _ p.cast_chosenGroupOrder_mul_denomBound_sq_ne_zero]

/-- For a pair `p = (ν, z)`, a tame character `ϑ` and a sign `s = ±1`, the ratio `p.ratio ϑ s` of
the absolute values of the `L`-values at `z` of `(ν ϑ ^ s)⁻¹` and of `ν⁻¹` is nonzero. -/
lemma ratio_ne_zero (p : D.CriticalPair) (ϑ : D.TameChar) (s : ℤˣ) : p.ratio ϑ s ≠ 0 := by
  -- The weight `-c` of `ν` is not zero and `ϑ` has weight zero, so neither `L`-value vanishes.
  have h_num : (p.character * ϑ.toAutChar ^ (s : ℤ))⁻¹.L ({w | D.IsChosen w} ∪ ϑ.Q) p.z ≠ 0 := by
    refine (p.hasWeight.mul (ϑ.hasWeight.zpow s)).inv.L_ne_zero
      (D.finite_isChosen.union ϑ.Q.finite_toSet) ?_ p.one_le_cast_z
    simpa using p.neg_negWeight_ne_zero
  have h_den : p.character⁻¹.L {w | D.IsChosen w} p.z ≠ 0 :=
    p.hasWeight.inv.L_ne_zero D.finite_isChosen (neg_ne_zero.2 p.neg_negWeight_ne_zero)
      p.one_le_cast_z
  simpa [ratio] using And.intro h_num h_den

/-- For a pair `p`, a tame character `ϑ` and a sign `s = ±1`, the ratio `p.ratio ϑ s`, a quotient
of absolute values, is real: complex conjugation fixes it. -/
lemma star_ratio (p : D.CriticalPair) (ϑ : D.TameChar) (s : ℤˣ) :
    star (p.ratio ϑ s) = p.ratio ϑ s := by
  simp [ratio]

/-- For a pair `p = (ν, z)`, a tame character `ϑ` and a sign `s = ±1`, the ratio `p.ratio ϑ s` of
the absolute values of the `L`-values at `z` of `(ν ϑ ^ s)⁻¹` and of `ν⁻¹` is nonzero and real. -/
lemma ratio_ne_zero_and_real (p : D.CriticalPair) (ϑ : D.TameChar) (s : ℤˣ) :
    p.ratio ϑ s ≠ 0 ∧ star (p.ratio ϑ s) = p.ratio ϑ s :=
  ⟨p.ratio_ne_zero ϑ s, p.star_ratio ϑ s⟩

end New.Data.CriticalPair

namespace New

open Fintype Finset Matrix Complex Space SiegelWeil Rows WeilData

section

variable {E m : Type} [Field E] [CMType E] [WeilData E] [Fintype m] [DecidableEq m]
  (X : LValueData E m)

/-- Let `X` be data for the lift from U(1) to the definite unitary group on `m`, with descent pair
`X.descentPair` (the line, the group on `m` and the character of `X`). The product `ChosenGL Unit`
of the groups `GL₁` over the residue fields at the chosen places, which acts on algebraic forms by
`formAction`, fixes `X.trivialLift`, a multiple of the theta lift of the constant function `1`. -/
lemma LValueData.formAction_trivialLift (s : X.descentPair.ChosenGL Unit) :
    X.descentPair.formAction s X.trivialLift = X.trivialLift := by
  -- The group fixes the constant `1` and commutes with the theta lift.
  have h_fix : X.descentPair.W.formRep (typeKernel 0 X.descentPair.signs)
    (liftResidue s : stdLevel E Unit)
      X.constForm = X.constForm := rfl
  rw [X.trivialLift_eq_smul_thetaLift, map_smul,
    ← X.descentPair.thetaLift_formRep X.fitsParams_descentPair _ (reduceFamily_liftResidue s),
      h_fix]

end

namespace Data.CriticalPair

variable {P : Parameters} {D : Data P} {p : D.CriticalPair} {n : Type} [Fintype n] [DecidableEq n]

/-- Let `p = (ν, z)` be a critical pair with `z ≥ 2` and `ϑ` a tame character. Let `O` be the
descent pair `(lValueData H ϑ).descentPair` of the lift from U(1) to `U(2 z)`, with weight
`O.columnCount`. The function on the adelic group `U(2 z)(𝔸)` attached by `ofAlgForm` to the
algebraic form `trivialLift H ϑ` (its matrix coefficient against the highest vector for the
parameter `O.paramV`, all signs being `1`) is a nonzero multiple of the theta lift, by the theta
kernel `O.pairThetaKernel`, of the constant function `1` on the adelic group `New.G` of U(1), taken
at the Schwartz function `O.fockDatum` made from that highest vector. -/
theorem exists_ofAlgForm_trivialLift_eq_smul_lift (H : p.HasLiftRank n) (ϑ : D.TameChar) :
    ∃ c : ℂ, c ≠ 0 ∧
      ofAlgForm (lValueData H ϑ).descentPair.paramV 1 (trivialLift H ϑ).val =
        c • lift (lValueData H ϑ).descentPair.pairThetaKernel
          ((lValueData H ϑ).descentPair.fockDatum
            (highestVector (lValueData H ϑ).descentPair.columnCount
              (lValueData H ϑ).descentPair.paramV))
          fun _ : New.G D.E (lValueData H ϑ).descentPair.signs ↦ 1 := by
  let scale : ℂ := P.vacuumScale D.towerExp ^ card n * (star (D.piMBar : ℂ) * P.jetScale D.towerExp)
    ^ p.rowLengthSum
  have h_scale : scale ≠ 0 := p.vacuumScale_pow_mul_pow_rowLengthSum_ne_zero (card n)
  have h_index : (stdLevelIndex (lValueData H ϑ).chosenLevel : ℂ) ≠ 0 := by simp
  refine ⟨scale * stdLevelIndex (lValueData H ϑ).chosenLevel, mul_ne_zero h_scale h_index, ?_⟩
  rw [mul_smul, (lValueData H ϑ).lift_fockDatum_const_one, smul_inv_smul₀ h_index, trivialLift]
  exact map_smul _ scale _

/-- Let `p = (ν, z)` be a critical pair, with `H` saying that `n` has `2 z` elements and `z ≥ 2`,
and let `ϑ` be a tame character. The product of the groups `GL₁` over the residue fields at the
chosen places of `lValueData H ϑ` acts by `formAction`, and it fixes the lift `trivialLift H ϑ` of
`ν ϑ`. -/
theorem formAction_trivialLift (H : p.HasLiftRank n) (ϑ : D.TameChar)
    (s : (lValueData H ϑ).descentPair.ChosenGL Unit) :
    (lValueData H ϑ).descentPair.formAction s (trivialLift H ϑ) = trivialLift H ϑ := by
  rw [trivialLift, map_smul, LValueData.formAction_trivialLift]

end Data.CriticalPair

end New

/-!
## Products of squared L-values of a twist

The section opens with `New.Data.IsRegularFamily.heightLe_of_eq_zpow_mul`: for a family of twists
with `IsRegularFamily`, a bound on the height of a family of numbers survives multiplication by
powers of the norms of the moduli, such as the power in
`New.Data.CriticalPair.lValueProd_eq_mul_prod_ratio_sq`.
-/

namespace New.Data

open Finset Exchange

variable {P : Parameters} {D : Data P}

/-- For each pair `ι` of a prime `ℓ` and an isomorphism `ℂ ≃ ℚ̄_ℓ` let `θ ι` be an `m`-fold twist
(`New.Data.MFoldTwist`: a twist whose tame part has nontrivial powers of exponent `1, …, m` at the
places of its modulus, for the number `m = D.m` fixed by the data `D`). Assume that the
family is regular (`New.Data.IsRegularFamily`: small ratios and bounded denominators), so that the
norm of the modulus of `θ ι` is prime to `ℓ`. Height at most `c` (`New.HeightLe`) means that there
are `H ≠ 0`, a real `α` and reals `h ℓ ≥ 0` with `‖σ H‖ ≤ exp α` for every automorphism `σ` of `ℂ`,
with `ℓ`-adic absolute value of `H * y ι` at most `ℓ ^ h ℓ` for every `ι`, and with
`α + ∑ ℓ ∈ T, h ℓ * log ℓ ≤ c` for every finite set `T` of primes. If the family `y` has height at
most `c ≤ c'`, and each `y' ι` is zero or is `y ι` times an integer power of that norm, then `y'`
has height at most `c'`. -/
lemma IsRegularFamily.heightLe_of_eq_zpow_mul {c c' : ℝ} {y y' : PrimePadicIso → ℂ}
    {θ : PrimePadicIso → D.MFoldTwist} (hθ : D.IsRegularFamily θ) (h_height : HeightLe c y)
    (hc : c ≤ c') (hy : ∀ ι : PrimePadicIso, y' ι ≠ 0 → ∃ k : ℤ, y' ι = (θ ι).normQ ^ k * y ι) :
    HeightLe c' y' := by
  choose! k hk using hy
  -- Multiplying by powers of numbers prime to `ℓ` keeps the bound on the height.
  refine (h_height.rpow_mul hc hθ.coprime fun ι ↦ k ι).mono le_rfl fun ι ↦ ?_
  by_cases h_zero : y' ι = 0
  · simp only [h_zero, map_zero, norm_zero, norm_nonneg]
  · rw [hk ι h_zero, Rat.cast_intCast, Real.rpow_intCast, Complex.ofReal_zpow,
      Complex.ofReal_natCast]

/-- The pair with the same character as `p` and the point `max 1 (min z p.z)`; for `1 ≤ z ≤ p.z`
this is `z`. Clamping makes the definition total. -/
def CriticalPair.lowerPoint (p : D.CriticalPair) (z : ℕ) : CriticalPair D :=
  { p with
    z := 1 ⊔ z ⊓ p.z
    z_mem :=
      ⟨le_sup_left,
        sup_le (p.z_mem.left.trans p.z_mem.right) (inf_le_right.trans p.z_mem.right)⟩
    le_negWeight := fun v ↦ sup_le (p.z_mem.left.trans (p.le_negWeight v))
      (inf_le_right.trans (p.le_negWeight v)) }

/-- No place of the modulus `Q` of a tame character `ϑ` is a chosen place. -/
lemma TameChar.disjoint_isChosen_Q (ϑ : D.TameChar) :
    Disjoint {w : FinPlace D.E | D.IsChosen w} (ϑ.Q : Set (FinPlace D.E)) := by
  refine Set.disjoint_right.2 fun w hw ↦ ?_
  exact (D.normQ_mem_and_notMem_of_mem_Q ϑ (Or.inl hw)).right.left

/-- For `1 ≤ z ≤ p.z`, the ratio of the pair `p.lowerPoint z = (ν, z)` at a tame character `ϑ` and
a sign `s` is the quotient of the absolute values of the `L`-values at `z` of `(ν ϑ ^ s)⁻¹` and of
`ν⁻¹`. -/
lemma CriticalPair.ratio_lowerPoint (p : D.CriticalPair) (s : ℤˣ) (ϑ : D.TameChar) {z : ℕ}
    (hz : z ∈ Icc 1 p.z) :
    (p.lowerPoint z).ratio ϑ s =
      ‖(p.character * ϑ.toAutChar ^ (s : ℤ))⁻¹.L ({w : FinPlace D.E | D.IsChosen w} ∪ ϑ.Q) z‖ /
        ‖p.character⁻¹.L {w : FinPlace D.E | D.IsChosen w} z‖ := by
  simp only [ratio, lowerPoint, inf_of_le_left (mem_Icc.1 hz).right,
    sup_of_le_right (mem_Icc.1 hz).left]

/-- Let `p` be a pair with character `ν`, let `ϑ` be a tame character of modulus `Q` and `s` a sign.
Recall `lValueProd S χ e = ∏_{w ∈ S} q_w ^ e ^ 2 * ∏_{1 ≤ z ≤ e} |L^S(z, χ)| ^ 2`. This product up
to `p.z` for `(ν ϑ ^ s)⁻¹`, away from the chosen places and `Q`, equals a product of three factors.
The first is `ϑ.normQ ^ p.z ^ 2`. The second is the product for `ν⁻¹`, away from the chosen places.
The third is the product of the squares of the ratios `|L(z, (ν ϑ ^ s)⁻¹)| / |L(z, ν⁻¹)|` of the
pairs `p.lowerPoint z = (ν, z)` for `1 ≤ z ≤ p.z`. -/
lemma CriticalPair.lValueProd_eq_mul_prod_ratio_sq (p : D.CriticalPair) (s : ℤˣ) (ϑ : D.TameChar) :
    lValueProd ({w : FinPlace D.E | D.IsChosen w} ∪ ϑ.Q) (p.character * ϑ.toAutChar ^ (s : ℤ))⁻¹ p.z
      =
      ϑ.normQ ^ p.z ^ 2 *
        (lValueProd {w : FinPlace D.E | D.IsChosen w} p.character⁻¹ p.z *
          ∏ z ∈ Icc 1 p.z, (p.lowerPoint z).ratio ϑ s ^ 2) := by
  have h_norm : ∏ᶠ w ∈ {w | D.IsChosen w} ∪ (ϑ.Q : Set (FinPlace D.E)), FinPlace.q w =
      (∏ᶠ w ∈ {w | D.IsChosen w}, FinPlace.q w) * ϑ.normQ := by
    rw [finprod_mem_union ϑ.disjoint_isChosen_Q D.finite_isChosen ϑ.Q.finite_toSet,
      finprod_mem_coe_finset]
  have h_factor (z : ℕ) (hz : z ∈ Icc 1 p.z) :
      (‖(p.character * ϑ.toAutChar ^ (s : ℤ))⁻¹.L ({w | D.IsChosen w} ∪ ϑ.Q) z‖ : ℂ) ^ 2 =
        ‖p.character⁻¹.L {w | D.IsChosen w} z‖ ^ 2 * (p.lowerPoint z).ratio ϑ s ^ 2 := by
    -- As the ratio is not zero, neither is its denominator.
    have h_ratio : (p.lowerPoint z).ratio ϑ s ≠ 0 := (p.lowerPoint z).ratio_ne_zero ϑ s
    rw [p.ratio_lowerPoint s ϑ hz] at h_ratio ⊢
    rw [← mul_pow, mul_div_cancel₀ _ (div_ne_zero_iff.1 h_ratio).right]
  rw [lValueProd, lValueProd, h_norm]
  push_cast [prod_congr rfl h_factor, prod_mul_distrib]
  ring

end New.Data
