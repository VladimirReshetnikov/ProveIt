import New.Determinant.Chain.ChainNorms
import New.Spanning.Multiplicities.EqualMultiplicities

/-!
# The volume of ι on the target forms as a product of volumes of theta lifts

The volume of a linear map `u` between finite-dimensional Hilbert spaces is
`det (u* u) = u.normDet ^ 2`. For data `D`, the good forms (`New.Data.goodForms`) are the image of
the idempotent `New.Data.e₀`, and the target forms are the good forms on `Y₀`. `D.goodLift ϑ j` is
the restriction of the lift `D.singleLift ϑ j` to the good forms on `W_j`; its range is the space of
lifts.

* `New.Data.liftDeterminant`, `New.Data.chainDeterminant`: the volumes of the lift on the good forms
  and of `ι` on the target forms.
* `New.Data.exists_normDet_goodLift_sq_eq`: the volume of one lift in terms of the determinant on
  the target forms of the series of Rallis' formula.
* `New.Data.exists_chainDeterminant_eq_norm_pow_mul_prod` factors the chain volume into
  single-lift volumes and a scalar whose normalized norm has bounded height.
* `New.Data.range_goodLift_le`: the space of lifts is spanned by lifts of good eigenforms.

Notions from other files:
* `New.Data.MFoldTwist`: a twist `ϑ` whose first `m` powers are twists.
* `New.Data.principalForms`: the forms of the fixed parameter on a space that are fixed by the
  principal level at the chosen places.
* `New.Data.singleLift`: the lift from principal forms on `W_j` to algebraic forms on `V_j`.
* `New.DescentPair.twistFactor`: the constant `c_Q` in the norm of one lift.
* `New.Data.lowerChainAtLevel`: the map `ι` from forms of principal level on `Y₀` to algebraic forms
  on `Y_m` of the last level of the twist.
* `New.Data.HasAbsUpToNormPower`: `D.HasAbsUpToNormPower c f` says that `‖c ϑ‖²` is `(f ϑ)²` times a
  constant, possibly zero, and a fixed integral power of the norm of the modulus of `ϑ`.
* `New.Data.quotientRatio`: `D.quotientRatio i j ϑ` is the product of the ratios of Hecke values of
  `D.untwistedLiftChar j / D.untwistedLiftChar i` at the twist `ϑ ^ (j - i)`.

## Relation to the literature

See `New.Determinant.Chain.ChainNorms` for related work.
-/

noncomputable section

namespace New.Data

open Finset LinearMap Module

attribute [local instance low] Fintype.ofFinite

section

variable {U V : Type*} [NormedAddCommGroup U] [InnerProductSpace ℂ U]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [Module.Finite ℂ V]

variable {P : Parameters} (D : Data P)

/-- Let `u : U →ₗ[ℂ] V` be a linear map between finite-dimensional complex inner product spaces `U`
and `V`, and `S` an endomorphism of `U` with `⟪u x, u y⟫ = a ⟪x, S y⟫` for all `x`, `y`. Then
`u.normDet ^ 2`, the volume det(u* u), equals `a ^ finrank ℂ U * S.det`. -/
lemma _root_.New.normDet_sq_eq_pow_mul_det [Module.Finite ℂ U] (u : U →ₗ[ℂ] V) (S : End ℂ U) {a : ℂ}
    (h_gram : ∀ x y : U, inner ℂ (u x) (u y) = a * inner ℂ x (S y)) :
    u.normDet ^ 2 = a ^ finrank ℂ U * S.det := by
  -- The hypothesis says `u* u = a S`; take determinants, using `det (u* u) = normDet u ^ 2`.
  have h_adjoint_comp : u.adjoint ∘ₗ u = a • S :=
    ext fun y ↦ ext_inner_left ℂ fun x ↦ by simp [adjoint_inner_right, inner_smul_right, h_gram]
  simpa [← normDet_sq] using congrArg LinearMap.det h_adjoint_comp

/-- The volume `liftDeterminant ϑ j` = det(u* u) = `u.normDet ^ 2` of the lift u = `singleLift` at
`j` for the twist ϑ^j, restricted to the good forms on U(W_j) (`New.Data.goodLift`). -/
def liftDeterminant (ϑ : D.MFoldTwist) (j : ℕ) : ℂ := ((D.goodLift (ϑ.pow j) j).normDet : ℂ) ^ 2

/-- For `1 ≤ j ≤ m` and every tame character `ϑ`, the volume `det(u* u) = u.normDet ^ 2` is
positive, where `u` is the lift from `W_j` for `ϑ`, restricted to the good forms: the lift is
injective. -/
theorem normDet_goodLift_sq_pos (ϑ : D.TameChar) (j : D.LiftIndex) :
    0 < (D.goodLift ϑ j).normDet ^ 2 := by
  rw [sq_pos_iff, Ne, normDet_eq_zero_iff_ker_ne_bot, not_not, ker_eq_bot]
  exact (D.singleLift_injective ϑ).comp (Submodule.injective_subtype _)

open scoped ComplexOrder in
/-- For `1 ≤ j ≤ m` the volume of the lift from `W_j` for the twist `ϑ ^ j`, restricted to the good
forms, is a positive real number. -/
theorem liftDeterminant_pos (ϑ : D.MFoldTwist) (j : D.LiftIndex) : 0 < D.liftDeterminant ϑ j := by
  rw [liftDeterminant]
  exact_mod_cast D.normDet_goodLift_sq_pos (ϑ.pow j) j

/-- The map ι_ϑ (`New.Data.lowerChainAtLevel`) restricted to the target forms, that is to the good
forms on Y₀. It takes values in the algebraic forms on Y_m whose weight has `columnsY` columns of
each height and last entry `lastEntry m`, and whose level is given by `lastResidueLevel` (trivial at
the chosen places, block upper triangular at the places of the twist) with the character
`lastLevelChar` made of the tame characters of the lifts on the diagonal blocks. -/
abbrev Θ (ϑ : D.MFoldTwist) :
    D.targetForms →ₗ[ℂ] (D.levelPlaces ϑ.toTameChar).LevelForm (lastResidueLevel ϑ.toTameChar)
      (lastLevelChar ϑ.toTameChar) D.columnsY (D.lastEntry D.m) :=
        D.lowerChainAtLevel ϑ ∘ₗ D.targetForms.subtype

/-- The volume `chainDeterminant ϑ` = det(u*u) of u = ι_ϑ (`New.Data.lowerChainAtLevel`), the map
from forms of principal level on Y₀ to forms on Y_m, restricted to the target forms (the good forms
on Y₀). -/
def chainDeterminant (ϑ : D.MFoldTwist) : ℂ := ((D.Θ ϑ).normDet : ℂ) ^ 2

open scoped ComplexOrder in
/-- For every m-fold twist `ϑ : D.MFoldTwist`, `D.chainDeterminant ϑ` is a positive real number.
This is the volume det(u* u) of the map u = ι_ϑ from forms on Y₀ to forms on Y_m, restricted to the
target forms. So this map is injective. -/
theorem chainDeterminant_pos (ϑ : D.MFoldTwist) : 0 < D.chainDeterminant ϑ := by
  rw [chainDeterminant, ← Complex.ofReal_pow, Complex.zero_lt_real, sq_pos_iff, Ne,
    normDet_eq_zero_iff_ker_ne_bot, not_not, ker_eq_bot]
  exact (D.lowerChainAtLevel_injective ϑ).comp D.targetForms.injective_subtype

/-- For `j : D.LiftIndex`, so `1 ≤ j ≤ m`, there is a constant `A ≠ 0` with the following property.
For every tame character `ϑ`, let `u = D.goodLift ϑ j` be the lift `singleLift` restricted to the
good forms on `W_j = D.spaceW j`. Then its volume `normDet ^ 2 = det(u* u)` is `(A c_Q) ^ targetDim`
times a determinant, where `targetDim` is the dimension of the target forms. That determinant is the
one of `rallisOnGood`, the series of Rallis' formula for the `j`-th lift for `ϑ`, acting as a
spherical Hecke operator on the target forms, the good forms on `Y₀ = D.spaceY 0`. Here `c_Q` is the
constant `New.DescentPair.twistFactor` of `D.descentPair ϑ j`, the pair of spaces and the data of
that lift. -/
lemma exists_normDet_goodLift_sq_eq (j : D.LiftIndex) :
    ∃ A : ℂ, A ≠ 0 ∧ ∀ ϑ : D.TameChar,
      ((D.goodLift ϑ j).normDet : ℂ) ^ 2 =
        (A * (D.descentPair ϑ j).twistFactor) ^ D.targetDim *
          (D.rallisOnGood (D.spaceY 0) ϑ j).det := by
  obtain ⟨A, hA, h_norm⟩ := D.exists_adjoint_singleLift_comp_eq j
  refine ⟨A, hA, fun ϑ ↦ ?_⟩
  -- The series has the same determinant on the target forms and on the good forms on `W_j`.
  rw [D.targetDim_eq_finrank_goodForms_spaceW j, D.det_rallisOnGood_eq (D.spaceY 0) (D.spaceW j)]
  refine normDet_sq_eq_pow_mul_det _ _ fun x y ↦ ?_
  calc inner ℂ (D.goodLift ϑ j x) (D.goodLift ϑ j y)
      = inner ℂ x.val (((D.singleLift ϑ j).adjoint ∘ₗ D.singleLift ϑ j) y.val) :=
        (adjoint_inner_right (D.singleLift ϑ j) x.val (D.singleLift ϑ j y.val)).symm
    _ = A * (D.descentPair ϑ j).twistFactor * inner ℂ x (D.rallisOnGood (D.spaceW j) ϑ j y) := by
        rw [h_norm, LinearMap.smul_apply, inner_smul_right]
        rfl

/-- The product, in the order `j = 1, …, m`, of the operators `rallisOnGood` on the target forms for
the twists `ϑ ^ j` and the indices `j`. The `j`-th one is the series of Rallis' formula for the
`j`-th lift at `ϑ ^ j`, which acts as a spherical Hecke operator. -/
def rallisProduct (ϑ : D.MFoldTwist) : End ℂ D.targetForms :=
  ((List.range D.m).map fun i : ℕ ↦ D.rallisOnGood (D.spaceY 0) (ϑ.pow (i + 1)) (i + 1)).prod

/-- The squared norm of the weighted chain of lifts. The triangle of lifts is a triangular array of
spaces of forms, with theta lifts `triangleLift` from position `(i, n)` to position `(i, n + 1)`;
the flag `false` picks one of the two triangles, the one whose characters are twisted by powers of
`ϑ`. The chain of its first `m` lifts from `Y₀`, each times its weight `triangleGLCard`
(`Exchange.weightedChain`), is taken on the target forms. Its Gram form is `κ ϑ` times a ratio of
group orders, divided by the `m`-th power of the number of matrices modulo `D.twistModulus ϑ 1`
indexed by `D.Y 1 × D.RowIndex`, times the form of `New.Data.rallisProduct`. Here
`triangleGLCard false ϑ n` is the order of the general linear group in the `n`-th place of the
triangle over the residue ring of its modulus, and `D.twistModulus ϑ 1` is the product of the chosen
places and the places of the twist. The statement `HasAbsUpToNormPower κ f` says
`‖κ ϑ‖² = C (normQ ϑ)^k (f ϑ)²` with `C` and `k` independent of `ϑ`; here `f` is the product over
`1 ≤ i < j ≤ m` of `quotientRatio i j`, the ratios of Hecke values of the quotient of the `j`-th and
`i`-th lift characters at `ϑ ^ (j - i)`. -/
lemma exists_inner_weightedChain_eq :
    ∃ κ : D.MFoldTwist → ℂ,
      D.HasAbsUpToNormPower κ (∏ i ∈ Ioc 0 D.m, ∏ j ∈ Ioc i D.m, D.quotientRatio i j) ∧
      ∀ (ϑ : D.MFoldTwist) (x y : D.targetForms),
        let u := Exchange.weightedChain (D.triangleGLCard false) (D.triangleLift false) ϑ 0 D.m
        inner ℂ (u x.val.val) (u y.val.val) =
          κ ϑ * (triangleGLCard false ϑ 0 * triangleGLCard false ϑ 1 ^ D.m /
            triangleGLCard false ϑ D.m) /
            Fintype.card (D.Y 1 × D.RowIndex → (D.twistModulus ϑ 1).ResidueRing) ^ D.m *
            inner ℂ x (D.rallisProduct ϑ y) := by
  -- By Rallis' formula the Gram form of the first lift in place `i` of the triangle, times
  -- `triangleGLCard false ϑ 0`, is a constant `C i` times the Gram form of the series
  -- `rallisFactor ϑ i` divided by `matrixCard ϑ`. The triangle multiplies these Gram forms.
  let matrixCard (ϑ : D.MFoldTwist) : ℂ := Fintype.card
    (D.Y 1 × D.RowIndex → (D.twistModulus ϑ 1).ResidueRing)
  let rallisFactor (ϑ : D.MFoldTwist) (i : ℕ) : End ℂ D.targetForms :=
    D.rallisOnGood (D.spaceY 0) (ϑ.pow (i + 1)) (i + 1)
  choose! C _ hC_sum using D.exists_hasSum_inner_triangleFirstLift false
  have h_first (i : ℕ) (hi : i < D.m) (ϑ : D.MFoldTwist) (x : D.principalForms (D.spaceY 0))
      (y : D.targetForms) :
      triangleGLCard false ϑ 0 *
          inner ℂ (D.triangleLift false ϑ i 0 (D.triangleNegEquiv false i x.val))
            (D.triangleLift false ϑ i 0 (D.triangleNegEquiv false i y.val.val)) =
        C i * inner ℂ x (((matrixCard ϑ)⁻¹ • rallisFactor ϑ i) y).val := by
    have h_series := D.hasSum_inner_rallisOperator (ϑ.pow (i + 1)) (i + 1) (D.spaceY 0) x y.val
    rw [(hC_sum i hi ϑ y.val x.val).unique
        ((h_series.div_const (matrixCard ϑ)).mul_left (C i)),
      div_eq_inv_mul, ← inner_smul_right]
    rfl
  obtain ⟨d, h_triangle, h_moduli⟩ := D.exists_isTriangle false
  obtain ⟨κ, hκ, h_inner⟩ := h_triangle.exists_inner_weightedChain_eq (h_moduli rfl)
    (fun ϑ i ↦ (matrixCard ϑ)⁻¹ • rallisFactor ϑ i) (fun i ↦ HasAbsUpToNormPower.const (C i))
      h_first D.m 0 (zero_add D.m)
  refine ⟨κ, hκ, fun ϑ x y ↦ ?_⟩
  have h_prod : ((List.range' 0 D.m).map fun i ↦ (matrixCard ϑ)⁻¹ • rallisFactor ϑ i).prod =
      (matrixCard ϑ)⁻¹ ^ D.m • D.rallisProduct ϑ := by
    simpa [rallisProduct, rallisFactor, Function.comp_def, ← List.range_eq_range'] using
      (List.smul_prod ((List.range D.m).map (rallisFactor ϑ)) (matrixCard ϑ)⁻¹).symm
  rw [div_eq_mul_inv _ (matrixCard ϑ ^ D.m), mul_assoc _ (matrixCard ϑ ^ D.m)⁻¹, ← inv_pow,
    ← inner_smul_right, ← LinearMap.smul_apply, ← h_prod]
  exact h_inner ϑ x.val y

/-- The Gram form of the chain. For an `m`-fold twist `ϑ` let `Θ = D.Θ ϑ` be the chain of lifts from
forms on `Y₀` to forms on `Y_m`, restricted to the target forms. There are numbers `c ϑ`, a real `C`
(possibly `0`) and an integer `k` such that for all `ϑ`
* `‖c ϑ‖ ^ 2 = C (Nm Q) ^ k (∏_{1 ≤ i < j ≤ m} quotientRatio i j ϑ) ^ 2` (`HasAbsUpToNormPower`),
* `⟪Θ x, Θ y⟫ = c ϑ * c_Q ^ m * ⟪x, R y⟫` for all target forms `x` and `y`.

Here `Q` is the set of places of `ϑ` and `Nm Q = ϑ.normQ` the product of their norms `q_w`. The
operator `R = D.rallisProduct ϑ` is the product over `1 ≤ j ≤ m` of the series of Rallis' formula
for the `j`-th lift at `ϑ ^ j`. The number `c_Q = (D.descentPair ϑ 1).twistFactor` is
`(Nm Q) ^ (r t) ∏_{w ∈ Q} ∏_{t < i ≤ t + r} (1 - q_w ^ (-i))`, and `quotientRatio i j ϑ` is the
product of the ratios of Hecke values of the quotient of the `j`-th and `i`-th lift characters at
`ϑ ^ (j - i)`. -/
theorem exists_inner_chain_eq :
    ∃ c : D.MFoldTwist → ℂ,
      D.HasAbsUpToNormPower c (∏ i ∈ Ioc 0 D.m, ∏ j ∈ Ioc i D.m, D.quotientRatio i j) ∧
      ∀ (ϑ : D.MFoldTwist) (x y : D.targetForms), inner ℂ (D.Θ ϑ x) (D.Θ ϑ y) =
        c ϑ * (D.descentPair ϑ 1).twistFactor ^ D.m * inner ℂ x (D.rallisProduct ϑ y) := by
  obtain ⟨κ, hκ, h_weighted⟩ := D.exists_inner_weightedChain_eq
  -- The index of the last level is `γ * N ^ l * gramFactor ^ m * N_m / (N_0 * N_1 ^ m)`, with `N`
  -- the norm of the modulus and `N_n` the orders `triangleGLCard`.
  obtain ⟨γ, l, h_index⟩ := D.exists_stdLevelIndex_lastLevel_eq
  simp only [Fintype.card_eq_nat_card] at h_index
  -- The constant is `κ * indexFactor`; as `indexFactor` is a fixed number times a power of the norm
  -- of the modulus, `HasAbsUpToNormPower indexFactor 1` holds.
  let indexConst : ℂ :=
    Fintype.card (WeylIndex (D.Y D.m) D.columnsY) * γ * (D.descentPair .one 1).chosenFactor ^ D.m
  let indexFactor (ϑ : D.MFoldTwist) : ℂ :=
    indexConst * Nat.card (D.twistModulus ϑ 0).ResidueRing ^ l
  have h_index_factor : D.HasAbsUpToNormPower indexFactor 1 :=
    .of_norm_sq_eq_mul_card_zpow 0 (‖indexConst‖ ^ 2) (l * 2) fun ϑ ↦ by
      simp [indexFactor, mul_pow, zpow_mul]
  refine ⟨κ * indexFactor, by simpa using hκ.mul h_index_factor, fun ϑ x y ↦ ?_⟩
  let matrixCard : ℂ := Fintype.card (D.Y 1 × D.RowIndex → (D.twistModulus ϑ 1).ResidueRing)
  -- On the target the inner product is the index times a dimension times the Petersson product.
  have h_chain : inner ℂ (D.Θ ϑ x) (D.Θ ϑ y) =
      stdLevelIndex (lastLevel ϑ.toTameChar) * Fintype.card (WeylIndex (D.Y D.m) D.columnsY) *
        (κ ϑ * (triangleGLCard false ϑ 0 * triangleGLCard false ϑ 1 ^ D.m /
          triangleGLCard false ϑ D.m) / matrixCard ^ D.m * inner ℂ x (D.rallisProduct ϑ y)) := by
    rw [← h_weighted ϑ x y]
    exact D.inner_lowerChainAtLevel ϑ x.val y.val
  -- The chosen places and the ranks do not depend on `ϑ`.
  have h_factor : (D.descentPair ϑ 1).gramFactor / matrixCard =
      (D.descentPair .one 1).chosenFactor * (D.descentPair ϑ 1).twistFactor :=
    (D.descentPair ϑ 1).gramFactor_div_card
  -- The orders `triangleGLCard` cancel.
  rw [h_chain, h_index, (div_eq_iff (NeZero.out : matrixCard ≠ 0)).1 h_factor]
  simp [indexFactor, indexConst, matrixCard, mul_pow, field]

/-- Let `ij = (i, j)` be a pair with `1 ≤ i < j ≤ m` and `χ_j = D.untwistedLiftChar j` the character
of the `j`-th lift without twist. Then `quotientRatio i j`, the product of the ratios of Hecke
values of `χ_j / χ_i`, is a ramified ratio: for some fixed `1 ≤ n ≤ m` and some ramified pair (a
character ramified at the chosen places and an integer `z`, the ratios taken at `1, …, z`), its
value at a twist `ϑ` is the product of the ratios of Hecke values of that pair at `ϑ ^ n`. -/
lemma isRamifiedRatio_of_mem_sigma {ij : Σ _ : ℕ, ℕ}
    (hij : ij ∈ (Ioc 0 D.m).sigma fun i : ℕ ↦ Ioc i D.m) :
    D.IsRamifiedRatio (D.quotientRatio ij.1 ij.2) := by
  obtain ⟨h_lt, h_le⟩ : ij.1 < ij.2 ∧ ij.2 ≤ D.m := mem_Ioc.1 (mem_sigma.1 hij).2
  exact isRamifiedRatio_quotientRatio h_lt h_le

/-- There are at most `m²` pairs `1 ≤ i < j ≤ m`. -/
lemma card_sigma_Ioc_le (m : ℕ) : #((Ioc 0 m).sigma fun i : ℕ ↦ Ioc i m) ≤ m * m := by
  simpa using sum_le_card_nsmul (Ioc 0 m) (fun i ↦ #(Ioc i m)) m (by simp)

/-- The chain volume is the product of the single-lift volumes times the target dimension power
of a scalar norm. For any family of twists with small ratios the normalized norm costs at most
`b` in height. -/
theorem exists_chainDeterminant_eq_norm_pow_mul_prod :
    ∃ c : D.MFoldTwist → ℂ,
      (∀ {θ : PrimePadicIso → D.MFoldTwist}, D.HasSmallRatios θ →
        HeightLe D.b fun ι ↦ (‖c 1 / c (θ ι)‖ : ℂ)) ∧
      ∀ ϑ, D.chainDeterminant ϑ =
        (‖c ϑ‖ : ℂ) ^ D.targetDim * ∏ j ∈ Icc 1 D.m, D.liftDeterminant ϑ j := by
  obtain ⟨c, hc, h_gram⟩ := D.exists_inner_chain_eq
  choose A hA h_lift using fun i : Fin D.m ↦ D.exists_normDet_goodLift_sq_eq ⟨i + 1, by simp⟩
  have hA_prod : ∏ i, A i ≠ 0 := prod_ne_zero_iff.2 fun i _ ↦ hA i
  let a : D.MFoldTwist → ℂ := c * fun _ ↦ (∏ i, A i)⁻¹
  have ha : D.HasAbsUpToNormPower a
      (∏ ij ∈ (Ioc 0 D.m).sigma (fun i : ℕ ↦ Ioc i D.m), D.quotientRatio ij.1 ij.2) := by
    simpa only [a, prod_sigma', mul_one] using hc.mul (HasAbsUpToNormPower.const (D := D) (∏ i, A i)⁻¹)
  refine ⟨a, fun {θ} hθ ↦ ?_, fun ϑ ↦ ?_⟩
  · have h := ha.heightLe_norm_div hθ fun x hx ↦ D.isRamifiedRatio_of_mem_sigma hx
    refine h.mono (le_trans ?_ (D.le_of_hasLogBound : D.m * D.m * (D.t * D.x₁) ≤ D.b))
      fun _ ↦ le_rfl
    grw [card_sigma_Ioc_le, Nat.cast_mul]
  · let cQ : ℂ := (D.descentPair ϑ 1).twistFactor
    let rallisDet (i : ℕ) : ℂ := (D.rallisOnGood (D.spaceY 0) (ϑ.pow (i + 1)) (i + 1)).det
    -- The powers of `ϑ` have the same modulus `Q`, hence the same `c_Q`.
    have h_liftDet (i : Fin D.m) :
        D.liftDeterminant ϑ (i + 1) = (A i * cQ) ^ D.targetDim * rallisDet i :=
      h_lift i (ϑ.pow (i + 1))
    have h_det : (D.rallisProduct ϑ).det = ∏ i : Fin D.m, rallisDet i := by
      simp [rallisProduct, rallisDet, map_list_prod, Function.comp_def, prod_range,
        ← List.prod_toFinset _ List.nodup_range, List.toFinset_range]
    have h_prod : ∏ j ∈ Icc 1 D.m, D.liftDeterminant ϑ j = ∏ i : Fin D.m,
      D.liftDeterminant ϑ (i + 1) := by
      rw [← prod_range fun i ↦ D.liftDeterminant ϑ (i + 1), range_eq_Ico, prod_Ico_add',
        zero_add, Ico_add_one_right_eq_Icc]
    have h_eq : D.chainDeterminant ϑ =
        (c ϑ * (∏ i, A i)⁻¹) ^ D.targetDim * ∏ j ∈ Icc 1 D.m, D.liftDeterminant ϑ j := by
      calc D.chainDeterminant ϑ = (c ϑ * cQ ^ D.m) ^ D.targetDim * ∏ i : Fin D.m, rallisDet i := by
              rw [← h_det]
              exact normDet_sq_eq_pow_mul_det (D.Θ ϑ) (D.rallisProduct ϑ) (h_gram ϑ)
        _ = (c ϑ * (∏ i, A i)⁻¹) ^ D.targetDim * ∏ i, ((A i * cQ) ^ D.targetDim * rallisDet i) := by
          simp_rw [prod_mul_distrib, prod_pow, prod_mul_distrib, Fin.prod_const]
          rw [← mul_assoc, ← mul_pow]
          field_simp
        _ = _ := by simp_rw [h_prod, h_liftDet]
    simpa [a, chainDeterminant, liftDeterminant] using congrArg (fun z : ℂ ↦ (‖z‖ : ℂ)) h_eq

open scoped Classical in
/-- Let `f` be a representation of the group algebra of `D.chosenGL`, the product of the finite
general linear groups at the chosen places, on a complex inner product space `U`. Let `c` be a good
tuple family: one of the finitely many admissible labellings of the chosen places by polynomials
over their residue fields. Then the range of the idempotent `tupleIdem D.RowIndex c` under `f` lies
in the range of `New.Data.e₀`, the sum of these idempotents over all good tuple families. -/
lemma range_tupleIdem_le {f : MonoidAlgebra ℂ D.chosenGL →ₐ[ℂ] End ℂ U}
    {c : (x : Σ i : Fin 2, D.ChosenPlace i) → Polynomial (ResField (D.chosenPlace x))}
    (hc : c ∈ D.goodTupleFamilies) :
    (f (tupleIdem D.RowIndex c)).range ≤ (f D.e₀).range := by
  -- the idempotent of `c` is its product with the central idempotent `e₀`
  have h_mul : D.e₀ * tupleIdem D.RowIndex c = tupleIdem D.RowIndex c := by
    rw [← (D.isCentralProj_e₀.2 : IsClassFunction D.e₀.coeff).commute]
    exact tupleIdem_orthogonal.mul_sum_of_mem hc
  rw [← h_mul, map_mul]
  exact range_comp_le_range _ _

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.univ in
/-- The theta lift `D.singleLift ϑ j`, for a tame character `ϑ` and `1 ≤ j ≤ m`, commutes with the
group algebra of `D.chosenGL`, the product of the groups `GL_r` over the residue fields of the
chosen places. An element `x` acts through `principalRep` on `principalForms`, the forms on the
hermitian space `W_j = D.spaceW j` fixed by the principal level at the chosen places. It acts by
`groupAlgAction` on the forms on the larger space of `D.descentPair ϑ j`, the datum of the lift. -/
lemma singleLift_asAlgebraHom {ϑ : D.TameChar} {j : D.LiftIndex} {x : MonoidAlgebra ℂ D.chosenGL}
    (y : D.principalForms (D.spaceW j)) :
    D.singleLift ϑ j ((D.principalRep (D.spaceW j)).asAlgebraHom x y) =
      (D.descentPair ϑ j).groupAlgAction x (D.singleLift ϑ j y) := by
  -- Both sides are sums over the group, and `singleLift` commutes with each group element.
  have h_sum : (D.descentPair ϑ j).groupAlgAction x (D.singleLift ϑ j y) =
      ∑ g : D.chosenGL, x.coeff g • (D.descentPair ϑ j).formAction g (D.singleLift ϑ j y) :=
    -- A term, as `rw` does not see that `D.chosenGL` is the group acting on the forms.
    (LinearMap.congr_fun (asAlgebraHom_eq_sum (D.descentPair ϑ j).formAction) _).trans
      (LinearMap.sum_apply ..)
  rw [h_sum, asAlgebraHom_eq_sum]
  simp [singleLift_principalRep]

open scoped Classical in
/-- Let `ϑ` be a tame character and `1 ≤ j ≤ m`. The range of `D.goodLift ϑ j`, the lift
`singleLift` restricted to the good forms on `W_j = D.spaceW j`, is spanned by the lifts of good
eigenforms whose lifts lie in the range of the idempotent of a good tuple family. A good tuple
family `c` is one of the finitely many admissible labellings of the chosen places by polynomials
over their residue fields. `tupleIdem D.RowIndex c` is the tensor product of the idempotents
labelled by these polynomials in the group algebra of the finite groups at the chosen places, which
acts on forms by `groupAlgAction`. A good form is a form of principal level at the chosen places
that lies in the image of `e₀`, the sum of these idempotents over all good tuple families.
Precisely, let a subspace `N` of the forms `FormV` on the larger space of the pair
`D.descentPair ϑ j` contain the lift `singleLift ϑ j y` for every good form `y` in `eigenPart p`
whose lift lies in the range of some `tupleIdem D.RowIndex c`. Here `eigenPart p` is the joint
eigenspace of the Hecke operators for a system `p`. Then `N` contains the range of
`goodLift ϑ j`. -/
lemma range_goodLift_le {ϑ : D.TameChar} {j : D.LiftIndex}
    {N : Submodule ℂ (D.descentPair ϑ j).FormV}
    (h_eigen : ∀ p : FinPlace D.E × ℕ → ℂ,
      ∀ y ∈ D.goodForms (D.spaceW j) ⊓ D.eigenPart (D.spaceW j) p, ∀ c ∈ D.goodTupleFamilies,
      D.singleLift ϑ j y ∈ (DescentPair.groupAlgAction (D.descentPair ϑ j)
        (tupleIdem D.RowIndex c)).range →
      D.singleLift ϑ j y ∈ N) :
    (D.goodLift ϑ j).range ≤ N := by
  -- Good forms are the values of `e₀`, and Hecke eigenforms span; so it suffices to lift `e₀ y`
  -- with `y` an eigenform. Split `e₀` into the idempotents of the good tuples `c`: each piece of
  -- `y` is a good eigenform, and its lift lies in the range of the same idempotent
  -- (`singleLift_asAlgebraHom`).
  suffices h_top_le : ⊤ ≤ N.comap
      (D.singleLift ϑ j ∘ₗ (D.principalRep (D.spaceW j)).asAlgebraHom D.e₀) by
    rintro _ ⟨⟨_, y, rfl⟩, rfl⟩
    exact h_top_le (Submodule.mem_top (x := y))
  rw [← D.iSup_eigenPart_eq_top]
  refine iSup_le fun p y hy ↦ ?_
  change D.singleLift ϑ j ((D.principalRep (D.spaceW j)).asAlgebraHom D.e₀ y) ∈ N
  simp only [e₀, map_sum, LinearMap.coe_sum, Finset.sum_apply]
  refine sum_mem fun c hc ↦ ?_
  -- The piece of `y` at `c` is a good eigenform.
  refine h_eigen p _ ⟨D.range_tupleIdem_le hc ⟨y, rfl⟩, principalRep_mem_eigenPart _ _ hy _⟩ c hc ?_
  exact ⟨D.singleLift ϑ j y, (D.singleLift_asAlgebraHom y).symm⟩

end

end New.Data

end
