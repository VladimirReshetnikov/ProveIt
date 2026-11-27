import New.OneLift.ComparisonOperator.DeterminantProducts
import New.OneLift.ComparisonOperator.GluedLattices

/-!
# The polynomial map ζ, the datum Ψ^add and the series Υ; norm, degree and denominator of ζ

Fix admissible data `D`, a tame character `ϑ` and an index `1 ≤ j ≤ m`. Write `E^n` for the standard
definite space of rank `n`, V″ for the one on `New.Data.FirstFactorIndex` and
W^add = E^{3m−j} ⊕ W♭ ⊕ E^{3m} for the one on `New.Data.AddedIndex`. Throughout, k = `D.k`,
m = `D.m`, M = `D.M`, and W_j is the space on `D.RowIndex` with r₊ = `D.posRank j` = k + j − 1 plus
signs. This file defines the constant rows 𝖼, the datum Ψ^add and the series Υ, which is built from
theta kernels of definite spaces. It also defines the polynomial map ζ to the Weyl module of μ⁺ with
P_V = P_{ζ(z)}(X). Here P_V has one determinant det(𝖼; X z) for each column of μ⁺, with variables X
in the positive basis vectors of W_j and variables z in W^add. This file bounds the norm, the degree
and the denominator of ζ.

## Main definitions and results

* `New.HasWeightNormSqLe`, `New.HasWeightNormSqLeIf`: "F has weight κ and squared norm at most b",
  outright or under a condition. Under finite products the weights add and the bounds multiply.
* `New.Data.constantRows`, `New.Data.stackedDetProdCoords`: the matrices 𝖼 of 2m constant rows, one
  for each column of μ⁺ at each infinite place (`New.Data.DetIndex`), and the coordinates of ζ.
* `New.Data.addedDatum`, `New.Data.leftSideSeries`: the datum Ψ^add on W^add and the series Υ.
* `New.Data.toPoly_stackedDetProdCoords`, `New.Data.weylNormSq_comp_eval_stackedDetProdCoords_le`:
  P_V is the polynomial of ζ, and when the entries of Y and the values of z are small, the squared
  norm of ζ(z) is bounded.
* `New.Data.exists_isHomogeneousOverEntries_smul_stackedDetProdCoords`: ζ is homogeneous of one
  degree `d`, and one integer `H ≤ (d ^ d) ^ 3` clears its denominators.

Notions from other files:
* `New.toPoly`, `New.weylNormSq`: the polynomial of a coordinate vector of weight κ, and the squared
  norm of the vector for the Gram matrix of κ. Here `κ τ h` counts the columns of height `h` at `τ`.
* `New.Data.DetIndex`: the columns of μ⁺ at the place τ. The number of those of height h < r₊ is
  `(untwistedDescentPair j).colsPlus τ h`, and Δ′ = `D.reducedHalfGap` have height r₊.
* `New.Data.FirstFactorIndex`: the indices of W_j, (E^j)⁻, E^{3m−j} and W♭ = E^{6m+1}.
* `New.Data.ChoiceIndex`: the choices, each a matrix Λ modulo ϖ² with a class h♭ of U(W♭) and rows
  for the columns of height r₊ (`New.Data.RowChoice`).
* `New.Data.TameChar`, `New.Data.twistModulus`: a character `ϑ` of U(1)(𝔸) of weight 0 with tame
  part on a finite set Q = `ϑ.Q` of places, and the moduli ϖ^c Q.

## Relation to the literature

See `New.OneLift.ComparisonOperator.FirstFactors` for related work.
-/

noncomputable section

/-! ## Norm bounds for products of semi-invariants -/

section SemiInvariantNorm

variable {Φ n : Type} [Fintype Φ] [DecidableEq Φ] [Fintype n] [DecidableEq n]

/-- `F` is the polynomial (`toPoly`) of a coordinate vector `ξ` of weight `κ` whose squared norm for
the Gram matrix of `κ` (`weylNormSq`) is at most `b`. -/
def New.HasWeightNormSqLe (κ : Φ → ℕ → ℕ) (F : MatrixPoly (Σ _ : Φ, n) ℂ) (b : ℝ) : Prop :=
  ∃ ξ : WeylIndex n κ → ℂ, toPoly (fun _ : Φ ↦ n) κ ξ = F ∧ weylNormSq ξ ≤ b

/-- A bound on the squared norm of a coordinate vector is nonnegative. -/
lemma New.HasWeightNormSqLe.nonneg {κ : Φ → ℕ → ℕ} {F : MatrixPoly (Σ _ : Φ, n) ℂ} {b : ℝ}
    (hF : HasWeightNormSqLe κ F b) : 0 ≤ b := by
  obtain ⟨ξ, -, hξ_le⟩ := hF
  exact (weylNormSq_nonneg ξ).trans hξ_le

lemma New.HasWeightNormSqLe.one :
    HasWeightNormSqLe (0 : Φ → ℕ → ℕ) (1 : MatrixPoly (Σ _ : Φ, n) ℂ) 1 := by
  -- The coordinate vector is evaluation at `0`; its polynomial is an empty product of minors.
  have h_kernel : weylKernel (fun _ : Φ ↦ n) 0 (0 : (Σ _ : Φ, n) × ℕ → ℂ) = 1 := by
    simp [weylKernel, highestPoly, tableauPoly]
  refine ⟨weylEval (fun _ ↦ n) 0 0, by rw [toPoly_weylEval, h_kernel], ?_⟩
  simp [weylNormSq, GL.star_weylEval, h_kernel]

/-- If `F` is the polynomial of a vector of the Weyl module of weight `κ` with squared norm for the
Gram matrix at most `b` (`HasWeightNormSqLe`), and likewise `G` for `κ'` and `c`, then `F * G` has
weight `κ + κ'` and squared norm at most `b * c`. -/
lemma New.HasWeightNormSqLe.mul {κ κ' : Φ → ℕ → ℕ} {F G : MatrixPoly (Σ _ : Φ, n) ℂ} {b c : ℝ}
    (hF : HasWeightNormSqLe κ F b) (hG : HasWeightNormSqLe κ' G c) :
    HasWeightNormSqLe (κ + κ') (F * G) (b * c) := by
  obtain ⟨ξ, hξ, hξ_le⟩ := hF
  obtain ⟨η, hη, hη_le⟩ := hG
  -- The product of two semi-invariants is a semi-invariant of the sum of the weights.
  have hFG_mem : F * G ∈ nablaFamily ℂ (fun _ : Φ ↦ n) (κ + κ') := by
    rw [nablaFamily, diagramWeight_add]
    exact SetLike.mul_mem_graded (range_toPoly.le ⟨ξ, hξ⟩) (range_toPoly.le ⟨η, hη⟩)
  obtain ⟨ζ, hζ : toPoly (fun _ ↦ n) (κ + κ') ζ = F * G⟩ := range_toPoly.ge hFG_mem
  have hζ_le : weylNormSq ζ ≤ weylNormSq ξ * weylNormSq η :=
    weylNormSq_le_mul_of_toPoly_eq (by rw [hζ, hξ, hη])
  exact ⟨ζ, hζ, hζ_le.trans
    (mul_le_mul hξ_le hη_le (weylNormSq_nonneg η) ((weylNormSq_nonneg ξ).trans hξ_le))⟩

/-- Under a finite product the weights add and the bounds on the squared norm multiply. -/
lemma New.HasWeightNormSqLe.prod {ι : Type*} {s : Finset ι} {κ : ι → Φ → ℕ → ℕ}
    {F : ι → MatrixPoly (Σ _ : Φ, n) ℂ} {b : ι → ℝ}
    (hF : ∀ i ∈ s, HasWeightNormSqLe (κ i) (F i) (b i)) :
    HasWeightNormSqLe (∑ i ∈ s, κ i) (∏ i ∈ s, F i) (∏ i ∈ s, b i) := by
  induction s using Finset.cons_induction with
  | empty => simpa using HasWeightNormSqLe.one
  | cons i s hi ih => simpa using (hF i (by simp)).mul (ih fun j hj ↦ hF j (by simp [hj]))

/-- `F` is the polynomial of a coordinate vector `ξ` of weight `κ`, and if the condition `p` holds,
the squared norm of `ξ` is at most `b`. -/
def New.HasWeightNormSqLeIf (p : Prop) (κ : Φ → ℕ → ℕ) (F : MatrixPoly (Σ _ : Φ, n) ℂ) (b : ℝ) :
    Prop :=
  ∃ ξ : WeylIndex n κ → ℂ, toPoly (fun _ : Φ ↦ n) κ ξ = F ∧ (p → weylNormSq ξ ≤ b)

/-- `F` has weight `κ` and, under `p`, squared norm at most `b` exactly when it has weight `κ` and
squared norm at most some `c` with `c ≤ b` under `p`. -/
lemma New.hasWeightNormSqLeIf_iff {p : Prop} {κ : Φ → ℕ → ℕ} {F : MatrixPoly (Σ _ : Φ, n) ℂ}
    {b : ℝ} :
    HasWeightNormSqLeIf p κ F b ↔ ∃ c : ℝ, HasWeightNormSqLe κ F c ∧ (p → c ≤ b) :=
  ⟨fun ⟨ξ, hξ, hξ_le⟩ ↦ ⟨weylNormSq ξ, ⟨ξ, hξ, le_rfl⟩, hξ_le⟩,
    fun ⟨_, ⟨ξ, hξ, hξ_le⟩, hc_le⟩ ↦ ⟨ξ, hξ, fun hp ↦ hξ_le.trans (hc_le hp)⟩⟩

/-- If each `F i` has weight `κ i` and, under `p`, squared norm at most `b i`, then the product has
weight `∑ κ i` and, under `p`, squared norm at most `∏ b i`. -/
lemma New.HasWeightNormSqLeIf.prod {p : Prop} {ι : Type*} {s : Finset ι} {κ : ι → Φ → ℕ → ℕ}
    {F : ι → MatrixPoly (Σ _ : Φ, n) ℂ} {b : ι → ℝ}
    (hF : ∀ i ∈ s, HasWeightNormSqLeIf p (κ i) (F i) (b i)) :
    HasWeightNormSqLeIf p (∑ i ∈ s, κ i) (∏ i ∈ s, F i) (∏ i ∈ s, b i) := by
  -- Each factor has an unconditional bound `c i`, and `c i ≤ b i` under `p`.
  choose! c hc hc_le using fun i hi ↦ hasWeightNormSqLeIf_iff.1 (hF i hi)
  refine hasWeightNormSqLeIf_iff.2 ⟨∏ i ∈ s, c i, HasWeightNormSqLe.prod hc, fun hp ↦ ?_⟩
  exact Finset.prod_le_prod₀ (fun i hi ↦ (hc i hi).nonneg) fun i hi ↦ hc_le i hi hp

open Matrix in
/-- For the weight with one column of height `h < card N` at `τ`, the kernel `weylKernel` at `y`
(the highest weight polynomial at `yᵀ x`) is the leading `h × h` minor of `yᵀ x` in block `τ`. -/
lemma New.eval_weylKernel_single_eq_det {N : Type} [Fintype N] [DecidableEq N] (τ : Φ) {h : ℕ}
    (h_lt : h < Fintype.card N) (y x : (Σ _ : Φ, N) × ℕ → ℂ) :
    (weylKernel (fun _ : Φ ↦ N) (Pi.single τ (Pi.single h 1)) y).eval x =
      (of fun a b : Fin h ↦ ∑ u : N, y (⟨τ, u⟩, a) * x (⟨τ, u⟩, b)).det := by
  -- Of the leading minors in `highestPoly`, only the one of size `h` at `τ` has nonzero exponent.
  simp [weylKernel, highestPoly, tableauPoly, minor, det_apply, rowSubst,
    Fin.val_eq_val _ ⟨h, h_lt⟩, Pi.single_apply, ite_apply, apply_ite]

open Matrix in
/-- Let a function `F` of `h` columns be the sum, over the `h`-subsets `S` of `N`, of the minor on
`S` times the value of `F` at the unit columns on `S`. Take the weight whose diagram is one column
of height `h < card N` at the place `τ` in `Φ` and is empty at the other places; `WeylIndex` indexes
a basis of its Weyl module. Then `F` is the polynomial `toPoly ξ` = ∑ (G ξ)ᵢ bᵢ of a vector `ξ`,
where G is the Gram matrix and the bᵢ are the basis products of minors, and the squared norm
`weylNormSq ξ` = ξ* G ξ is the sum of the squared moduli of these values. -/
lemma New.exists_toPoly_single_eq {N : Type} [Fintype N] [LinearOrder N] [DecidableEq N]
    (τ : Φ) {h : ℕ} (h_lt : h < Fintype.card N) (F : Matrix N (Fin h) ℂ → ℂ)
    (h_expand : ∀ X : Matrix N (Fin h) ℂ, F X = ∑ S : Set.powersetCard N h,
      (X.submatrix (enumSubset S) id).det * F ((1 : Matrix N N ℂ).submatrix id (enumSubset S))) :
    ∃ ξ : WeylIndex N (Pi.single τ (Pi.single h 1) : Φ → ℕ → ℕ) → ℂ,
      (∀ x : (Σ _ : Φ, N) × ℕ → ℂ,
        (toPoly (fun _ : Φ ↦ N) (Pi.single τ (Pi.single h 1)) ξ).eval x =
          F (.of fun (u : N) (a : Fin h) ↦ x (⟨τ, u⟩, a))) ∧
      weylNormSq ξ = ∑ S : Set.powersetCard N h,
        ‖F ((1 : Matrix N N ℂ).submatrix id (enumSubset S))‖ ^ 2 := by
  -- `unit S` is the array of the unit columns on `S`; evaluation at it has the minor on `S` as its
  -- polynomial. The vector `ξ` combines these evaluations with the values `c S` of `F`.
  let κ : Φ → ℕ → ℕ := Pi.single τ (Pi.single h 1)
  let unit (S : Set.powersetCard N h) : (Σ _ : Φ, N) × ℕ → ℂ := fun (⟨_, u⟩, a) ↦
    if ha : a < h then (1 : Matrix N N ℂ) u (enumSubset S ⟨a, ha⟩) else 0
  have h_minor (S : Set.powersetCard N h) (x : (Σ _ : Φ, N) × ℕ → ℂ) :
      (weylKernel (fun _ ↦ N) κ (unit S)).eval x =
        ((of fun u (a : Fin h) ↦ x (⟨τ, u⟩, a)).submatrix (enumSubset S) id).det := by
    rw [eval_weylKernel_single_eq_det τ h_lt]
    simp [unit, one_apply, Matrix.submatrix]
  let c (S : Set.powersetCard N h) : ℂ := F ((1 : Matrix N N ℂ).submatrix id (enumSubset S))
  let ξ : WeylIndex N κ → ℂ := ∑ S, c S • weylEval (fun _ ↦ N) κ (unit S)
  have h_eval (x : (Σ _ : Φ, N) × ℕ → ℂ) :
      (toPoly (fun _ ↦ N) κ ξ).eval x = F (.of fun u a ↦ x (⟨τ, u⟩, a)) := by
    rw [h_expand]
    simp [ξ, c, toPoly_weylEval, MvPolynomial.smul_eval, h_minor, mul_comm]
  refine ⟨ξ, h_eval, ?_⟩
  -- The pairing of `ξ` with evaluation at `unit S` is the value `c S` of its polynomial there.
  have h_pair (S : Set.powersetCard N h) :
      weylEval (fun _ ↦ N) κ (unit S) ⬝ᵥ (weylGram (fun _ ↦ N) κ).map (↑) *ᵥ ξ = c S := by
    simp [← GL.eval_toPoly, h_eval, c, unit, Matrix.submatrix, Matrix.one_apply]
  have h_unit (S : Set.powersetCard N h) : star (unit S) = unit S := by
    ext ⟨⟨τ', u⟩, a⟩
    simp [unit, one_apply, apply_dite (starRingEnd ℂ), apply_ite (starRingEnd ℂ)]
  have h_star : star ξ = ∑ S, star (c S) • weylEval (fun _ ↦ N) κ (unit S) := by
    simp_rw [ξ, star_sum, star_smul, GL.star_weylEval, h_unit]
  have h_sum : star ξ ⬝ᵥ (weylGram (fun _ ↦ N) κ).map (↑) *ᵥ ξ = ∑ S, star (c S) * c S := by
    simp_rw [h_star, sum_dotProduct, smul_dotProduct, h_pair, smul_eq_mul]
  rw [weylNormSq, h_sum]
  simp [c, Complex.conj_mul', ← Complex.ofReal_pow]

open Matrix in
/-- Take the weight whose diagram is one column of height `h < card N` at the place `τ` in `Φ` and
is empty at the other places; `WeylIndex` indexes a basis of its Weyl module. The determinant of the
matrix `((0; X) | Z)`, with variables `X` in `h` columns and with columns indexed through `e`, is
the polynomial `toPoly ξ` = ∑ (G ξ)ᵢ bᵢ of a vector `ξ`, where G is the Gram matrix and the bᵢ are
the basis products of minors. The squared norm `weylNormSq ξ` = ξ* G ξ is at most the product of the
squared lengths of the columns of `Z`. -/
lemma New.exists_toPoly_eq_det_and_weylNormSq_le {a N c : Type} [Fintype a] [DecidableEq a]
    [Fintype N] [DecidableEq N] [Fintype c] (τ : Φ) {h : ℕ} (h_lt : h < Fintype.card N)
    (e : a ⊕ N ≃ Fin h ⊕ c) (Z : Matrix (a ⊕ N) c ℂ) :
    ∃ ξ : WeylIndex N (Pi.single τ (Pi.single h 1) : Φ → ℕ → ℕ) → ℂ,
      (∀ x : (Σ _ : Φ, N) × ℕ → ℂ,
        (toPoly (fun _ : Φ ↦ N) (Pi.single τ (Pi.single h 1)) ξ).eval x =
          (((fromRows 0 (of fun (u : N) (b : Fin h) ↦ x (⟨τ, u⟩, b))).fromCols Z).submatrix
            id e).det) ∧
      weylNormSq ξ ≤ ∏ b : c, ∑ x : a ⊕ N, ‖Z x b‖ ^ 2 := by
  -- Expand along the first `h` columns. Up to sign the coordinates are the complementary minors;
  -- the Cauchy–Binet formula and Hadamard's inequality bound the sum of their squared moduli.
  let _ : LinearOrder N := .lift' (Fintype.equivFin N) (Equiv.injective _)
  let one : Matrix (a ⊕ N) (a ⊕ N) ℂ := 1
  let F (X : Matrix N (Fin h) ℂ) : ℂ :=
    ((fromCols (one.submatrix id Sum.inr * X) Z).submatrix id e).det
  have h_rows (X : Matrix N (Fin h) ℂ) : one.submatrix id Sum.inr * X = fromRows 0 X := by
    ext (u | u) b <;> simp [one, mul_apply, one_apply]
  have h_unit (S : Set.powersetCard N h) :
      one.submatrix id Sum.inr * (1 : Matrix N N ℂ).submatrix id (enumSubset S) =
        one.submatrix id (Sum.inr ∘ enumSubset S) := by
    ext
    simp [mul_apply, one_apply]
  have h_expand (X : Matrix N (Fin h) ℂ) : F X = ∑ S : Set.powersetCard N h,
      (X.submatrix (enumSubset S) id).det *
        F ((1 : Matrix N N ℂ).submatrix id (enumSubset S)) := by
    simp only [F, h_unit]
    exact det_fromCols_eq_sum_minors e Sum.inr X Z
  obtain ⟨ξ, h_eval, h_norm⟩ := exists_toPoly_single_eq τ h_lt F h_expand
  refine ⟨ξ, fun x ↦ by simp only [h_eval, F, h_rows], ?_⟩
  calc weylNormSq ξ = ∑ S : Set.powersetCard N h,
        ‖((fromCols (one.submatrix id (Sum.inr ∘ enumSubset S)) Z).submatrix id e).det‖ ^ 2 := by
        simp only [h_norm, F, h_unit]
    _ ≤ ∏ b, ∑ x, ‖Z x b‖ ^ 2 := sum_norm_det_fromCols_sq_le e .inr Z

end SemiInvariantNorm

namespace New.Data

/-!
## Index sets, constant rows, datum and series

`modKernelStdSpace S a b 𝔪 Ψ P` is the theta kernel of a space `S` and a standard definite space,
with characters `a`, `b`, a function `Ψ` on matrices modulo `𝔪` and a polynomial `P`.
`New.stdClassSum K` is the class sum of level `K` on a standard definite space. `New.inclMatrix` is
the matrix of a map of index sets.
-/

section LineDefs

open Matrix Rows WeilData Fintype U Sum Equiv

variable {P : Parameters} {D : Data P} (ϑ : D.TameChar) (j : D.LiftIndex)

/-- The chosen representative h♭ in U(W♭)(𝔸_f) of the class in `i`. -/
abbrev RowChoice.classRep (i : D.RowChoice) : Gf D.E D.FlatIndex := i.1.out

/-- The row indices chosen in `i`: `i.rows τ k` is the k-th list of 2m rows at the place τ. -/
abbrev RowChoice.rows (i : D.RowChoice) :
    D.Φ → Fin D.reducedHalfGap → Fin (2 * D.m) → D.FlatIndex := i.2

/-- The matrix Λ modulo ϖ² of the choice `i`. -/
abbrev ChoiceIndex.matrix {j : D.LiftIndex} (i : ChoiceIndex j) :
    Matrix D.CarrierIndex (FirstFactorIndex j) (D.untwistedModulus 2).ResidueRing := i.1

/-- The class h♭ and the rows of the choice `i`. -/
abbrev ChoiceIndex.rowChoice {j : D.LiftIndex} (i : ChoiceIndex j) : D.RowChoice := i.2

/-- The index set of the definite space W^add = E^{3m−j} ⊕ W♭ ⊕ E^{3m}, with W♭ = E^{6m+1}. -/
abbrev AddedIndex : Type := Fin (2 * D.m + (D.m - j)) ⊕ D.FlatIndex ⊕ D.CarrierIndex

/-- The two groupings of the summands of W: as W_j ⊕ (E^j)⁻ ⊕ W^add, and as E^{3m} ⊕ W′, where
E^{3m} is on `D.CarrierIndex` and W′ = W_j ⊕ (E^j)⁻ ⊕ E^{3m−j} ⊕ W♭ is on `D.FirstFactorIndex j`. -/
def regroupEquiv : D.RowIndex ⊕ Fin j ⊕ AddedIndex j ≃ D.CarrierIndex ⊕ FirstFactorIndex j :=
  -- the inverse moves `D.CarrierIndex` to the end and reassociates
  ((sumComm ..).trans ((sumAssoc ..).trans
    ((sumAssoc ..).trans (sumCongr (Equiv.refl D.RowIndex) (sumAssoc ..))))).symm

/-- A bijection, chosen from equality of cardinalities, from 2m indices together with those of V″
to `D.posRank j = k + j − 1` indices together with those of W^add. -/
def posEquiv : Fin (2 * D.m) ⊕ FirstFactorIndex j ≃ Fin (D.posRank j) ⊕ AddedIndex j :=
  equivOfCardEq <| by
    -- `↓` counts `D.RowIndex` as a whole; what is left is `D.r + j = D.posRank j + D.m`
    simp [↓card_rowIndex]
    grind

/-- The constant rows: a matrix 𝖼 with 2m rows for each column of μ⁺ at the place τ
(`DetIndex j τ`). Its columns are the r₊ = `D.posRank j` positive indices of W_j and the indices of
W^add. For a column of height h < r₊, row a is the basis vector of W_j at the positive index h + a
if h + a < r₊, and the basis vector number a of E^{3m−j} otherwise. For the l-th column of height
r₊, the rows are the rows `i.rows τ l` of τ(Y), placed in the columns of W♭. -/
def constantRows (i : D.RowChoice) (Y : Matrix D.FlatIndex D.FlatIndex D.E)
    (τ : NumberField.InfinitePlace D.E) :
    DetIndex j τ → Matrix (Fin (2 * D.m)) (Fin (D.posRank j) ⊕ AddedIndex j) ℂ :=
  (fun h ↦ (inclMatrix ℂ fun a : Fin (2 * D.m) ↦
      if ha : (h.1 + a : ℕ) < D.posRank j then Sum.inl ⟨h.1 + a, ha⟩
      else inr (Sum.inl (a.castAdd (D.m - j))))ᵀ) ⊕ᵥ
    fun k : Fin D.reducedHalfGap ↦
      fromCols 0 (fromCols 0 (fromCols ((Y.map (Φ τ)).submatrix (i.rows τ k) id) 0))

/-- The polynomial map ζ: the coordinates, in the columns X at the positive indices of W_j
(`firstColsCoord`), of the product P_V of the determinants det(𝖼; X z), with 𝖼 from
`constantRows j i Y` and the rows of variables indexed by V″. Here `firstColsCoord` reads P_V as a
polynomial in X with coefficients in z (`inFirstCols`) and takes its coordinate at a basis index of
weight μ⁺ (`WeylIndexFamily`). So each coordinate is a polynomial in the variables z in the columns
of W^add. -/
abbrev stackedDetProdCoords (i : D.RowChoice) (Y : Matrix D.FlatIndex D.FlatIndex D.E) :
    WeylIndexFamily (fun _ : NumberField.InfinitePlace D.E ↦ FirstFactorIndex j)
      (untwistedDescentPair j).colsPlus →
      MvPolynomial (NumberField.InfinitePlace D.E × FirstFactorIndex j × AddedIndex j) ℂ :=
  firstColsCoord (untwistedDescentPair j).colsPlus
    (stackedDetProd (posEquiv j) (constantRows j i Y))

/-- The reduction homomorphism O_E/ϖ²Q → O_E/ϖ², where ϖ is the product of the chosen places and Q
the product of the places in `ϑ.Q`. -/
abbrev forgetTwist : (D.twistModulus ϑ 2).ResidueRing →+* (D.untwistedModulus 2).ResidueRing :=
  reduceToChosenModulusSq

/-- The datum Ψ^add on matrices `z` modulo ϖ²Q with columns in W^add, for the matrix Λ = `u` modulo
ϖ² (`D.untwistedModulus 2`, ϖ the product of the chosen places). It is `0` unless
the columns on E^{3m−j} and W♭ are those of the identity matrix on `FirstFactorIndex j`. In that
case it is ψ_Λ^inv(z′), the sum over `g` in GL_{3m}(O_E/ϖ²) of ψ_Λ (`New.Rows.traceChar u`,
y ↦ ψ(tr(y Λ)) for a primitive additive character ψ) at z′ g, where z′ consists of the columns on
E^{3m} modulo ϖ². -/
def addedDatum (u : Matrix D.CarrierIndex (FirstFactorIndex j) (D.untwistedModulus 2).ResidueRing)
    (z : Matrix (FirstFactorIndex j) (AddedIndex j) (D.twistModulus ϑ 2).ResidueRing) : ℂ :=
  if z.submatrix id (Sum.map id Sum.inl) = inclMatrix (D.twistModulus ϑ 2).ResidueRing
    (.map (inr ∘ inr) id)
    then
    ∑ g : GL D.CarrierIndex _, traceChar u (z.toCols₂.toCols₂.map (forgetTwist ϑ) * g.1)
  else 0

/-- The coordinate l of the series Υ at h, for the choice `i`: the kernel of ((E^j)⁻, V″)
at (1, h), whose datum is the indicator of the columns of the identity matrix, times the class sum
over h′ in U(E^{3m}) of 𝖺(h′) χ′(h′) 𝖪[ζ_l]((1, h♭, h′), h). Here 𝖺χ′ is `New.Rows.carrierCoeff` at
the character χ′ = χ^j ϑ (`twistedChiMPow`), a class sum of theta kernels of (E^m, E^{3m}). 𝖪 is the
kernel of (W^add, V″) with both characters ν″ = `firstFactorChar` and the datum Ψ^add =
`New.Data.addedDatum` for the matrix Λ of `i`, and ζ = `New.Data.stackedDetProdCoords` is formed
with the short basis `D.shortRows` at the class h♭ of `i`. The first kernel has characters
`upsilonU1 ^ j` (υ on the norm-one ideles) and ν″, and `blockSumOne` forms the block diagonal point
(1, h♭, h′). -/
def leftSideSeries (i : ChoiceIndex j) (h : Gf D.E (FirstFactorIndex j))
    (l : WeylIndexFamily (fun _ : NumberField.InfinitePlace D.E ↦ FirstFactorIndex j)
      (untwistedDescentPair j).colsPlus) : ℂ :=
  modKernelStdSpace (stdSpace D.E (Fin j)).neg (upsilonU1 ^ j.val) (firstFactorChar ϑ j)
    (D.twistModulus ϑ 2)
      (Pi.single (inclMatrix (D.twistModulus ϑ 2).ResidueRing (Sum.inl ∘ inr ∘ Sum.inl)) 1) 1 1 h *
    stdClassSum (stdLevel D.E D.CarrierIndex) fun c : Gf D.E D.CarrierIndex ↦
      carrierCoeff D.m (twistedChiMPow ϑ j) c *
        modKernelStdSpace (stdSpace D.E (AddedIndex j)) (firstFactorChar ϑ j) (firstFactorChar ϑ j)
          (D.twistModulus ϑ 2)
          (addedDatum ϑ j i.matrix) (stackedDetProdCoords j i.rowChoice (D.shortRows i.rowChoice) l)
          (1, blockSumOne (1, blockSumOne (i.rowChoice.classRep, c))) h

end LineDefs

/-!
## The polynomial map ζ

The polynomial P_V, which is `New.Rows.stackedDetProd` for the constant rows at `j`, `i` and `Y`, is
a product of determinants det(𝖼; X z). Each has `2 m` constant rows `𝖼` stacked over rows of
variables, one row for each index in `D.FirstFactorIndex j`.
-/

section LineCoordinates

open Matrix MvPolynomial Rows Fintype «GL» ComplexOrder Norms.L2Operator Complex Matrix.Module
open Finset hiding map

variable {P : Parameters} {D : Data P}

/-- Let μ⁺ be the diagram with `(untwistedDescentPair j).colsPlus τ h` columns of height `h` at the
infinite place `τ`, from the data of the `j`-th theta lift of `D`. The set `DetIndex j τ`, which
indexes the determinants at `τ`, has one element for each column of μ⁺: its cardinality is the sum
of the column counts over the heights below the rank `card (FirstFactorIndex j)` of V″. -/
lemma card_detIndex_eq_sum (j : D.LiftIndex) (τ : NumberField.InfinitePlace D.E) :
    Fintype.card (DetIndex j τ) =
      ∑ h ∈ range (Fintype.card (FirstFactorIndex j)), (untwistedDescentPair j).colsPlus τ h := by
  -- The weight is `D.reducedHalfGap` at the height `D.posRank j` and vanishes beyond.
  have h_lt : D.posRank j < Fintype.card (FirstFactorIndex j) := by
    grind [card_sum, Fintype.card_fin, card_rowIndex, targetParameter_eq]
  have h_zero : ∀ h ≥ D.posRank j + 1, (untwistedDescentPair j).colsPlus τ h = 0 := by
    grind [descentPair]
  have h_top : (untwistedDescentPair j).colsPlus τ (D.posRank j) = D.reducedHalfGap := by
    grind [descentPair, reducedHalfGap, targetParameter_eq]
  calc Fintype.card (DetIndex j τ)
    _ = ∑ h ∈ range (D.posRank j), (untwistedDescentPair j).colsPlus τ h + D.reducedHalfGap := by
        simp [← sum_range]
    _ = ∑ h ∈ range (D.posRank j + 1), (untwistedDescentPair j).colsPlus τ h := by
        rw [sum_range_succ, h_top]
    _ = ∑ h ∈ range (Fintype.card (FirstFactorIndex j)), (untwistedDescentPair j).colsPlus τ h :=
        (eventually_constant_sum h_zero h_lt).symm

/-- The number of determinants at the infinite place `τ` is at most `natB + offWeight + Δ + m Δ`:
`D.natB` is the weight b at the b-places as a natural number, `D.offWeight` the weight at the other
places, and Δ = `D.gap` = 2 r⁸ the gap of the data. -/
lemma card_detIndex_le (j : D.LiftIndex) (τ : NumberField.InfinitePlace D.E) :
    Fintype.card (DetIndex j τ) ≤ D.natB + D.offWeight + D.gap + D.m * D.gap := by
  -- By `card_detIndex_add_firstFactorCharExp` the count is at most the weight `D.liftWeight j τ`,
  -- and `j ≤ m`.
  have h_mul : j * D.gap ≤ D.m * D.gap := mul_le_mul_left j.2.2 D.gap
  grind [card_detIndex_add_firstFactorCharExp j τ, D.weight_le_natB_add_offWeight τ]

/-- The number `card (DetIndex j τ)` of determinants at the infinite place `τ` is the number of
columns of μ⁺. This is the sum of `(untwistedDescentPair j).colsPlus τ h` over heights
`h < card (FirstFactorIndex j)`. It is at most `D.natB + D.offWeight + D.gap + D.m * D.gap`. -/
lemma card_detIndex (j : D.LiftIndex) (τ : NumberField.InfinitePlace D.E) :
    Fintype.card (DetIndex j τ) =
        ∑ h ∈ range (Fintype.card (FirstFactorIndex j)), (untwistedDescentPair j).colsPlus τ h ∧
      Fintype.card (DetIndex j τ) ≤ D.natB + D.offWeight + D.gap + D.m * D.gap :=
  ⟨card_detIndex_eq_sum j τ, card_detIndex_le j τ⟩

/-- Let `Z` have the `2 m + card (FirstFactorIndex j)` rows of a determinant det(𝖼; X z) at `j`, and
as columns the last `D.posRank j - h ≤ j` of the `D.posRank j` positive indices of W_j and the
indices `AddedIndex j` of W^add = E^{3m−j} ⊕ W♭ ⊕ E^{3m}, at most `12 m + 1` columns in all. If its
entries are at most `M ^ 4`, for the integers `m = D.m` and `M = D.M` of the data, the product of
the squared lengths of its columns is at most `(M ^ 9) ^ (12 m + 1)`. -/
lemma prod_sum_norm_sq_le_M_pow (j : D.LiftIndex) {h : ℕ} (h_rest : D.posRank j - h ≤ j)
    {Z : Matrix (Fin (2 * D.m) ⊕ FirstFactorIndex j) (Fin (D.posRank j - h) ⊕ AddedIndex j) ℂ}
    (hZ : ∀ (a : Fin (2 * D.m) ⊕ FirstFactorIndex j) (b : Fin (D.posRank j - h) ⊕ AddedIndex j),
      ‖Z a b‖ ≤ D.M ^ 4) :
    ∏ b : Fin (D.posRank j - h) ⊕ AddedIndex j,
      ∑ a : Fin (2 * D.m) ⊕ FirstFactorIndex j, ‖Z a b‖ ^ 2 ≤
      (↑(D.M ^ 9) : ℝ) ^ (12 * D.m + 1) := by
  have h_rows : card (Fin (2 * D.m) ⊕ FirstFactorIndex j) = D.r + 11 * D.m + 1 := by
    grind [card_sum, Fintype.card_fin, card_rowIndex]
  have h_cols : card (Fin (D.posRank j - h) ⊕ AddedIndex j) ≤ 12 * D.m + 1 := by
    grind [card_sum, Fintype.card_fin]
  -- Each column has squared length at most `(r + 11 m + 1) M ^ 8 ≤ M ^ 9`.
  have h_col (b : Fin (D.posRank j - h) ⊕ AddedIndex j) :
      ∑ a, ‖Z a b‖ ^ 2 ≤ (D.M ^ 9 : ℝ) := calc
    _ ≤ ∑ _a : Fin (2 * D.m) ⊕ FirstFactorIndex j, (D.M ^ 4 : ℝ) ^ 2 :=
        sum_le_sum fun a _ ↦ pow_le_pow_left₀ (norm_nonneg _) (hZ a b) 2
    _ = (D.r + 11 * D.m + 1 : ℕ) * (D.M ^ 4 : ℝ) ^ 2 := by
        rw [sum_const, card_univ, h_rows, nsmul_eq_mul]
    _ ≤ D.M ^ 9 := D.le_of_hasLogBound
  refine (prod_le_prod₀ (fun b _ ↦ by positivity) fun b _ ↦ h_col b).trans ?_
  simpa using pow_le_pow_right₀ (D.le_of_hasLogBound : (1 : ℝ) ≤ D.M ^ 9) h_cols

/-- The entries that a specialisation by `z` and `φ` puts into the determinants have norm at most
`M ^ 4`, where `M = D.M`. -/
structure IsSmallSpecialization (j : D.LiftIndex) (Y : Matrix D.FlatIndex D.FlatIndex D.E)
    (φ : ℂ →+* ℂ) (z : D.Φ × FirstFactorIndex j × AddedIndex j → ℂ) : Prop where
  /-- `φ` of every conjugate of an entry of `Y` has norm at most `M ^ 4`. -/
  norm_entry_le (τ : D.Φ) (a b : D.FlatIndex) : ‖φ (Φ τ (Y a b))‖ ≤ D.M ^ 4
  /-- `φ` of every value of `z` has norm at most `M ^ 4`. -/
  norm_value_le (x : D.Φ × FirstFactorIndex j × AddedIndex j) : ‖φ (z x)‖ ≤ D.M ^ 4

/-- Let `l` be a column of μ⁺ and `h` its height. The factor `stackedDet` for `l` is the determinant
of the constant rows `constantRows j i Y τ l` stacked over rows of variables, with `posEquiv j`
matching rows and columns; `inFirstCols` reads it as a polynomial in the first r₊ columns X with
coefficients in the others, z. Specialised by `z` and `φ`, it is the polynomial of a vector whose
weight is one column of height `h` at `τ`, and the squared norm of this vector is at most
`(M ^ 9) ^ (12 m + 1)` if the values of `φ` at the conjugates of the entries of `Y` and at the
values of `z` are at most `M ^ 4`. -/
lemma hasWeightNormSqLeIf_stackedDet (j : D.LiftIndex) (i : D.RowChoice)
    (Y : Matrix D.FlatIndex D.FlatIndex D.E) (φ : ℂ →+* ℂ)
    (z : D.Φ × FirstFactorIndex j × AddedIndex j → ℂ) (τ : D.Φ) (l : DetIndex j τ) {h : ℕ}
    (h_height : Sum.elim
      (fun x : Σ a : Fin (D.posRank j), Fin ((untwistedDescentPair j).colsPlus τ a) ↦ (x.fst : ℕ))
      (fun _ : Fin D.reducedHalfGap ↦ D.posRank j) l = h) :
    HasWeightNormSqLeIf (n := FirstFactorIndex j) (IsSmallSpecialization j Y φ z)
      (Pi.single τ (Pi.single h 1))
      (.map (φ.comp (eval z)) (inFirstCols (stackedDet τ (constantRows j i Y τ l) (posEquiv j))))
      (↑(D.M ^ 9) ^ (12 * D.m + 1)) := by
  classical
  -- Clear the columns of `X` after the first `h` by their unit rows, and apply
  -- `exists_toPoly_eq_det_and_weylNormSq_le` to the cleared matrix.
  have h_le : h ≤ D.posRank j := by cases l <;> grind [descentPair]
  have h_rest : D.posRank j - h ≤ j := by
    cases l <;> grind [Fin, Sigma, descentPair, targetParameter_eq]
  have h_lt : h < card (FirstFactorIndex j) := by
    grind [card_sum, Fintype.card_fin, card_rowIndex, targetParameter_eq]
  -- `colSplit` splits off the first `h` columns; `Z` is the rest after clearing.
  let firstCols : Fin (D.posRank j) ≃ Fin h ⊕ Fin (D.posRank j - h) :=
    (finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le h_le))).symm
  let colSplit : Fin (D.posRank j) ⊕ AddedIndex j ≃ Fin h ⊕ Fin (D.posRank j - h) ⊕ AddedIndex j :=
    (firstCols.sumCongr (.refl _)).trans (.sumAssoc ..)
  let Z : Matrix (Fin (2 * D.m) ⊕ FirstFactorIndex j) (Fin (D.posRank j - h) ⊕ AddedIndex j) ℂ :=
    of fun a b ↦
      φ ((constantRows j i Y τ l).fromRows (fromCols 0 (of fun u c ↦ z (τ, u, c))) a
        (colSplit.symm (.inr b)))
  have h_clear (x : (Σ _ : D.Φ, FirstFactorIndex j) × ℕ → ℂ) :
      eval x (MvPolynomial.map (φ.comp (eval z))
        (inFirstCols (stackedDet τ (constantRows j i Y τ l) (posEquiv j)))) =
      (((fromRows 0 (of fun u (c : Fin h) ↦ x (⟨τ, u⟩, c))).fromCols Z).submatrix id
        ((posEquiv j).trans colSplit)).det := by
    simp [stackedDet, AlgHom.map_det, RingHom.map_det, ↓ constantRows, ↓ inclMatrix]
    -- The two matrices differ by the unipotent factor (1 0; T 1), where T holds the cleared
    -- variables: it adds multiples of the upper rows.
    let T : Matrix (FirstFactorIndex j) (Fin (2 * D.m)) ℂ :=
      of fun u a ↦ if h + a < D.posRank j then x (⟨τ, u⟩, h + a) else 0
    refine det_eq_of_eq_det_one_mul (fromBlocks 1 0 T 1) (by simp)
      (ext fun a ↦ ((posEquiv j).trans colSplit).forall_congr_left.mpr ?_)
    -- Compare entries, by the kind of the factor and of the row.
    cases l <;> cases a
    all_goals
      simp [T, Z, Matrix.one_apply, ↓ Matrix.mul_apply, ↓ constantRows, ↓ inclMatrix,
        fromCols_map] at h_height ⊢
      simp +contextual [colSplit, firstCols, inFirstCols, h_height, Fin.cast]
    · -- an upper row vanishes in the first `h` columns
      lia
    · -- in a cleared column the sum over the upper rows has a single nonzero term
      intro b
      have hb_lt : (b : ℕ) < 2 * D.m := by grind
      have hb_pos : h + b < D.posRank j := by lia
      rw [Fintype.sum_eq_single ⟨b, hb_lt⟩]
      · simp [hb_pos]
      · intro a ha
        simp [Fin.val_ne_of_ne ha]
    · -- if `h = posRank j` there is no cleared column
      lia
  obtain ⟨ξ, h_eval, h_norm⟩ := exists_toPoly_eq_det_and_weylNormSq_le τ h_lt
    ((posEquiv j).trans colSplit) Z
  refine ⟨ξ, funext fun x ↦ by rw [h_eval, h_clear], ?_⟩
  rintro ⟨hY_small, hz_small⟩
  have hZ : ∀ a b, ‖Z a b‖ ≤ D.M ^ 4 := by
    -- Each entry is `0`, `1`, an entry of `Y` or a value of `z`.
    cases l <;> simp [Z, colSplit, firstCols, apply_ite, hY_small, hz_small, NeZero.one_le,
      one_le_pow₀, ↓ constantRows, ↓ inclMatrix, Matrix.one_apply, ↓ ite_apply]
  exact h_norm.trans (prod_sum_norm_sq_le_M_pow j h_rest hZ)

/-- At the `j`-th lift, take the product of the determinants of the constant rows
`constantRows j i Y` stacked over variables with rows `FirstFactorIndex j`, as a polynomial in the
first `D.posRank j` columns. Specialise the columns on `AddedIndex j` by `z` and apply `φ`. The
result is the polynomial of a vector of weight μ⁺, the diagram with
`(untwistedDescentPair j).colsPlus τ h` columns of height `h` at `τ`, whose squared norm is at most
`(M ^ 9) ^ ((12 m + 1) N)` if the specialised entries of `Y` and `z` are at most `M ^ 4`. Here `i`
chooses the rows of `Y`, `M = D.M`, and `N` is the total number of determinants over all places. -/
lemma hasWeightNormSqLeIf_stackedDetProd (j : D.LiftIndex) (i : D.RowChoice)
    (Y : Matrix D.FlatIndex D.FlatIndex D.E) (φ : ℂ →+* ℂ)
    (z : D.Φ × FirstFactorIndex j × AddedIndex j → ℂ) :
    HasWeightNormSqLeIf (n := FirstFactorIndex j) (IsSmallSpecialization j Y φ z)
      (untwistedDescentPair j).colsPlus
      (.map (φ.comp (eval z)) (inFirstCols (stackedDetProd (posEquiv j) (constantRows j i Y))))
      (↑(D.M ^ 9) ^ ((12 * D.m + 1) * ∑ τ : D.Φ, card (DetIndex j τ))) := by
  -- `stackedDetProd` is a product of determinants; `HasWeightNormSqLeIf.prod` adds their weights
  -- and multiplies the bounds.
  let height (τ : D.Φ) : DetIndex j τ → ℕ := Sum.elim (fun x ↦ (x.fst : ℕ)) fun _ ↦ D.posRank j
  have h_factors : HasWeightNormSqLeIf (n := FirstFactorIndex j) (IsSmallSpecialization j Y φ z)
      (∑ τ, ∑ l, Pi.single τ (Pi.single (height τ l) 1))
      (∏ τ, ∏ l,
        .map (φ.comp (eval z)) (inFirstCols (stackedDet τ (constantRows j i Y τ l) (posEquiv j))))
      (∏ τ : D.Φ, ∏ _l : DetIndex j τ, ↑(D.M ^ 9) ^ (12 * D.m + 1)) :=
    .prod fun τ _ ↦ .prod fun l _ ↦ hasWeightNormSqLeIf_stackedDet j i Y φ z τ l rfl
  -- The columns of all the factors together make up the diagram
  -- `(untwistedDescentPair j).colsPlus`.
  have h_weight : (∑ τ : D.Φ, ∑ l : DetIndex j τ, Pi.single τ (Pi.single (height τ l) 1)) =
      (untwistedDescentPair j).colsPlus := by
    -- Below `posRank j` a height occurs once for each such column; at `posRank j` it occurs
    -- `reducedHalfGap` times, which is the column count of the descent pair there.
    simp [height, funext_iff, Fintype.sum_sigma, sum_fin_eq_sum_range, ← mem_range,
      sum_add_distrib, Pi.single_apply]
    grind [descentPair, reducedHalfGap, targetParameter_eq]
  rw [h_weight] at h_factors
  simpa [stackedDetProd, map_prod, mul_sum, ← prod_pow_eq_pow_sum, pow_mul] using h_factors

/-- Take the product of the determinants of the constant rows `constantRows j i Y`, some of them
rows of the matrix `Y` chosen by `i`, stacked over rows of variables. Its coordinates in the first
`D.posRank j` columns of variables form the vector `stackedDetProdCoords j i Y` of polynomials in
the other columns. Give these other variables the values `z` and apply the ring map `φ`. If the
product becomes the polynomial (`toPoly`) of a vector `ξ`, then the vector of coordinates becomes
`ξ`. -/
lemma comp_eval_stackedDetProdCoords_eq_of_toPoly_eq (j : D.LiftIndex) (i : D.RowChoice)
    (Y : Matrix D.FlatIndex D.FlatIndex D.E) {φ : ℂ →+* ℂ}
    {z : D.Φ × FirstFactorIndex j × AddedIndex j → ℂ}
    {ξ : WeylIndex (FirstFactorIndex j) (untwistedDescentPair j).colsPlus → ℂ}
    (hξ : toPoly (fun _ : D.Φ ↦ FirstFactorIndex j) (untwistedDescentPair j).colsPlus ξ =
      .map (φ.comp (eval z)) (inFirstCols (stackedDetProd (posEquiv j) (constantRows j i Y)))) :
    φ ∘ eval z ∘ stackedDetProdCoords j i Y = ξ := by
  -- Coordinates commute with `φ` and with evaluation at `z`, and those of the polynomial of `ξ`
  -- are `ξ`.
  simp [funext_iff, firstColsCoord, map_fockPairing, MvPolynomial.map_map, ← hξ]

/-- Specialise the coordinates `stackedDetProdCoords j i Y` by values `z` for the remaining
variables and a ring map `φ`. The polynomial of the result is the specialised product of
determinants. -/
lemma toPoly_comp_eval_stackedDetProdCoords (j : D.LiftIndex) (i : D.RowChoice)
    (Y : Matrix D.FlatIndex D.FlatIndex D.E) (φ : ℂ →+* ℂ)
    (z : D.Φ × FirstFactorIndex j × AddedIndex j → ℂ) :
    toPoly (fun _ : D.Φ ↦ FirstFactorIndex j) (untwistedDescentPair j).colsPlus
        (φ ∘ eval z ∘ stackedDetProdCoords j i Y) =
      .map (φ.comp (eval z)) (inFirstCols (stackedDetProd (posEquiv j) (constantRows j i Y))) := by
  obtain ⟨ξ, hξ, -⟩ := hasWeightNormSqLeIf_stackedDetProd j i Y φ z
  rw [comp_eval_stackedDetProdCoords_eq_of_toPoly_eq j i Y hξ, hξ]

/-- Specialise the coordinates `stackedDetProdCoords j i Y` by values `z` for the remaining
variables and a ring map `φ`. Suppose `φ` of every image `Φ τ (Y a b)` of an entry of `Y` and of
every value `z x` has norm at most `M ^ 4`. Then the squared norm `weylNormSq` of the result is at
most `(M ^ 9) ^ ((12 m + 1) · ∑ τ, card (DetIndex j τ))`. -/
lemma weylNormSq_comp_eval_stackedDetProdCoords_le (j : D.LiftIndex) (i : D.RowChoice)
    (Y : Matrix D.FlatIndex D.FlatIndex D.E) {φ : ℂ →+* ℂ}
    {z : D.Φ × FirstFactorIndex j × AddedIndex j → ℂ}
    (hY_small : ∀ (τ : D.Φ) (a b : D.FlatIndex), ‖φ (Φ τ (Y a b))‖ ≤ D.M ^ 4)
    (hz_small : ∀ x : D.Φ × FirstFactorIndex j × AddedIndex j, ‖φ (z x)‖ ≤ D.M ^ 4) :
    weylNormSq (φ ∘ eval z ∘ stackedDetProdCoords j i Y) ≤
      ↑(D.M ^ 9) ^ ((12 * D.m + 1) * ∑ τ : D.Φ, card (DetIndex j τ)) := by
  obtain ⟨ξ, hξ, h_norm⟩ := hasWeightNormSqLeIf_stackedDetProd j i Y φ z
  rw [comp_eval_stackedDetProdCoords_eq_of_toPoly_eq j i Y hξ]
  exact h_norm ⟨hY_small, hz_small⟩

/-- Specialise the coordinates `stackedDetProdCoords j i Y` by values `z` for the remaining
variables and a ring map `φ`. Then `toPoly` of the result is the specialised product of
determinants. Assume `IsSmallSpecialization j Y φ z`: the images under `φ` of the conjugates of the
entries of `Y`, and of the values of `z`, are at most `M ^ 4` in size. Then `weylNormSq` of the
result is at most `(M ^ 9) ^ ((12 D.m + 1) N)`, where `N` is the sum over `τ` of
`card (DetIndex j τ)`, the total number of determinants. -/
lemma weylNormSq_stackedDetProdCoords_le (j : D.LiftIndex) (i : D.RowChoice)
    (Y : Matrix D.FlatIndex D.FlatIndex D.E) (φ : ℂ →+* ℂ)
    (z : D.Φ × FirstFactorIndex j × AddedIndex j → ℂ) :
    toPoly (fun _ : D.Φ ↦ FirstFactorIndex j) (untwistedDescentPair j).colsPlus
        (φ ∘ eval z ∘ stackedDetProdCoords j i Y) =
      .map (φ.comp (eval z)) (inFirstCols (stackedDetProd (posEquiv j) (constantRows j i Y))) ∧
    (IsSmallSpecialization j Y φ z → weylNormSq (φ ∘ eval z ∘ stackedDetProdCoords j i Y) ≤
      ↑(D.M ^ 9) ^ ((12 * D.m + 1) * ∑ τ : D.Φ, card (DetIndex j τ))) :=
  ⟨toPoly_comp_eval_stackedDetProdCoords j i Y φ z, fun h_small ↦
    weylNormSq_comp_eval_stackedDetProdCoords_le j i Y h_small.norm_entry_le h_small.norm_value_le⟩

/-- Take the product of the determinants of the constant rows `constantRows j i Y`, some of them
rows of the matrix `Y` chosen by `i`, stacked over rows of variables (`stackedDetProd`). Read it as
a polynomial in the first `D.posRank j` columns of variables, with coefficients polynomials in the
other columns (`inFirstCols`). It is the polynomial (`toPoly`) of its vector of coordinates
`stackedDetProdCoords j i Y`, of weight `(untwistedDescentPair j).colsPlus`. -/
lemma toPoly_stackedDetProdCoords (j : D.LiftIndex) (i : D.RowChoice)
    (Y : Matrix D.FlatIndex D.FlatIndex D.E) :
    toPoly (fun _ : D.Φ ↦ FirstFactorIndex j) (untwistedDescentPair j).colsPlus
      (stackedDetProdCoords j i Y) =
      inFirstCols (stackedDetProd (posEquiv j) (constantRows j i Y)) := by
  -- Compare coefficients at every point `z`, using `toPoly_comp_eval_stackedDetProdCoords` for the
  -- identity of `ℂ`.
  refine MvPolynomial.ext _ _ fun d ↦ MvPolynomial.funext fun z ↦ ?_
  have h_spec : toPoly (fun _ : D.Φ ↦ FirstFactorIndex j) (untwistedDescentPair j).colsPlus
      (eval z ∘ stackedDetProdCoords j i Y) =
      MvPolynomial.map (eval z) (inFirstCols
        (stackedDetProd (posEquiv j) (constantRows j i Y))) := by
    simpa using toPoly_comp_eval_stackedDetProdCoords j i Y (RingHom.id ℂ) z
  rw [← coeff_map, ← coeff_map, map_toPoly, h_spec]

/-- Replacing the variables `x` by `c • x` multiplies each coordinate `stackedDetProdCoords j i Y l`
at the `j`-th lift by `c ^ d` for the degree `d = ∑ τ, ∑ h, (N - h) κ(τ, h)`, where `N` is the
number of rows of variables, indexed by `FirstFactorIndex j`, and `κ` the weight
`(untwistedDescentPair j).colsPlus`. -/
lemma aeval_smul_X_stackedDetProdCoords (j : D.LiftIndex) (i : D.RowChoice)
    (Y : Matrix D.FlatIndex D.FlatIndex D.E)
    (l : WeylIndex (FirstFactorIndex j) (untwistedDescentPair j).colsPlus) {c : ℂ} (hc : c ≠ 0) :
    aeval (fun x : D.Φ × FirstFactorIndex j × AddedIndex j ↦ c • MvPolynomial.X x)
        (stackedDetProdCoords j i Y l) =
      c ^ (∑ τ : D.Φ, ∑ h ∈ range (card (FirstFactorIndex j)),
          (card (FirstFactorIndex j) - h) * (untwistedDescentPair j).colsPlus τ h) •
        stackedDetProdCoords j i Y l := by
  -- The product of determinants is multiplied by `c ^ (N ∑ κ(h))` and the Schur matrix of `c • 1`
  -- is the scalar `c ^ ∑ h κ(h)`; the quotient of the two is `c ^ d`.
  let κ : D.Φ → ℕ → ℕ := (untwistedDescentPair j).colsPlus
  let N : ℕ := card (FirstFactorIndex j)
  have h_schur : schur (n := fun _ ↦ FirstFactorIndex j) (n' := fun _ ↦ FirstFactorIndex j) κ
      (c • 1 : D.Φ → Matrix (FirstFactorIndex j) (FirstFactorIndex j) ℂ) =
      c ^ (∑ τ, ∑ h ∈ range N, h * κ τ h) • 1 := by
    simp [Pi.smul_def, schur_smul, prod_pow_eq_pow_sum, rankAt, N]
  have h_subst : c ^ (∑ τ, ∑ h ∈ range N, h * κ τ h) •
      aeval (fun x ↦ c • MvPolynomial.X x) (stackedDetProdCoords j i Y l) =
      c ^ (∑ τ, ∑ h ∈ range N, N * κ τ h) • stackedDetProdCoords j i Y l := by
    simpa [h_schur, ↓ card_detIndex_eq_sum, -card_sum, prod_pow_eq_pow_sum, mul_sum, ← pow_mul,
      Matrix.one_apply, N, κ] using
      twoSidedSubst_firstColsCoord (c • 1) 1
        (twoSidedSubst_stackedDetProd (posEquiv j) (constantRows j i Y) ..) κ l
  have h_exp : ∑ τ, ∑ h ∈ range N, N * κ τ h =
      (∑ τ, ∑ h ∈ range N, h * κ τ h) + ∑ τ, ∑ h ∈ range N, (N - h) * κ τ h := by
    simp_rw [← sum_add_distrib, ← add_mul]
    exact sum_congr rfl fun τ _ ↦ sum_congr rfl fun h hh ↦ by grind
  rw [h_exp, pow_add, mul_smul] at h_subst
  exact smul_right_injective _ (pow_ne_zero _ hc) h_subst

/-- Take the product of the determinants of the constant rows `constantRows j i Y` stacked over
variables, with `posEquiv j` matching rows and columns. Read as a polynomial in the first
`D.posRank j` columns over the polynomials in the others (`inFirstCols`), it has coefficients in
every subring `A` of `ℂ` that contains all the conjugates `Φ τ (Y a b)`. -/
lemma inFirstCols_stackedDetProd_mem_range (j : D.LiftIndex) (i : D.RowChoice)
    (Y : Matrix D.FlatIndex D.FlatIndex D.E) {A : Subring ℂ}
    (hA : ∀ (τ : D.Φ) (a b : D.FlatIndex), Φ τ (Y a b) ∈ A) :
    inFirstCols (stackedDetProd (posEquiv j) (constantRows j i Y)) ∈
      (MvPolynomial.map (MvPolynomial.map A.subtype)).range := by
  suffices stackedDetProd (posEquiv j) (constantRows j i Y) ∈
      (MvPolynomial.map (MvPolynomial.map A.subtype)).range.comap inFirstCols.toRingHom from this
  refine prod_mem fun τ _ ↦ prod_mem fun k _ ↦ IsIntMatrix.det_mem fun a b ↦ ?_
  rcases a with a | a
  · -- a row of constants
    have h_entry : ∀ u : Fin (D.posRank j) ⊕ AddedIndex j, constantRows j i Y τ k a u ∈ A := by
      cases k <;> simp [apply_ite, hA, ↓ constantRows, ↓ inclMatrix, Matrix.one_apply]
    exact ⟨C (C ⟨_, h_entry (posEquiv j b)⟩), by simp [inFirstCols]⟩
  · -- a row of variables
    simp only [AlgHom.toRingHom_eq_coe, Subring.mem_comap, submatrix_apply]
    rcases posEquiv j b with b | b
    · exact ⟨MvPolynomial.X (⟨τ, a⟩, b.val), by simp [inFirstCols]⟩
    · exact ⟨C (MvPolynomial.X (τ, a, b)), by simp [inFirstCols]⟩

/-- The polynomial `Q` in the variables of the columns of W^add is homogeneous of degree `d`, and
its coefficients lie in the ring generated by the conjugates of the entries of `Y`. -/
structure IsHomogeneousOverEntries (j : D.LiftIndex) (Y : Matrix D.FlatIndex D.FlatIndex D.E)
    (d : ℕ) (Q : MvPolynomial (D.Φ × FirstFactorIndex j × AddedIndex j) ℂ) : Prop where
  /-- `Q` is multiplied by `c ^ d` when the variables are multiplied by `c ≠ 0`. -/
  aeval_smul_X (c : ℂ) (hc : c ≠ 0) :
    aeval (fun x : D.Φ × FirstFactorIndex j × AddedIndex j ↦ c • MvPolynomial.X x) Q = c ^ d • Q
  /-- `Q` has its coefficients in every subring of `ℂ` that contains all the `Φ τ (Y a b)`. -/
  mem_range (A : Subring ℂ) (hA : ∀ (τ : D.Φ) (a b : D.FlatIndex), Φ τ (Y a b) ∈ A) :
    Q ∈ (MvPolynomial.map A.subtype).range

/-- There are a degree `d`, at most `10 m + 1` times the number of determinants over the infinite
places `D.Φ` of the CM field `D.E`, and an integer `0 < H ≤ (d ^ d) ^ 3`, both independent of `i`
and `Y`, such that every `H • stackedDetProdCoords j i Y l` is homogeneous of degree `d` and has its
coefficients in every subring of `ℂ` that contains all the conjugates `Φ τ (Y a b)`. -/
lemma exists_isHomogeneousOverEntries_smul_stackedDetProdCoords (j : D.LiftIndex) :
    ∃ d : ℕ, d ≤ (10 * D.m + 1) * ∑ τ : D.Φ, Fintype.card (DetIndex j τ) ∧
      ∃ H : ℤ, 0 < H ∧ H ≤ (d ^ d) ^ 3 ∧
        ∀ (i : D.RowChoice) (Y : Matrix D.FlatIndex D.FlatIndex D.E)
          (l : WeylIndex (FirstFactorIndex j) (untwistedDescentPair j).colsPlus),
          IsHomogeneousOverEntries j Y d (H • stackedDetProdCoords j i Y l) := by
  -- Let `N` be the number of rows of variables and `κ` the weight. The degree is
  -- `d = ∑ (N - h) κ(h)`, and `H` is the hook number of the complementary diagram `h ↦ κ(N - h)`,
  -- which has at most `d` boxes.
  let N : ℕ := card (FirstFactorIndex j)
  let κ : D.Φ → ℕ → ℕ := (untwistedDescentPair j).colsPlus
  let d : ℕ := ∑ τ, ∑ h ∈ range N, (N - h) * κ τ h
  let H : ℤ := hookNumber (fun τ h ↦ κ τ (N - h)) fun _ ↦ N
  have h_factor (τ : D.Φ) (h : ℕ) : (N - h) * κ τ h ≤ (10 * D.m + 1) * κ τ h := by
    -- `N - h ≤ 10 m + 1` whenever `κ(h) ≠ 0`.
    simp only [card_sum, ↓card_rowIndex, Fintype.card_fin, N, κ]
    grind [Nat.mul_lt_mul_right, descentPair, targetParameter]
  have hd_le : d ≤ (10 * D.m + 1) * ∑ τ : D.Φ, card (DetIndex j τ) := by
    simp only [↓card_detIndex_eq_sum, mul_sum]
    exact sum_le_sum fun τ _ ↦ sum_le_sum fun h _ ↦ h_factor τ h
  have hH_le : H ≤ (d ^ d) ^ 3 := by
    -- Count the boxes at each place, reversing the order of summation.
    refine hookNumber_le (sum_mono fun τ ↦ ?_)
    calc
      _ ≤ ∑ h ∈ range (N + 1), h * κ τ (N - h) := by
        grw [range_mono le_self_add]
      _ = ∑ h ∈ range (N + 1), (N - h) * κ τ (N - (N - h)) := by
        rw [← sum_flip]
      _ ≤ ∑ h ∈ range N, (N - h) * κ τ h := by
        grind only [sum_range_succ]
  refine ⟨d, hd_le, H, hookNumber_pos, hH_le, fun i Y l ↦ ⟨fun c hc ↦ ?_, fun A hA ↦ ?_⟩⟩
  · -- Homogeneity.
    rw [map_zsmul, aeval_smul_X_stackedDetProdCoords j i Y l hc, smul_comm]
  · -- Integrality: the product of determinants has coefficients in `A`, hence so have its
    -- coordinates `c` in the basis of products of minors.
    obtain ⟨F, hF : map (map A.subtype) F =
        inFirstCols (stackedDetProd (posEquiv j) (constantRows j i Y))⟩ :=
      inFirstCols_stackedDetProd_mem_range j i Y hA
    have h_coord (k : WeylIndex (FirstFactorIndex j) κ) :
        (weylGramOver *ᵥ stackedDetProdCoords j i Y) k ∈ (map A.subtype).range := by
      refine coord_mem_of_coeff_mem (map A.subtype).range.toAddSubgroup 0
        (f := map (map A.subtype) F) ?_ (by simp [coeff_map]) k
      rw [hF, ← toPoly_stackedDetProdCoords j i Y, ← nablaCombination_weylGramOver_mulVec]
      simp [detPow, Fintype.linearCombination_apply, κ]
    choose c hc using h_coord
    -- Over the polynomials with coefficients in `A`, the combination with coordinates `c`, times
    -- `H`, is the polynomial of a vector `ζ`.
    obtain ⟨ζ, hζ⟩ : ∃ ζ : WeylIndex (FirstFactorIndex j) κ →
        MvPolynomial (D.Φ × FirstFactorIndex j × AddedIndex j) A,
        toPoly (fun _ ↦ FirstFactorIndex j) κ ζ = H • nablaCombination κ c :=
      exists_toPoly_eq_hookNumber_dual_smul (fun _ _ _ ↦ rfl) (range_nablaCombination.le ⟨c, rfl⟩)
    have h_map : map (map A.subtype) (nablaCombination κ c) =
        toPoly (fun _ ↦ FirstFactorIndex j) κ (stackedDetProdCoords j i Y) := by
      rw [← nablaCombination_weylGramOver_mulVec, ← funext hc]
      simp [Fintype.linearCombination_apply, ← C_mul']
    -- A vector is determined by its polynomial, so `ζ` maps to `H • stackedDetProdCoords`.
    have h_eq : map A.subtype ∘ ζ = H • stackedDetProdCoords j i Y :=
      toPoly_injective (by rw [← map_toPoly, hζ, map_zsmul, h_map, map_zsmul])
    exact ⟨ζ l, congrFun h_eq l⟩

end LineCoordinates

end New.Data

end
