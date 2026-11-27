import New.Determinant.Norms.AdjointThetaLift

/-!
# The lift of a character and its squared norm as a Hecke L-value

Let `p = (ν, z)` be a critical pair (`New.Data.CriticalPair`) with `z ≥ 2` and `ϑ` a tame character
with set of places `Q`. The first section defines the lift `φ` of `ν ϑ` from `U(1)` to the definite
`U(2 z)`, a denominator for its values, and its normalized squared norm. The second section works
with any lift data `X` (`New.LValueData`) and the lift `X.trivialLift`, which differs from `φ` by
the scales of the vacuum and of the derivatives. For even rank `2 k ≥ 4` its squared norm is an
explicit multiple of the value at `k` of the partial Hecke `L`-function of `X.u1Char⁻¹`, where
`X.u1Char` is the character of the data.

## Main definitions and results

* `New.Data.CriticalPair.trivialLift`: the lift `φ` of `ν ϑ`, which is the lift for these data times
  `vacuumScale ^ card n` and `(π̄ * jetScale) ^ rowLengthSum`, where `π = D.piMBar`.
* `New.Data.CriticalPair.denomBound`: a denominator `n_ν` for the values of `φ`.
* `New.Data.CriticalPair.algPart`: the squared norm of `φ` divided by `N(Q) ^ (2 z - 1)`;
  `New.Data.CriticalPair.integralAlgebraicPart` is its multiple by
  `n_L = chosenGroupOrder * denomBound ^ 2`.
* `New.LValueData.trivialLift_eq_smul_thetaLift`: `X.trivialLift` is the theta lift of the constant
  function `1` times the index of the level of `U(1)`.
* `New.LValueData.hasLiftHeckePolynomial_trivialLift`: at split places off the level,
  `X.trivialLift` is spherical, with the Hecke polynomials of a lift of the trivial system
  (`New.DescentPair.HasLiftHeckePolynomial`).
* `New.LValueData.inner_thetaLift_constForm_self`: Rallis' inner product formula
  `New.SiegelWeil.IsSharp.petersson_lift_eq_integral` for the constant `1`. It gives the squared
  norm of the theta lift of `1` as a multiple of the sum of the coefficients of the vacuum.

Notions from other files:
* `New.Data.TameChar`: a character of `U(1)(𝔸)` of weight `0` whose tame part is supported on a
  finite set `Q` of places of norm prime to `D.M * D.N`, with `Q` disjoint from its conjugate.
* `New.LValueData`: two families of split places (`chosenPlace`, and `twistPlace` for `Q`), row
  lengths `rowLength`, and a character `u1Char` of `U(1)(𝔸)` whose tame part is trivial off these
  places.
* `New.LValueData.descentPair`: the descent datum (`New.DescentPair`) attached to the data. Its
  source is the definite line, and its weight has one row of length `rowLength τ` at each infinite
  place `τ`.
* `New.Parameters.vacuumScale`, `New.Parameters.jetScale`: the scaling factor of the vacuum, and the
  scale at which Taylor series of theta functions are taken.
* `New.Data.chosenGroupOrder`: a common multiple of the orders of the stabilisers in the class sums.
* `New.placeSign`: signs on the places of `E` whose Euler product at `k` is the value at `2 k` of
  the zeta function `ζ_F` of the maximal real subfield `F`, over which `E` is unramified.

## Relation to the literature

See `Lib.SiegelWeil.RallisInner.SharpData` for sources.
-/

noncomputable section

/-! ## The lift of a pair, its denominator and the algebraic part -/

section AlgebraicPartDefs

open Fintype

namespace New.Data.CriticalPair

variable {P : Parameters} {D : Data P} (p : D.CriticalPair) (n : Type) [Fintype n] [DecidableEq n]

/-- For the pair `p = (ν, z)`, the index set `n` has `2 z` elements, and `z ≥ 2`. -/
abbrev HasLiftRank : Prop := card n = 2 * p.z ∧ 2 ≤ p.z

/-- The pair `p = (ν, z)`, with `ν` of weight `-c`, has empty row: `c τ = z` at every infinite place
`τ`. Moreover the index set `n` has `2 z` elements, and `z ≥ 2`. -/
abbrev HasEmptyRow : Prop := (∀ τ : D.Φ, p.negWeight τ = p.z) ∧ p.HasLiftRank n

/-- The sum `∑ τ, (c τ - z)` of the row lengths of the pair `p = (ν, z)` with `ν` of weight `-c`. It
is the total order of the derivatives in the lift. -/
@[simp] abbrev rowLengthSum : ℕ := ∑ τ : D.Φ, (p.negWeight τ - p.z)

/-- A denominator for the values of the lift: the number `n_ν = M ^ (4 f z) * (M d) ^ j`, where
`M = D.M`, `f = D.f` is the number of infinite places, `d = P.d`, and `j = p.rowLengthSum` is the
sum of the row lengths. -/
def denomBound : ℕ := D.M ^ (2 * D.f * (2 * p.z)) * (D.M * P.d) ^ p.rowLengthSum

variable {p : D.CriticalPair} {n : Type} [Fintype n] [DecidableEq n] (H : p.HasLiftRank n)
  (ϑ : D.TameChar)

/-- The lift data `New.LValueData` for the pair `p = (ν, z)` twisted by the tame character `ϑ`, when
`n` has `2 z ≥ 4` elements: the chosen places together with the set `Q` of `ϑ`, the row lengths
`c τ - z` and the character `ν ϑ`. -/
abbrev lValueData : LValueData D.E n where
  toLevelPlaces := D.levelPlaces ϑ
  rowLength := fun τ ↦ p.negWeight τ - p.z
  u1Char := p.character * ϑ.toAutChar
  tamePart := p.tamePart * ϑ.tamePart
  hasWeight := by simpa [H, le_negWeight] using p.hasWeight.mul ϑ.hasWeight
  one_lt_card := by lia
  unramified := by simp_all [levelPlaces, ϑ.tamePart_eq_one, tamePart_eq_one, range_chosenPlace]

/-- The lift `φ` of `ν ϑ`, an algebraic form on the definite `U(n)` with the weight, level and level
character of the descent datum `(lValueData H ϑ).descentPair` (the space `New.DescentPair.FormV`).
It is the lift for the data `lValueData H ϑ`, multiplied by `vacuumScale ^ card n`, which makes the
vacuum integral, and by the power `rowLengthSum` of the scale `star piMBar * jetScale` of the
derivatives. Both scales are taken at `towerExp = D.towerExp`, the exponent that selects the field
`D.E = P.E towerExp`. -/
def trivialLift : (lValueData H ϑ).descentPair.FormV :=
  (P.vacuumScale D.towerExp ^ card n *
      (star (D.piMBar : ℂ) * P.jetScale D.towerExp) ^ p.rowLengthSum) •
    (lValueData H ϑ).trivialLift

/-- The algebraic part `L^alg(z, ν ϑ) = ‖φ‖ ^ 2 / N(Q) ^ (2 z - 1)`, viewed in `ℂ`: the squared norm
of the lift `φ = trivialLift H ϑ`, divided by a power of the product `N(Q)` of the norms of the
places in the set `Q` of `ϑ`. -/
@[simp] def algPart : ℂ := ‖trivialLift H ϑ‖ ^ 2 / ϑ.normQ ^ (card n - 1)

/-- The multiple `n_L L^alg(z, ν ϑ)` of `algPart H ϑ` by the natural number
`n_L = chosenGroupOrder * denomBound ^ 2`. -/
def integralAlgebraicPart : ℂ := (D.chosenGroupOrder * p.denomBound ^ 2 : ℕ) * algPart H ϑ

end New.Data.CriticalPair

end AlgebraicPartDefs

/-!
## The lift of the constant function and the squared norm

This section concerns the unscaled lift `New.LValueData.trivialLift` from `U(1)` to the definite
`U(n)`, for lift data `X`. Here `New.AutChar.L μ S` is the `L`-function of `x ↦ μ(x / x̄)` without
the factors at `S` and its conjugates, and `New.hookNumber` is the squared Fock norm of the highest
vector of a weight.
-/

namespace New

open Matrix Fintype ComplexConjugate MeasureTheory Fock Complex SiegelWeil Rows Finset MulAction
  Space Subgroup

variable {E n : Type} [Field E] [CMType E] [Fintype n] [DecidableEq n] (X : LValueData E n)

/-! ### The lift is a multiple of the theta lift of `1` -/

omit [DecidableEq n] in
/-- For lift data `X` let `W = X.descentPair.W` be the source of the theta lift: the standard
positive definite hermitian space of rank one over the CM field `E`, with adelic unitary group
`U(1) = G E X.descentPair.signs`. The constant function `1` on this group is a form of parameter
`0`: it is automorphic, bounded, and fixed by right convolution over the real points with
`typeKernel 0 X.descentPair.signs` if this kernel is integrable (`New.Space.IsForm`). -/
lemma LValueData.isForm_const_one :
    X.descentPair.W.IsForm (typeKernel 0 X.descentPair.signs) fun _ : G E X.descentPair.signs ↦
      1 := by
  -- It is the function attached to the constant algebraic form whose value is a unit vector.
  let ψ : AlgForm Unit X.descentPair.columnCount (0 : NumberField.InfinitePlace E → ℤ) :=
    ⟨fun _ ↦ highestVector X.descentPair.columnCount 0, by simp [smoothFunctions, rightStabilizer],
      fun γ g ↦ by simp [weightRep]⟩
  have h_one : ofAlgForm 0 1 ψ = fun _ : G E (1 : Unit → ℤˣ) ↦ 1 := funext fun g ↦ by
    simpa [algFormCoeff_apply, ψ] using gramForm_highestVector_self fun w ↦ (X.isHCParam_zero w).1
  rw [← h_one]
  exact isForm_ofAlgForm X.isHCParam_zero ψ

/-- The constant function `1` as a form of parameter `0` on the source line of `X.descentPair`. -/
def LValueData.constForm : X.descentPair.W.Form (typeKernel 0 X.descentPair.signs) :=
  ⟨fun _ ↦ 1, X.isForm_const_one⟩

/-- The lift `X.trivialLift` is the theta lift `Θ_W 1` of the constant function `1` on `U(1)`, times
the index of the principal level at the chosen places. -/
theorem LValueData.trivialLift_eq_smul_thetaLift [WeilData E] :
    X.trivialLift = (stdLevelIndex X.chosenLevel : ℂ) •
      X.descentPair.thetaLift X.fitsParams_descentPair X.constForm := by
  -- Pair both sides with a form `y`. As `Θ_W 1 = ∫ θ_W(g, ·) dg`, the product with `Θ_W 1` is the
  -- integral of the descent `⟨θ_W(g, ·), y⟩` of `y`, which depends only on the class of `g` at
  -- the level; so the integral is a class sum.
  refine ext_inner_right ℂ fun y ↦ ?_
  have h_descent := X.descentPair.isForm_normalizedDescent X.fitsParams_descentPair y
  let f (g : Gf E Unit) : ℂ := inner ℂ (X.kernelForm g) y
  have h_avg (g : Gf E Unit) : ∫ x : GInf E (1 : Unit → ℤˣ),
    X.descentPair.normalizedDescent y (x, g) = f g := by
    simp [f, X.normalizedDescent_eq_inner_kernelForm]
  have h_level : X.chosenLevel ≤ rightStabilizer f :=
    X.kernelForm_invariant.2.trans fun k hk g ↦ congrArg (inner ℂ · y) (hk g)
  have h_sum : inner ℂ X.trivialLift y = stdClassSum X.chosenLevel f := by
    simp [f, X.inner_trivialLift 1, X.normalizedDescent_eq_inner_kernelForm]
  have h_lift : inner ℂ (X.descentPair.thetaLift X.fitsParams_descentPair X.constForm) y =
      (stdLevelIndex X.chosenLevel : ℂ)⁻¹ * stdClassSum X.chosenLevel f :=
    calc _ = ∫ g, X.descentPair.normalizedDescent y g ∂X.descentPair.W.quotMeasure := by
          rw [DescentPair.thetaLift_eq_integral, ← inner_conj_symm, ← integral_inner
            (X.descentPair.integrable_smul_vectorKernelForm X.fitsParams_descentPair X.constForm),
            ← integral_conj]
          simp [constForm, DescentPair.normalizedDescent_eq_inner_vectorKernelForm]
      _ = _ := integral_quotMeasure_eq_classSum h_descent.rat_mul h_avg _ h_level
        h_descent.continuous
  rw [inner_smul_left, map_natCast, h_lift, h_sum, mul_inv_cancel_left₀ (by simp)]

/-- For lift data `X` the target of the theta lift is the definite `U(n)`, with forms of weight
`mixedWeight n colsPlus colsMinus`: as `colsMinus = 0` and `colsPlus τ` has `X.rowLength τ` columns
of height `1`, it has the single row `X.rowLength τ` at each infinite place `τ`. Let `paramV` be the
doubled Harish-Chandra parameter of this weight and `highestVector` its highest weight vector in the
order that `paramV` gives to the basis.

The lift of the constant function `1` on adelic `U(1)` by the theta kernel `pairThetaKernel` of the
two spaces, at the datum `fockDatum` of the highest vector, is the function `ofAlgForm` on adelic
`U(n)` attached to the algebraic form `X.trivialLift`, divided by the index of the level
`X.chosenLevel` in the integral points of `U(1)`. -/
lemma LValueData.lift_fockDatum_const_one [WeilData E] :
    lift X.descentPair.pairThetaKernel (X.descentPair.fockDatum
        (highestVector (mixedWeight n X.descentPair.colsPlus X.descentPair.colsMinus)
          X.descentPair.paramV))
        (fun _ : G E X.descentPair.signs ↦ 1) =
      (stdLevelIndex X.chosenLevel : ℂ)⁻¹ • ofAlgForm X.descentPair.paramV 1 X.trivialLift.val := by
  have h_val : X.trivialLift.val = (stdLevelIndex X.chosenLevel : ℂ) •
      (X.descentPair.thetaLift X.fitsParams_descentPair X.constForm).val :=
    congrArg Subtype.val X.trivialLift_eq_smul_thetaLift
  rw [h_val, map_smul, inv_smul_smul₀ (by simp), X.descentPair.ofAlgForm_thetaLift,
    X.fitsParams_descentPair.isArrow_fockDatum.coe_formLift]
  rfl

/-- The lift `X.trivialLift` has the Hecke polynomials of a lift of the trivial system of
eigenvalues. That is, at a split place `w` of norm `q` with neither `w` nor `w̄` among the places of
`X`, it is spherical with Hecke polynomial `∏_{l < N - 1} (1 - q ^ l α T) * (1 - q ^ (N - 1) α β⁻¹
T)`. Here `N = card n`, and `α`, `β` are the values `New.AutChar.frobValue` at `w` of the characters
`charW`, `charV` of the descent datum `X.descentPair`, for the spaces of ranks `1` and `N`. -/
lemma LValueData.hasLiftHeckePolynomial_trivialLift [WeilData E] :
    X.descentPair.HasLiftHeckePolynomial X.trivialLift 1 := by
  intro w hw hw_off
  -- The constant `1` on `U(1)` has the polynomial `1 - Y`; transfer it along the theta lift.
  have h_one : HasHeckePolynomial (X.descentPair.W.formRep (typeKernel 0 X.descentPair.signs)) hw
      (qPochhammer w.q (card Unit)) X.constForm :=
    hasHeckePolynomial_qPochhammer hw fun _ ↦ rfl
  have h_poly (Y : ℂ) :
      heckePolyEval Unit w ((1 : FinPlace E → ℕ → ℂ) w) Y = qPochhammer w.q (card Unit) Y := by
    simp [heckePolyEval, sub_eq_add_neg, sum_range_succ]
  obtain ⟨h_fixed, h_hecke⟩ :=
    X.descentPair.hasHeckePolynomial_thetaLift X.fitsParams_descentPair hw hw_off h_one
  have h_val : X.trivialLift.val.val = (stdLevelIndex X.chosenLevel : ℂ) •
      (X.descentPair.thetaLift X.fitsParams_descentPair X.constForm).val.val :=
    congrArg (·.val.val) X.trivialLift_eq_smul_thetaLift
  rw [h_val]
  refine ⟨Submodule.smul_mem _ _ h_fixed, fun T ↦ ?_⟩
  simp only [map_smul, h_poly]
  rw [h_hecke, smul_comm]

/-! ### Indices, masses and the real integral -/

/-- Let `F` be the residue field at `w` and `i : n` the index given by the embedding
`X.descentPair.incl : Unit ↪ n`. The subgroup `rangeParabolic` of `GL n F`, the stabiliser of the
hyperplane spanned by the basis vectors other than the `i`-th, has index
`1 + q + ⋯ + q ^ (card n - 1)`, where `q = #F`. -/
lemma LValueData.index_rangeParabolic_incl (w : FinPlace E) :
    (rangeParabolic (R := ResField w) X.descentPair.incl).index =
      ∑ j ∈ range (card n), Nat.card (ResField w) ^ j := by
  -- The inverse transpose takes it to the block triangular group, the stabiliser of a line.
  rw [index_rangeParabolic]
  refine index_stabilizer_line (X.descentPair.incl ()) fun g ↦ forall_congr' fun j ↦ ?_
  -- `False < True` in `Prop`, so the block condition concerns the entries in column `incl ()`.
  have h_lt (k : n) : (k ∉ Set.range X.descentPair.incl) < (j ∉ Set.range X.descentPair.incl) ↔
      k = X.descentPair.incl () ∧ j ≠ X.descentPair.incl () := by
    simp only [Set.mem_range, lt_iff_le_not_ge, le_Prop_eq]
    grind
  simp only [h_lt, and_imp, forall_eq]

/-- Let `F` be the residue field at `w`. The matrix `inclMatrix F X.descentPair.incl` has one
column, a standard basis vector of `F ^ n`. The index of its stabiliser in `GL n F` is the number
`#F ^ card n - 1` of non-zero vectors. -/
lemma LValueData.index_stabilizer_inclMatrix_col (w : FinPlace E) :
    (stabilizer (GL n (ResField w)) (inclMatrix (ResField w) X.descentPair.incl).col).index =
      Nat.card (ResField w) ^ Fintype.card n - 1 := by
  set A : Matrix n Unit (ResField w) := inclMatrix (ResField w) X.descentPair.incl
  have h_stab : stabilizer (GL n (ResField w)) A.col = stabilizer (GL n (ResField w)) (A.col ()) :=
    ext fun _ ↦ funext_iff.trans Unique.forall_iff
  rw [h_stab, index_stabilizer_GL_vector (by simp [A, inclMatrix, funext_iff, Matrix.one_apply])]

/-- The pairing `fockPairing ℂ P Q = P(∂) Q (0)` of two polynomials is unchanged when the variables
are renamed along an injective map. -/
lemma fockPairing_rename_rename {σ τ : Type} (e : σ ↪ τ) (P Q : MvPolynomial σ ℂ) :
    fockPairing ℂ (P.rename e) (Q.rename e) = fockPairing ℂ P Q := by
  change jet ℂ (P.rename e) (Q.rename e : MvPolynomial τ ℂ) = jet ℂ P Q
  rw [← MvPowerSeries.rename_coe, jet_rename e rfl]

/-- Let `X` be lift data and `κ = X.descentPair.columnCount` the weight with one row of length
`X.rowLength τ` at each infinite place `τ`. Let `η` be its highest weight vector, for the order of
the basis given by `paramV`, the doubled Harish-Chandra parameter of this weight, and let
`P = fockPoly η` be the polynomial in the coordinates of `Hom(W, V)` at the infinite places that
corresponds to `η`, with `W`, `V` the definite spaces of ranks `1` and `card n`. Then the squared
Fock norm `⟨P̄, P⟩` is the hook number, where `⟨P, Q⟩ = fockPairing ℂ P Q = P(∂) Q (0)`. -/
lemma LValueData.fockPairing_fockPoly_highestVector [WeilData E] :
    fockPairing ℂ ((X.descentPair.fockPoly
      (highestVector X.descentPair.columnCount X.descentPair.paramV)).map conj)
        (X.descentPair.fockPoly (highestVector X.descentPair.columnCount X.descentPair.paramV)) =
      hookNumber X.descentPair.columnCount (rankAt fun _ : NumberField.InfinitePlace E ↦ n) := by
  -- The pairing of the polynomials `toPoly` is the hook number times the Gram form, which is `1`
  -- on the highest vector; `toPoly` is the harmonic polynomial with its variables renamed.
  let η : WeylIndex n X.descentPair.columnCount → ℂ :=
    highestVector X.descentPair.columnCount X.descentPair.paramV
  have h_unit : gramForm η η = 1 :=
    gramForm_highestVector_self fun w ↦ (X.descentPair.isHCParam_paramV w).1
  have h_gram :
      fockPairing ℂ (toPoly (fun _ ↦ n) X.descentPair.columnCount (conj ∘ η))
        (toPoly (fun _ ↦ n) X.descentPair.columnCount η) =
        hookNumber X.descentPair.columnCount (rankAt fun _ ↦ n) * gramForm η η :=
    fockPairing_toPoly_toPoly ..
  let e : NumberField.InfinitePlace E × n × Unit ↪ (Σ _ : NumberField.InfinitePlace E, n) × ℕ :=
    ⟨fun c ↦ (⟨c.1, c.2.1⟩, 0), by simp_intro _ [Prod.ext_iff]⟩
  have h_rename : toPoly (fun _ ↦ n) X.descentPair.columnCount η = (X.descentPair.fockPoly η).rename
    e :=
    X.toPoly_eq_rename_fockPoly η
  rwa [h_unit, mul_one, ← map_toPoly, h_rename, MvPolynomial.map_rename,
    fockPairing_rename_rename] at h_gram
/-- The group `GL Unit (ResField w)` of invertible 1×1 matrices over the residue field `ResField w`
at `w` has as many elements as the unit group `(ResField w)ˣ` of this field. -/

lemma natCard_GL_unit_resField (w : FinPlace E) :
    Nat.card (GL Unit (ResField w)) = Nat.card (ResField w)ˣ :=
  Nat.card_congr (Units.mapEquiv uniqueRingEquiv.toMulEquiv).toEquiv

omit [DecidableEq n] in
/-- The index of the level `X.chosenLevel` in the integral points of `U(1)` is the product of the
numbers `q - 1` of units of the residue fields at the places `X.chosenPlace`. -/
lemma LValueData.stdLevelIndex_chosenLevel :
    (stdLevelIndex X.chosenLevel : ℂ) = ∏ i : X.ChosenIndex, (((X.chosenPlace i).q : ℂ) - 1) := by
  simp [stdLevelIndex, relIndex_levelOf, natCard_GL_unit_resField,
    Nat.card_units, Nat.card_pi, card_ResField]

/-- For lift data `X` let `i` be the index that the embedding `X.descentPair.incl : Unit ↪ n` picks.
The group `descentResidueLevel` consists of the families in the `GL n k_w`, over the places `w` of
the data (`toLevelPlaces`), that fix the `i`-th basis vector at each `X.chosenPlace` and preserve
the span of the other basis vectors at each `X.twistPlace`. Its preimage `levelOf` under reduction
is the level of the forms on `U(n)`. Its index (`relIndex`) in the group `stdLevel E n` of integral
points has a factor `q ^ N - 1` at each place `X.chosenPlace`, where a vector is fixed, and
`1 + q + ⋯ + q ^ (N - 1)` at each place `X.twistPlace`, where a hyperplane is preserved. Here
`N = card n` and `q` is the norm of the place. -/
lemma LValueData.relIndex_descentResidueLevel :
    ((levelOf X.descentPair.placeAt (descentResidueLevel X.descentPair.toLevelPlaces
      X.descentPair.incl)).relIndex
        (stdLevel E n) : ℂ) =
      (∏ i : X.ChosenIndex, (((X.chosenPlace i).q : ℂ) ^ card n - 1)) *
        ∏ i : X.TwistIndex, ∑ j ∈ range (card n), ((X.twistPlace i).q : ℂ) ^ j := by
  simp +instances [descentResidueLevel, ↓relIndex_levelOf, Seesaw.index_pi_univ,
    X.index_rangeParabolic_incl,
    X.index_stabilizer_inclMatrix_col, card_ResField]

/-- The mean of `|Ψ|²` for the block datum `Ψ = X.descentPair.blockFn`, that is the proportion of
the columns in its support, written as an explicit product (see `blockMass_eq_blockMeanSquare_div`):
a factor `q ^ (-card n)` at each place `X.chosenPlace` and `(q - 1) / q` at each place
`X.twistPlace`, where `q` is the norm of the place. -/
def LValueData.blockMeanSquare : ℂ :=
  (∏ i : X.ChosenIndex, (((X.chosenPlace i).q : ℂ) ^ Fintype.card n)⁻¹) *
    ∏ i : X.TwistIndex, (((X.twistPlace i).q : ℂ) - 1) / (X.twistPlace i).q

/-- For lift data `X` the block datum `Ψ = X.descentPair.blockFn` is a function of the columns `x`
of length `card n` modulo the places of `X`: it is zero unless `x` reduces at each `X.chosenPlace`
to one fixed basis vector, and then it is the product over the `X.twistPlace` of the tame characters
at one fixed entry of `x`. The mass `X.descentPair.blockMass` is defined as the sum of `|Ψ x|²` over
these columns, divided by the number of columns and by the order of the product of the groups
`GL Unit k_w` at the places `X.chosenPlace`. It equals the product `X.blockMeanSquare` of `q ^ (-N)`
over the chosen places and `(q - 1) / q` over the twist places (`q` the norm of the place,
`N = card n`), divided by the index of `X.chosenLevel` in the integral points of `U(1)`. -/
lemma LValueData.blockMass_eq_blockMeanSquare_div :
    X.descentPair.blockMass = X.blockMeanSquare / stdLevelIndex X.chosenLevel := by
  have h_twist (w : FinPlace E) :
      ((w.q : ℂ) - 1) / w.q = (w.q - 1) * w.q ^ (card n - 1) / w.q ^ card n := by
    rw [← pow_sub_one_mul X.one_lt_card.ne_bot (w.q : ℂ)]
    field_simp
  calc X.descentPair.blockMass
      = (∏ i, (((X.twistPlace i).q : ℂ) - 1) * ((X.twistPlace i).q : ℂ) ^ (card n - 1)) /
          ((∏ i, ((X.chosenPlace i).q : ℂ) ^ card n) * ∏ i, ((X.twistPlace i).q : ℂ) ^ card n) /
          ∏ i, (((X.chosenPlace i).q : ℂ) - 1) := by
        -- `Nat.card` is kept, so that `Nat.card_pi` splits the products of groups.
        simp +instances [DescentPair.blockMass, X.card_levelModulus_residueRing, Nat.card_pi,
          natCard_GL_unit_resField, Nat.card_units, mul_pow, prod_mul_distrib, prod_pow,
          card_ResField, DescentPair.rankDiff, -Nat.card_eq_fintype_card]
    _ = X.blockMeanSquare / stdLevelIndex X.chosenLevel := by
        simp only [X.stdLevelIndex_chosenLevel, blockMeanSquare, h_twist, prod_div_distrib,
          prod_inv_distrib]
        ring

/-- Let `F = X.descentPair.blockDatum` be the finite datum given by the function
`X.descentPair.blockFn` of columns modulo the places of `X` and by the vacuum at the other finite
places. Let `S₀` be the set of the places of `X` and their conjugates, and `J = X.chosenLevel`. Then
`F` is sharp for the action `ω` of `U(1)` with character `X.descentPair.charV`: it is a vacuum off
`S₀`, and at the finite points `g` integral off `S₀` the coefficient `⟨F, ω(g) F⟩` is `⟨F, F⟩ ≠ 0`
for `g ∈ J` and `0` otherwise. Its mass, `⟨F, F⟩` over the index of `J`, is the mean square
`X.blockMeanSquare` of the block datum over this index. -/
lemma LValueData.isSharp_blockDatum [WeilData E] :
    IsSharp X.descentPair.charV X.places.conjClosure X.descentPair.blockDatum.val X.chosenLevel
      (X.blockMeanSquare / stdLevelIndex X.chosenLevel) := by
  have h_places : (X.descentPair.levelModulus 1).places = X.places := places_levelModulus
  rw [← X.blockMass_eq_blockMeanSquare_div, ← h_places]
  exact X.descentPair.isSharp_blockDatum (.inl fun _ _ ↦ rfl)

/-- A place of the lift data `X` of norm `q` enters the norm of the lift, besides the index of
`X.chosenLevel` at a chosen place, through three factors:
* its factor in `blockMeanSquare`, the mean square of the block datum: `q ^ (-N)` at a place
`X.chosenPlace` and `(q - 1) / q` at a place `X.twistPlace`, where `N = card n`;
* its factor in the index (`relIndex`) of the level of the forms on `U(n)` in the integral points
`stdLevel E n`.
* the factor `(1 - q ^ (-N))⁻¹` of `ζ_F(N)`, with `F` the real subfield.

So the product over all places of `X` is `N(Q) ^ (N - 1)`, with `N(Q)` the product of the norms of
the twist places. -/
lemma LValueData.blockMeanSquare_mul_relIndex_mul_prod_eq_pow :
    X.blockMeanSquare *
        (levelOf X.descentPair.placeAt (descentResidueLevel X.descentPair.toLevelPlaces
          X.descentPair.incl)).relIndex
          (stdLevel E n) *
        ∏ i : X.ChosenIndex ⊕ X.TwistIndex, (1 - (((X.placeAt i).q : ℂ) ^ Fintype.card n)⁻¹)⁻¹ =
      (∏ i : X.TwistIndex, (X.twistPlace i).q : ℕ) ^ (Fintype.card n - 1) := by
  have h_card : card n ≠ 0 := X.one_lt_card.ne_bot
  have h_ne (w : FinPlace E) : (w.q : ℂ) ^ card n - 1 ≠ 0 :=
    sub_ne_zero.2 (mod_cast (one_lt_pow₀ w.one_lt_q h_card).ne')
  have h_chosen (w : FinPlace E) :
      ((w.q : ℂ) ^ card n)⁻¹ * (w.q ^ card n - 1) * (1 - ((w.q : ℂ) ^ card n)⁻¹)⁻¹ = 1 := by
    field_simp [h_ne w]
  have h_twist (w : FinPlace E) : ((w.q : ℂ) - 1) / w.q * (∑ j ∈ range (card n), (w.q : ℂ) ^ j) *
      (1 - ((w.q : ℂ) ^ card n)⁻¹)⁻¹ = w.q ^ (card n - 1) := by
    rw [div_mul_eq_mul_div, mul_geom_sum]
    field_simp [h_ne w]
    rw [mul_pow_sub_one h_card]
  calc _ = (∏ i, ((X.chosenPlace i).q ^ card n : ℂ)⁻¹ * ((X.chosenPlace i).q ^ card n - 1) *
          (1 - ((X.chosenPlace i).q ^ card n : ℂ)⁻¹)⁻¹) *
        ∏ i, (((X.twistPlace i).q : ℂ) - 1) / (X.twistPlace i).q *
          (∑ j ∈ range (card n), ((X.twistPlace i).q : ℂ) ^ j) *
          (1 - ((X.twistPlace i).q ^ card n : ℂ)⁻¹)⁻¹ := by
        simp only [blockMeanSquare, X.relIndex_descentResidueLevel, prod_sum_type, prod_mul_distrib,
          Sum.elim_inl, Sum.elim_inr]
        ring
    _ = _ := by simp [h_chosen, h_twist, prod_pow]

/-- For lift data `X` let `v` be the Fock vector (`polyVector`) of the polynomial `fockPoly η` of
the highest weight vector `η` of the weight `X.descentPair.columnCount`, which has one row of length
`X.rowLength τ` at each infinite place `τ`; the basis is ordered by `paramV`, the doubled
Harish-Chandra parameter of this weight. Both hermitian spaces, `W` of rank `1` and that of rank
`card n`, are definite, so the signs `realSigns E (homSigns 1 1)` of the coordinates of the Fock
space are all `1`, and the real points `GInf E X.descentPair.signs` of `U(1)` are one circle for
each infinite place. Let `ω` be the real Weil representation `realPairWeil γ γ'` of `U(1) × U(n)`,
in which `(x, y)` acts by the Fock operator times `∏ τ, det (y τ) ^ γ τ * det (x τ) ^ (-γ' τ)`. Here
`γ = X.descentPair.detExp` is the power of the determinant in the weight of the forms on `U(n)`, and
`γ' τ = -X.rowLength τ`, so that `ω(x, 1)` fixes `v`. Then the integral over the real points `x` of
`U(1)` of `⟨v, ω(x, 1) v⟩` times the Petersson product `⟨1, 1⟩` on `W` is the hook number times the
volume of the adelic quotient `[U(1)]`, the total mass of `quotMeasure` of `stdSpace E Unit`. -/
lemma LValueData.integral_fockInner_realPairWeil [WeilData E] :
    ∫ x : GInf E X.descentPair.signs,
        fockInner (polyVector (realSigns E (homSigns 1 1))
            (X.descentPair.fockPoly (highestVector X.descentPair.columnCount X.descentPair.paramV)))
          (realPairWeil X.descentPair.detExp
            (fun τ : NumberField.InfinitePlace E ↦ -(X.rowLength τ : ℤ)) (x, 1)
            (polyVector (realSigns E (homSigns 1 1))
              (X.descentPair.fockPoly (highestVector X.descentPair.columnCount
                X.descentPair.paramV)))) *
          X.descentPair.W.petersson 1 1 =
      hookNumber X.descentPair.columnCount (rankAt fun _ : NumberField.InfinitePlace E ↦ n) *
        ((stdSpace E Unit).quotMeasure.real .univ : ℂ) := by
  -- The real points of `U(1)` fix `v`, so `⟨v, ω(x, 1) v⟩` is the squared norm of `v`.
  set v := polyVector (realSigns E (homSigns (1 : Unit → ℤˣ) (1 : n → ℤˣ)))
    (X.descentPair.fockPoly (highestVector X.descentPair.columnCount X.descentPair.paramV))
  have h_norm (x : GInf E X.descentPair.signs) :
      fockInner v (realPairWeil X.descentPair.detExp (fun τ ↦ -(X.rowLength τ : ℤ)) (x, 1) v) =
        hookNumber X.descentPair.columnCount (rankAt fun _ : NumberField.InfinitePlace E ↦ n) := by
    simp +instances [← X.fockPairing_fockPoly_highestVector, v, fockInner_polyVector,
      fockPoly_eq_schurCoeffPoly, realPairWeil_schurCoeffPoly X.isLiftWeight]
  simp [h_norm, petersson]

/-! ### The inner product formula, the Euler product and the norm -/

/-- The inner product formula for the constant function `1` on `U(1)`. Let `X` be lift data of rank
`N = card n > 2`. The squared norm of the lift of `1` is a product of six factors:
* the volumes of `[U(1)]` and `[U(n)]` divided by the index of `X.chosenLevel`;
* the dimension of the weight, the cardinality of the index set `WeylIndex` of a basis;
* its hook number, the squared Fock norm of its highest vector;
* the index of the level `levelOf descentResidueLevel` of `U(n)` in the integral points;
* `X.blockMeanSquare`, the product of `q ^ (-N)` over the chosen places and `(q - 1) / q` over the
  twist places, with `q` the norm of the place;
* the sum `vacuumSum` of the coefficients `(b(det g) * finMultiplier g ^ N)⁻¹` of the vacuum, with
  `b = charV = X.u1Char * upsilonU1 ^ (N / 2)` and `finMultiplier` the multiplier of the Weil
  representation. Here `g` runs over representatives of the finite points of `U(1)` modulo those
  integral at every place other than the places of `X` and their conjugates. -/
theorem LValueData.inner_thetaLift_constForm_self [WeilData E] (h_rank : 2 < Fintype.card n) :
    inner ℂ (X.descentPair.thetaLift X.fitsParams_descentPair X.constForm)
        (X.descentPair.thetaLift X.fitsParams_descentPair X.constForm) =
      (stdSpace E Unit).quotMeasure.real .univ * (stdSpace E n).quotMeasure.real .univ /
          stdLevelIndex X.chosenLevel *
        card (WeylIndex n X.descentPair.columnCount) *
        hookNumber X.descentPair.columnCount (rankAt fun _ : NumberField.InfinitePlace E ↦ n) *
        (levelOf X.descentPair.placeAt (descentResidueLevel X.descentPair.toLevelPlaces
          X.descentPair.incl)).relIndex
          (stdLevel E n) *
        X.blockMeanSquare * vacuumSum Unit (Fintype.card n) X.descentPair.charV
          X.places.conjClosureᶜ := by
  let O : DescentPair E Unit n := X.descentPair
  let σ : ℂ := vacuumSum Unit (card n) O.charV X.places.conjClosureᶜ
  let v : PairFock E O.signs (1 : n → ℤˣ) :=
    polyVector (realSigns E (homSigns 1 1)) (O.fockPoly (highestVector O.columnCount O.paramV))
  let θ₁ : G E (1 : n → ℤˣ) → ℂ :=
    lift O.pairThetaKernel (O.fockDatum (highestVector O.columnCount O.paramV)) fun _ ↦ 1
  have h_lift : ofAlgForm O.paramV 1 (O.thetaLift X.fitsParams_descentPair X.constForm).val =
    θ₁ := by
    rw [O.ofAlgForm_thetaLift, X.fitsParams_descentPair.isArrow_fockDatum.coe_formLift]
    rfl
  have h_one : (fun _ : G E O.signs ↦ (1 : ℂ)) ∈ (stdSpace E Unit).rapidFunctions :=
    ((stdSpace E Unit).isAutomorphic_const 1).mem_rapidFunctions fun _ _ ↦ rfl

  have h_rallis : (stdSpace E n).petersson θ₁ θ₁ =
      (stdSpace E n).quotMeasure.real .univ * (X.blockMeanSquare / stdLevelIndex X.chosenLevel) *
        ∫ x : GInf E O.signs,
          fockInner v (realPairWeil O.detExp (fun τ ↦ -(X.rowLength τ : ℤ)) (x, 1) v) *
            O.W.petersson (fun _ ↦ 1) fun g : G E O.signs ↦
              rallisSeries (card n) O.charV X.places.conjClosureᶜ (fun _ ↦ 1) (g * (x, 1)) :=
    (X.isSharp_blockDatum.petersson_lift_eq_integral (by simpa) O.charW O.detExp v h_one h_one
      fun _ _ _ ↦ rfl).right
  -- Translations fix `1`, so its series is the constant `σ`; the real points fix `v`.
  have h_series (x : GInf E O.signs) : O.W.petersson (fun _ ↦ 1) (fun g : G E O.signs ↦
      rallisSeries (card n) O.charV X.places.conjClosureᶜ (fun _ ↦ 1) (g * (x, 1))) =
        O.W.petersson 1 1 * σ := by
    simp [rallisSeries_const, petersson, σ]
  have h_real : ∫ x : GInf E O.signs,
        fockInner v (realPairWeil O.detExp (fun τ ↦ -(X.rowLength τ : ℤ)) (x, 1) v) *
          O.W.petersson 1 1 =
      hookNumber O.columnCount (rankAt fun _ : NumberField.InfinitePlace E ↦ n) *
        ((stdSpace E Unit).quotMeasure.real .univ : ℂ) :=
    X.integral_fockInner_realPairWeil
  simp only [h_series, ← mul_assoc, integral_mul_const, h_real] at h_rallis
  rw [LevelPlaces.LevelForm.inner_eq_petersson (stdSpace E n) O.isHCParam_paramV, h_lift, h_rallis]
  ring

/-- The Euler product `eulerProd placeSign` over the finite places of `E`, with the signs
`placeSign`, does not vanish at `k` for natural `k > 1`. If `E` is unramified over its maximal real
subfield `F` at the finite places, this product at `k` is `ζ_F(2 k)`. -/
lemma eulerProd_placeSign_ne_zero {k : ℕ} (hk : 1 < k) :
    eulerProd (K := E) placeSign k ≠ 0 := by
  simp [eulerProd_eq_exp_neg_tsum_log_of_norm_le_one norm_placeSign_le (Nat.one_lt_cast.2 hk)]

omit [DecidableEq n] in
/-- For lift data `X` let the rank be `card n = 2 * k` with `1 < k`. The function `placeSign` gives
`1` at a place fixed by complex conjugation and the two signs to the two places of a split pair, so
its Euler product `eulerProd placeSign k`, of the factors `(1 - placeSign w * q_w ^ (-k))⁻¹` over
the places `w` of `E`, is `ζ_F(2 k)` for the maximal real subfield `F` when `E` is unramified over
`F` at the finite places, which this lemma does not assume. Setting the signs to zero on
`X.places.conjClosure`, the places of `X` and their conjugates, omits these factors, and so
multiplies the product by `1 - q ^ (-card n)` for each place of `X` of norm `q`. -/
lemma LValueData.eulerProd_indicator_placeSign {k : ℕ} (h_rank : 2 * k = card n) (hk : 1 < k) :
    eulerProd (X.places.conjClosureᶜ.indicator placeSign) k =
      eulerProd (K := E) placeSign k *
        ∏ i : X.ChosenIndex ⊕ X.TwistIndex, (1 - (((X.placeAt i).q : ℂ) ^ Fintype.card n)⁻¹) := by
  -- `S` is the finite set of the places of `X` and their conjugates. These places are split, so
  -- each pair contributes `1 - q ^ (-2 k)`.
  let S : Finset (FinPlace E) := univ.map ⟨star ∘ X.placeAt ⊕ᵥ X.placeAt,
    (star_injective.comp X.apart.injective).sumElim X.apart.injective X.apart.star_ne⟩
  have hS_eq : (S : Set (FinPlace E)) = X.places.conjClosure := by
    ext w
    have h_mem : w ∈ S ↔ (∃ i, star (X.placeAt i) = w) ∨ ∃ i, X.placeAt i = w := by
      simp only [S, mem_map, mem_univ, true_and, Sum.exists, Function.Embedding.coeFn_mk,
        Sum.elim_inl, Sum.elim_inr, Function.comp_apply]
    grind [star_star]
  have h_erase : eulerProd ((S : Set (FinPlace E))ᶜ.indicator placeSign) k =
      eulerProd (K := E) placeSign k *
        ∏ w ∈ S, (1 - placeSign w * (w.q : ℂ) ^ (-((k : ℝ) : ℂ))) := by
    obtain ⟨-, -, h_eq⟩ := eulerProd_erase norm_placeSign_le S
    exact h_eq k (mod_cast hk)
  rw [← hS_eq, h_erase, prod_map, prod_sum_type, ← prod_mul_distrib]
  refine congrArg _ (Finset.prod_congr rfl fun i _ ↦ ?_)
  simp [cpow_neg, placeSign_factor_mul (X.apart.star_ne i i), ← pow_mul', h_rank]

/-- The squared norm of the lift `X.trivialLift`. Here `X` consists of chosen and twist places, row
lengths, and a character `μ = X.u1Char` of `U(1)(𝔸)` of weight `-(X.rowLength τ + k)` at each
infinite place `τ`, whose tame part is trivial off these places; `X.trivialLift` is the theta lift
to the definite `U(n)` of the constant `1` on `U(1)` for these data, times the index of
`X.chosenLevel`.

Let the rank be `2 * k` with `1 < k`. Let `C` be the product of the volumes of `[U(n)]` and
`[U(1)]`, divided by `ζ_F(2 k)`, the Euler product at `k` of the signs `placeSign` (`F` is the
maximal real subfield of `E`). Then `C ≠ 0`, and the squared norm is a product of six factors: `C`,
the product of the numbers `q - 1` of the places `X.chosenPlace`, the hook number of the weight
`X.descentPair.columnCount`, its dimension, the value `L(k)` and `N(Q) ^ (card n - 1)`. Here
`L = X.u1Char⁻¹.L X.places` is the `L`-function of the character `x ↦ μ(x / x̄)⁻¹` of `E`, without
the factors at the places of `X` and their conjugates, and `N(Q)` is the product of the norms of the
places `X.twistPlace`. -/
lemma LValueData.inner_trivialLift_self_eq_L [WeilData E]
    {k : ℕ} (h_rank : 2 * k = card n) (hk : 1 < k) :
    let C : ℂ := (stdSpace E n).quotMeasure.real ⊤ * (stdSpace E Unit).quotMeasure.real ⊤ /
      eulerProd (K := E) placeSign (card n / 2 : ℕ)
    C ≠ 0 ∧
    inner ℂ X.trivialLift X.trivialLift =
      C * (∏ i : X.ChosenIndex, ((X.chosenPlace i).q - 1) : ℕ) *
        hookNumber X.descentPair.columnCount (rankAt fun _ : NumberField.InfinitePlace E ↦ n) *
        card (WeylIndex n X.descentPair.columnCount) * X.u1Char⁻¹.L X.places k *
        (∏ i : X.TwistIndex, (X.twistPlace i).q : ℕ) ^ (card n - 1) := by
  -- The inner product formula gives the squared norm of `Θ_W 1` by the sum of the coefficients of
  -- the vacuum. This sum is the Euler product `L(k) / ζ_F(2 k)` without the places of `X`. The
  -- omitted factors of `ζ_F(2 k)` combine with the index and the mean square at the level.
  obtain rfl : k = card n / 2 := by lia
  have h_index : (∏ i, ((X.chosenPlace i).q - 1) : ℕ) = (stdLevelIndex X.chosenLevel : ℂ) := by
    simp [X.stdLevelIndex_chosenLevel]
  have h_euler : vacuumSum Unit (card n) X.descentPair.charV X.places.conjClosureᶜ =
      X.u1Char⁻¹.L X.places (card n / 2 : ℕ) / eulerProd (K := E) placeSign (card n / 2 : ℕ) *
        ∏ i, (1 - (((X.placeAt i).q : ℂ) ^ card n)⁻¹)⁻¹ := by
    rw [show X.descentPair.charV = X.u1Char * WeilData.upsilonU1 ^ (card n / 2) from rfl,
      vacuumSum_eq_L_div_eulerProd X.hasWeight X.unramified h_rank.symm hk,
      X.eulerProd_indicator_placeSign h_rank hk, prod_inv_distrib, ← div_div, div_eq_mul_inv]
  refine ⟨by simp [measureReal_univ_ne_zero, eulerProd_placeSign_ne_zero hk], ?_⟩
  -- The mean square, the index and the omitted factors are collected into `N(Q) ^ (2 k - 1)`.
  rw [X.trivialLift_eq_smul_thetaLift, inner_smul_left, inner_smul_right, map_natCast,
    X.inner_thetaLift_constForm_self (by lia), h_euler, h_index,
    ← X.blockMeanSquare_mul_relIndex_mul_prod_eq_pow, Set.top_eq_univ, Set.top_eq_univ]
  field_simp

end New

end
