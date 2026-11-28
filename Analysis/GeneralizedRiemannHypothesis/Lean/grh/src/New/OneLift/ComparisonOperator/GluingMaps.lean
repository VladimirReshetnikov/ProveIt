import New.Determinant.Chain.NormOfChain
import New.OneLift.ComparisonOperator.GluedForms
import New.OneLift.ComparisonOperator.ProductsSpan
import New.OneLift.FalseLifts.PeriodsOfFalseLifts
import New.Spanning.SecondMoment.SpanningTheorem

/-!
# The first factors and the gluing maps

The first factors `φ″_{ϑ,i}` on `V″` are integral away from `Q` and small for `ϑ = 1`, and their
theta series satisfy `c′_ϑ Ξ_{ϑ,i} = c″ 𝖥_i` with functions `𝖥_i` that do not depend on the twist.
Gluing them to forms on `V°` gives the map `glue_ϑ` to forms on `V_j`. Its adjoint, the period,
satisfies `c′_ϑ glue_ϑ* Θ_{j,ϑ} = Θ°`, where `Θ°` does not depend on the twist and is injective,
because products span. The map `glue_ϑ` keeps integrality away from `Q`, is short for `ϑ = 1`, and
takes the image of `Θ°` to forms orthogonal to the false lifts. The comparison operator, an integer
multiple of `glue_ϑ glue_ϑ*`, is built from it in `New.OneLift.LiftVolumeHeight`.

In the code `φ″` is `firstFactor`, `Ξ` is `firstFactorPairing`, `𝖥` is `choiceFn`, `glue_ϑ` is
`glue j ϑ` and `Θ°` is `periodLift`. The integer `M` is `D.M`, its factor `ϖ` is `D.piM`, and `Q` is
the set of places of the twist `ϑ`.

Notions from other files:
* `descentPair ϑ j`: the spaces `W_j` and `V_j` with the characters and levels for the twist `ϑ`;
  `untwistedDescentPair j` is its untwisted form. The diagram of the values of the forms on `V″` is
  `μ⁺` (`colsPlus`), that on `V°` is `μ⁻` (`colsMinus`).
* `ChoiceIndex j`: the choices `i`, each a matrix `Λ` with a class `h♭` and constant rows.
* `FirstFactorIndex j` indexes the basis of `V″`, `D.SecondFactorIndex` that of `V°`, and
  `D.SecondFactorClasses` is the set of classes of `U(V°)` at the level `J (ϖ²)`.
* `goodLift ϑ j`: the theta lift `Θ_{j,ϑ}` from good forms on `W_j` to forms on `V_j`.
* `normalizedDescent`: the descent, which sends a form on `V_j` to a function on `U(W_j)` by pairing
  it with the theta kernel over the classes of `U(V_j)`.
* `weylGauge`, `weylNormSq`: the gauge at a place over `l` and the squared norm of a vector in a
  representation given by a diagram.

## Relation to the literature

Integral forms pairing with a lift to an explicit L-value (pullback, seesaw) are known in the
literature in low rank.

Related work: Böcherer–Dummigan–Schulze-Pillot, Yoshida lifts and Selmer groups, 2012; Y.-S. Lee,
Hida family of theta lift from U(1) to definite U(2), 2024; Prasanna, Integrality of a ratio of
Petersson norms and level-lowering congruences, 2006.
-/

noncomputable section

namespace New.Rows

open Finset Real ComplexConjugate Data WeilData Submodule Function.Embedding MeasureTheory

open LinearMap Fintype LevelPlaces DescentPair

variable {P : Parameters} {D : Data P} (j : D.LiftIndex)

/-! ### Tuples of forms on `V°`, the splitting and the lattices -/

/-- The hook number `hk` of the diagram `μ⁻`, which gives the weight of the forms on `V°`. -/
abbrev hookNumberMinus : ℤ :=
  hookNumber (untwistedDescentPair j).colsMinus (rankAt fun _ ↦ D.SecondFactorIndex)

/-- The values of the forms on `V°`, with the invariant metric. -/
@[implicit_reducible] def SecondFactorFormValues : Type :=
  WeylIndex D.SecondFactorIndex (untwistedDescentPair j).colsMinus → ℂ

instance : NormedAddCommGroup (SecondFactorFormValues j) :=
  Matrix.toNormedAddCommGroup _ weylGramOver_posDef

instance : InnerProductSpace ℂ (SecondFactorFormValues j) := .ofCore (F := _ → ℂ) _

instance : Module.Finite ℂ (SecondFactorFormValues j) := .pi

/-- `𝒜^⊕`: one copy of the forms on `V°` for each choice. The level `J (ϖ²)` is sufficiently small
(all stabilisers of classes are trivial), so a form is the table of its values at representatives
of the classes, and an inner product is a plain sum over the classes. -/
abbrev _root_.New.Data.FormTuples : Type := PiLp 2 fun _ : ChoiceIndex j × D.SecondFactorClasses ↦
  SecondFactorFormValues j

variable {j} in
/-- A tuple of forms on `V°` is integral at the place `φ` over `l` if all its values are, that is,
have `weylGauge` at most `1`. A matrix acts on the values by its inverse transpose, so the gauge is
that of the conjugate vector at the conjugate place. -/
def IsIntegralFormTuple {l : ℕ} [Fact l.Prime] (φ : PadicPlace l) (ζ : FormTuples j) : Prop :=
  ∀ b : ChoiceIndex j × D.SecondFactorClasses,
    weylGauge (ι := ⟨φ.ιₚ.comp conj⟩) (untwistedDescentPair j).colsMinus 0 b.2.out (star (ζ b)) ≤ 1

variable {j} in
/-- The squared norm `‖ζ‖_σ²` of a tuple of forms on `V°`: a plain sum over the classes. -/
def formTupleNormSq (σ : ℂ ≃+* ℂ) (ζ : FormTuples j) : ℝ :=
  ∑ b : ChoiceIndex j × D.SecondFactorClasses, weylNormSq (σ ∘ ζ b)

/-- The rank `r + 9 m + 1` of `V″` is at most `2 n_m`. -/
lemma card_firstFactorIndex_le_two_mul_n : card (FirstFactorIndex j) ≤ 2 * D.n D.m := by
  rw [card_firstFactorIndex]
  linarith [D.six_mul_r_le_n, D.r_add_one, D.hundred_mul_m_add_nine_lt_k]

variable (D) in
/-- The rank `r + t = 6 r` of `V_j` is at most `2 n_m`. -/
lemma card_rowIndex_sum_fin_le_two_mul_n : card (D.RowIndex ⊕ Fin D.t) ≤ 2 * D.n D.m := by
  rw [D.card_rowIndex_sum_fin]
  linarith [D.six_mul_r_le_n, D.t_eq_five_mul_r]

/-- The basis of `V″` is large enough to hold the divided directions: `D.CarrierIndex` embeds in
`FirstFactorIndex j`. -/
lemma nonempty_carrierIndex_embedding_firstFactorIndex :
    Nonempty (D.CarrierIndex ↪ FirstFactorIndex j) := by
  have r_add_one : D.r + 1 = D.k + D.m := D.r_add_one
  have k_large : 100 * D.m + 9 < D.k := D.hundred_mul_m_add_nine_lt_k
  refine nonempty_of_card_le ?_
  rw [card_firstFactorIndex, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
  omega

/-- If `card N ≤ card n` and the diagram `κ` has no column of height at least `card N`, then
`HasColumnsBelow n N κ` holds. -/
lemma hasColumnsBelow_of_eq_zero {Φ n N : Type} [Fintype n] [Fintype N] {κ : Φ → ℕ → ℕ}
    (h_card : card N ≤ card n) (h_zero : ∀ (τ : Φ) (h : ℕ), card N ≤ h → κ τ h = 0) :
    HasColumnsBelow n N κ := by
  refine ⟨fun τ ↦ ⟨h_card, fun h h_mem ↦ h_zero τ h (mem_Ioo.1 h_mem).1.le⟩, funext fun τ ↦ ?_⟩
  simp [schurDetExp, h_zero τ (card N) le_rfl]

/-- The indices of `V″ ⊕ V°` other than those of `W_j` in `V″` are `t` in number. -/
lemma card_padIndex_sum_flatIndex_sum_secondFactorIndex :
    card (PadIndex j ⊕ D.FlatIndex ⊕ D.SecondFactorIndex) = D.t := by
  have k_large : 100 * D.m + 9 < D.k := D.hundred_mul_m_add_nine_lt_k
  have r_add_one : D.r + 1 = D.k + D.m := D.r_add_one
  have t_eq : D.t = 5 * D.r := D.t_eq_five_mul_r
  have j_le : j.val ≤ D.m := j.2.2
  simp only [Fintype.card_sum, Fintype.card_fin, D.card_rowIndex]
  omega

variable (ϑ : D.Twist)

/-- For the `j`-th pair `W_j, V_j` and the summand `V″` of `V_j` with basis `FirstFactorIndex j`:
the rank of `V″` is at most that of `V_j`, and the diagram `μ⁺`, given by its numbers `colsPlus τ h`
of columns of height `h` at the infinite place `τ`, has no column whose height is at least the rank
of `V″` and below the rank of `V_j`. -/
lemma hasColumnsBelow_colsPlus :
    HasColumnsBelow (D.RowIndex ⊕ Fin D.t) (FirstFactorIndex j) (D.descentPair ϑ j).colsPlus := by
  have k_large : 100 * D.m + 9 < D.k := D.hundred_mul_m_add_nine_lt_k
  have r_add_one : D.r + 1 = D.k + D.m := D.r_add_one
  refine hasColumnsBelow_of_eq_zero ?_ fun τ h h_le ↦ ?_
  · have t_eq : D.t = 5 * D.r := D.t_eq_five_mul_r
    rw [card_firstFactorIndex, D.card_rowIndex_sum_fin]
    omega
  · -- the entry `h - 1` of the row parameter lies below `-w_j`
    have h_rank : D.posRank j ≤ h - 1 := by
      have j_le : j.val ≤ D.m := j.2.2
      rw [card_firstFactorIndex] at h_le
      rw [posRank]
      omega
    have h_below : D.targetParameter τ (h - 1) + D.liftWeight j τ ≤ -D.halfGap :=
      D.targetParameter_add_liftWeight_le_neg_halfGap τ h_rank
    simp only [descentPair]
    omega

/-- For `D.descentPair ϑ j`, its diagram `μ⁻` (`colsMinus`) satisfies `HasColumnsBelow`: the rank of
`V°` is at most that of `V_j` (`D.RowIndex ⊕ Fin D.t`), and `μ⁻` has no column whose height is at
least the rank of `V°` and below the rank of `V_j`. -/
lemma hasColumnsBelow_colsMinus :
    HasColumnsBelow (D.RowIndex ⊕ Fin D.t) D.SecondFactorIndex (D.descentPair ϑ j).colsMinus := by
  refine hasColumnsBelow_of_eq_zero ?_ fun τ h h_le ↦ ?_
  · simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  · -- as `r ≤ h`, both entries of the row parameter in the formula are the entry `0`
    have h_index : D.r - h - 1 = D.r - h := by
      rw [Fintype.card_sum, D.card_rowIndex] at h_le
      omega
    simp only [descentPair, h_index]
    omega

/-- The splitting `V_j = V″ ⊕ V°` of the basis, for the pair `descentPair ϑ j`. The indices of `W_j`
come first in `V″`. The divided directions are given by an arbitrary embedding of `D.CarrierIndex`
in `FirstFactorIndex j`. The splitting and both embeddings in `FirstFactorIndex j` do not depend on
the twist. -/
def splittingV : DividedSplitting (FirstFactorIndex j) D.SecondFactorIndex D.CarrierIndex
  (D.descentPair ϑ j)
    Function.Embedding.inl where
  -- keep the indices of `W_j`, which come first in `V″`, and number the remaining ones
  ε := (Equiv.sumAssoc ..).trans <| (Equiv.sumAssoc ..).trans <|
    Equiv.sumCongr 1 (Fintype.equivFinOfCardEq
      (card_padIndex_sum_flatIndex_sum_secondFactorIndex j))
  fixedEmb := inl.trans Function.Embedding.inl
  equiv_inl_fixedEmb _ := rfl
  dividedEmb := (nonempty_carrierIndex_embedding_firstFactorIndex j).some
  hasColumnsBelow := ⟨hasColumnsBelow_colsPlus j ϑ, hasColumnsBelow_colsMinus j ϑ⟩

/-- The level `J_Λ` on `V″` of a matrix `Λ` modulo `ϖ²`. It is `rowFixingLevel` for the rows of `Λ`
and of `ϖ • 1`: its elements are `1` modulo `ϖ` and fix `Λ` modulo `ϖ²`, and modulo `ϖ² Q`, for `Q`
the product of the twist places, their columns off the indices of `W_j` are those of the identity
matrix. -/
abbrev gluingLevel
    (Λ : Matrix D.CarrierIndex (FirstFactorIndex j)
      (D.descentPair ϑ j).chosenModulusSq.ResidueRing) :
    Subgroup (Gf D.E (FirstFactorIndex j)) :=
  rowFixingLevel (D.descentPair ϑ j).toLevelPlaces ((splittingV j ϑ).stackOverGenScalar Λ)
    (splittingV j ϑ).fixedEmb

/-- The level `J_Λ` (`gluingLevel`) is sufficiently small: at every point `g` the stabiliser
`classAut` is trivial. -/
lemma classAut_gluingLevel_eq_bot
    (Λ : Matrix D.CarrierIndex (FirstFactorIndex j) (D.descentPair ϑ j).chosenModulusSq.ResidueRing)
    (g : Gf D.E (FirstFactorIndex j)) :
    classAut (stdSpace D.E (FirstFactorIndex j)).embFin.range (gluingLevel j ϑ Λ) g = ⊥ := by
  have h_le : gluingLevel j ϑ Λ ≤ D.chosenLevel := rowFixingLevel_le_levelOf (splittingV j ϑ) Λ
  exact D.classAut_eq_bot_of_le_chosenLevel h_le (card_firstFactorIndex_le_two_mul_n j) g

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.univ in
/-- The lattice `L_Λ` of a choice `i` with matrix `Λ = i.1`, given by the matrix `𝗀` (the field
`point`) of a basis. It is chosen once, for the trivial twist, and read as a lattice for the twist
`ϑ`. -/
def glueLattice (i : ChoiceIndex j) : DividedLattice (D.descentPair ϑ j) :=
  { ((splittingV j 1).exists_isGlued i.1).choose with }

/-- A lattice that is glued for the twist `ϑ'` is glued for the twist `ϑ`. -/
lemma isGlued_splittingV_of_isGlued {ϑ' : D.Twist}
    {Λ : Matrix D.CarrierIndex (FirstFactorIndex j) (D.descentPair ϑ'
      j).chosenModulusSq.ResidueRing}
    {L : DividedLattice (D.descentPair ϑ' j)} (hL : (splittingV j ϑ').IsGlued Λ L) :
    (splittingV j ϑ).IsGlued Λ { L with } :=
  -- the conditions on a lattice do not involve the twist, up to unfolding
  { hL with }

/-- The lattice `glueLattice j ϑ i` is glued for the matrix `Λ = i.1` (`IsGlued`): the congruence
modulo `ϖ` that defines it is, after a translation by a unique element of `congruenceGroup`, a
pair of conditions on the blocks `V″` and `V°`, and its inverse is integral on most of `V″`. -/
lemma isGlued_glueLattice (i : ChoiceIndex j) : (splittingV j ϑ).IsGlued i.1 (glueLattice j ϑ i) :=
  isGlued_splittingV_of_isGlued j ϑ ((splittingV j 1).exists_isGlued i.1).choose_spec

/-- The scalar `c_𝗀` of the lattice `L_Λ` does not depend on the twist. -/
lemma weilScalar_glueLattice (i : ChoiceIndex j) :
    (glueLattice j ϑ i).weilScalar = (glueLattice j 1 i).weilScalar := rfl

/-! ### The first factors -/

/-- The constant `c″ ≠ 0` that makes the vectors `c″ Υ_{ϑ,i} (h)` integral away from `Q`, and small
for `ϑ = 1`. Here `Υ_{ϑ,i}` is `leftSideSeries`, a theta kernel times a class sum of theta kernels
formed from the choice `i`. The constant depends neither on the twist nor on the choice. -/
def firstFactorScale : ℂ := (exists_isIntegralAndSmall_leftSideSeries j).choose

lemma firstFactorScale_ne_zero : firstFactorScale j ≠ 0 :=
  (exists_isIntegralAndSmall_leftSideSeries j).choose_spec.1

/-- The first factor `φ″_{ϑ,i}`, the complex conjugate of `c″ Υ_{ϑ,i}`, where `Υ_{ϑ,i}`
(`leftSideSeries`) is a function on the finite points of `U(V″)` and `c″ = firstFactorScale j`. -/
def firstFactor (i : ChoiceIndex j) (h : Gf D.E (FirstFactorIndex j)) :
    WeylIndex (FirstFactorIndex j) (untwistedDescentPair j).colsPlus → ℂ :=
  star (firstFactorScale j • leftSideSeries ϑ j i h)

/-- The theta series `Ξ_{ϑ,i} (g) = ⟨φ″_{ϑ,i}, θ″_{ϑ,Λ} (g, ·)⟩` on `U(W_j)`. It is the sum
(`kernelClassSum`) over the classes `h` of level `J_Λ` of the theta kernel `θ″_{ϑ,Λ}` of
`(W_j, V″)` at `(g, h)`, with datum given by the rows of `Λ` stacked over those of `ϖ • 1`
(`stackOverGenScalar`) and polynomial given by `φ″_{ϑ,i} (h)`. -/
def firstFactorPairing (i : ChoiceIndex j) (g : G D.E (D.signsW j)) : ℂ :=
  kernelClassSum (D.descentPair ϑ j) (firstFactorChar ϑ j) ((splittingV j ϑ).stackOverGenScalar i.1)
    (splittingV j ϑ).fixedEmb (fun h ↦ star (firstFactor j ϑ i h)) g

/-- The series `Ξ_{ϑ,i}` is `c″` times the left side `thirdExchangeLeftSide` of the third exchange,
the class sum over `U(V″)` whose multiple by a number is the twist-free function `choiceFn`. -/
lemma firstFactorPairing_eq_mul_thirdExchangeLeftSide (i : ChoiceIndex j) (g : G D.E (D.signsW j)) :
    firstFactorPairing j ϑ i g = firstFactorScale j * thirdExchangeLeftSide ϑ j i g := by
  have h_rows : Matrix.fromCols 1 0 * (splittingV j ϑ).stackOverGenScalar i.1 = i.1 := by
    -- `erw`, since `stackOverGenScalar` is a `fromRows` only up to unfolding
    erw [Matrix.fromCols_mul_fromRows, Matrix.zero_mul, Matrix.one_mul, add_zero]
  have h_star : (fun h : Gf D.E (FirstFactorIndex j) ↦ star (firstFactor j ϑ i h)) =
      fun h ↦ firstFactorScale j • leftSideSeries ϑ j i h := funext fun h ↦ star_star _
  rw [thirdExchangeLeftSide_eq_kernelClassSum ϑ j h_rows, firstFactorPairing]
  -- rewrite by `h_star` with `congrArg`, as the motive of `rw` is not type correct
  exact (congrArg (kernelClassSum (D.descentPair ϑ j) (firstFactorChar ϑ j) _ _ · g) h_star).trans
    (kernelClassSum_smul (O := D.descentPair ϑ j) ..)

/-- Let `y` be a good form on the hermitian space `W_j = D.spaceW j`. The theta series
`firstFactorPairing j ϑ i` on `U(W_j)` of a twist `ϑ` and a choice `i` is a finite combination of
theta kernels, so its product with `y` is a rapidly decreasing automorphic function. -/
lemma mul_firstFactorPairing_mem_rapidFunctions (y : D.goodForms (D.spaceW j)) (i : ChoiceIndex j) :
    (y : G D.E (D.signsW j) → ℂ) * firstFactorPairing j ϑ i ∈ (D.spaceW j).rapidFunctions := by
  obtain ⟨hy, -⟩ := goodForms_mem_rapidOfLevel y dvd_rfl
  have h_tame (w : FinPlace D.E) (hw : w ∉ ((D.descentPair ϑ j).levelModulus 2).places) :
      (D.descentPair ϑ j).tamePart w = 1 :=
        (D.descentPair ϑ j).tame_eq_one w (places_levelModulus.ge.mt hw)
  -- the class sum is a finite sum of multiples of the products of `y` with a theta kernel
  simp only [firstFactorPairing, kernelClassSum, classSum, finsum_eq_sum_of_fintype, Pi.mul_def,
    Finset.mul_sum, mul_smul_comm, ← Finset.sum_fn]
  refine (D.spaceW j).rapidFunctions.toSubmodule.sum_mem fun h _ ↦ ?_
  rw [← Pi.smul_def]
  exact Submodule.smul_of_tower_mem _ _
    (mul_modKernel_mem_rapidFunctions inferInstance h_tame hy _ _ (1, h.out))

/-- The theta series `firstFactorPairing j ϑ i` on `U(W_j)` depends on the twist `ϑ` only through a
scalar: there are numbers `c ϑ` such that `c ϑ` times the series is `firstFactorScale j` times the
function `choiceFn j i`, neither of which involves `ϑ`, for all choices `i`. Moreover `|c ϑ|²` is a
constant `C`, possibly `0`, divided by `heckeValueProd j ϑ`, a product of three Hecke L-value
factors twisted by `ϑ`. -/
lemma exists_mul_firstFactorPairing_eq : ∃ (C : ℂ) (c : D.Twist → ℂ), ∀ ϑ : D.Twist,
    ‖c ϑ‖ ^ 2 = C / heckeValueProd j ϑ ∧
    ∀ (i : ChoiceIndex j) (g : G D.E (D.signsW j)),
      c ϑ * firstFactorPairing j ϑ i g = firstFactorScale j * choiceFn j i g := by
  obtain ⟨C, c, h_third⟩ := exists_mul_thirdExchangeLeftSide_eq_choiceFn j
  refine ⟨C, c, fun ϑ : D.Twist ↦ ?_⟩
  obtain ⟨h_norm, h_eq⟩ := h_third ϑ
  refine ⟨h_norm, fun i g ↦ ?_⟩
  calc c ϑ * firstFactorPairing j ϑ i g = firstFactorScale j *
         (c ϑ * thirdExchangeLeftSide ϑ j i g) := by
        rw [firstFactorPairing_eq_mul_thirdExchangeLeftSide, mul_left_comm]
    _ = firstFactorScale j * choiceFn j i g := by rw [h_eq]

/-- The number `c′_ϑ` with `c′_ϑ Ξ_{ϑ,i} = c″ 𝖥_i` for all `i`. -/
def twistFactor : D.Twist → ℂ := (exists_mul_firstFactorPairing_eq j).choose_spec.choose

/-- There is a constant `C`, possibly `0`, with `|c′_ϑ|² = C / heckeValueProd j ϑ` for every twist
`ϑ`; the denominator is the product of the Hecke values of the three exchanges. -/
lemma exists_norm_twistFactor_sq_eq :
    ∃ C : ℂ, ∀ ϑ : D.Twist, ‖twistFactor j ϑ‖ ^ 2 = C / heckeValueProd j ϑ :=
  ⟨_, fun ϑ ↦ ((exists_mul_firstFactorPairing_eq j).choose_spec.choose_spec ϑ).1⟩

/-- The defining equation `c′_ϑ Ξ_{ϑ,i} (g) = c″ 𝖥_i (g)` of `twistFactor`, where `𝖥_i`
(`choiceFn`) is a function on `U(W_j)` that does not depend on the twist. -/
lemma twistFactor_mul_firstFactorPairing (i : ChoiceIndex j) (g : G D.E (D.signsW j)) :
    twistFactor j ϑ * firstFactorPairing j ϑ i g = firstFactorScale j * choiceFn j i g :=
  ((exists_mul_firstFactorPairing_eq j).choose_spec.choose_spec ϑ).2 i g

/-- The values of the first factor `φ″_{ϑ,i}` are integral away from the level of `ϑ`, and, if `Q`
is empty, their conjugates have squared norm at most `exp (f m b log² b)` (`IsIntegralAndSmall`). -/
lemma isIntegralAndSmall_firstFactor (i : ChoiceIndex j) (h : Gf D.E (FirstFactorIndex j)) :
    IsIntegralAndSmall ϑ j h (firstFactor j ϑ i h) :=
  (exists_isIntegralAndSmall_leftSideSeries j).choose_spec.2 i ϑ h

/-- Arithmetic of the first factors: the value of `φ″_{ϑ,i}` at `h` is integral (`weylGauge` at
most `1`) at a place above a prime `l` that does not divide the norm of the level of `ϑ`. -/
lemma weylGauge_firstFactor_le_one (i : ChoiceIndex j) (h : Gf D.E (FirstFactorIndex j)) (l : ℕ)
    [Fact l.Prime] [PadicPlace l] (hl : l.Coprime ϑ.1.normQ) :
    weylGauge (untwistedDescentPair j).colsPlus 0 h (firstFactor j ϑ i h) ≤ 1 :=
  (isIntegralAndSmall_firstFactor j ϑ i h).weylGauge_le_one l hl

/-- Arithmetic of the first factors: for the trivial twist, every conjugate
`σ ∘ firstFactor j 1 i h` of the values of `φ″_{1,i}` has squared norm (`weylNormSq`) at most
`exp (D.f * D.m * D.b * D.logB ^ 2)`. -/
lemma weylNormSq_firstFactor_le (i : ChoiceIndex j) (h : Gf D.E (FirstFactorIndex j))
    (σ : ℂ ≃+* ℂ) :
    weylNormSq (σ ∘ firstFactor j 1 i h) ≤ exp (D.f * D.m * D.b * D.logB ^ 2) :=
  (isIntegralAndSmall_firstFactor j 1 i h).weylNormSq_le rfl σ

/-! ### The gluing map and the slices of lifts -/

set_option backward.isDefEq.respectTransparency false in
/-- The gluing map `glue_ϑ`. For `ζ` in the copy `i` of the forms on `V°` it is `M ^ l₁` times the
sum, over the classes `h` of level `J_Λ` and `h°` of level `J (ϖ²)`, of the forms supported on the
class of `(h, h°) 𝗀` formed from the product vector `φ″ (h) · ζ (h°)` (`productForm`). Here `𝗀`
is the matrix of `glueLattice j ϑ i`, `M = D.M`, and `l₁` is
`DividedSplitting.denominatorExponent`, the exponent that repays the denominators of `𝗀`. -/
@[simps -isSimp] def glue : FormTuples j →ₗ[ℂ] (D.descentPair ϑ j).FormV where
  toFun ζ := (D.M ^ (splittingV j ϑ).denominatorExponent : ℂ) • ∑ b :
    ChoiceIndex j × D.SecondFactorClasses,
    stdClassSum (gluingLevel j ϑ b.1.1) fun h : Gf D.E (FirstFactorIndex j) ↦
      (splittingV j ϑ).productForm (glueLattice j ϑ b.1) (h, b.2.out) (firstFactor j ϑ b.1 h) (ζ b)
  map_add' := by
    simp [↓classAut_gluingLevel_eq_bot, classSum, ↓finsum_eq_sum_of_fintype, sum_add_distrib]
  map_smul' a := by
    simp [↓classAut_gluingLevel_eq_bot, smul_comm a, ← smul_sum, classSum,
      ↓finsum_eq_sum_of_fintype]

set_option backward.isDefEq.respectTransparency false in
/-- The period is a sum of slices. Let `φ` be a form on `V_j = V″ ⊕ V°` and `ζ` a tuple of forms on
`V°`. The inner product of `ζ` with the adjoint of the gluing map `glue j ϑ` at `φ` is `M ^ l₁`
(`M = D.M`, `l₁ = denominatorExponent`) times the sum, over the choices `i` with matrix `Λ = i.1`,
the classes `c` of `U(V°)` with representative `h° = c.out` and the classes `h` of `U(V″)` of level
`J_Λ = gluingLevel j ϑ Λ` (`stdClassSum`), of `⟨φ″ (h) · ζ (i, c), φ ((h, h°) 𝗀)⟩` (`gramForm`).
Here `φ″ = firstFactor j ϑ i`, `ε` splits the basis of `V_j` into those of `V″` and `V°`, the
product of vectors is `cartanProduct ε 1`, the point `(h, h°)` is the block matrix
`U.block ε (h, h°)`, and `𝗀` is the matrix of the lattice `glueLattice j ϑ i`. -/
lemma inner_adjoint_glue (φ : (D.descentPair ϑ j).FormV) (ζ : FormTuples j) :
    inner ℂ ζ ((glue j ϑ).adjoint φ) =
      D.M ^ (splittingV j ϑ).denominatorExponent * ∑ i : ChoiceIndex j, ∑ c : D.SecondFactorClasses,
        stdClassSum (gluingLevel j ϑ i.1) fun h : Gf D.E (FirstFactorIndex j) ↦
          gramForm (cartanProduct (splittingV j ϑ).ε 1 (firstFactor j ϑ i h) (ζ (i, c)))
            (φ (U.block (splittingV j ϑ).ε (h, c.out) * (glueLattice j ϑ i).point)) := by
  rw [adjoint_inner_right, glue_apply, inner_smul_left, map_pow, map_natCast, sum_inner,
    sum_prod_type]
  refine congrArg _ (sum_congr rfl fun i _ ↦ sum_congr rfl fun c _ ↦ ?_)
  simp [↓classAut_gluingLevel_eq_bot, sum_inner, DividedSplitting.productForm, inner_classForm,
    classSum, ↓ finsum_eq_sum_of_fintype, apply_eq_evalForm]
  -- the two sides differ only in the implicit level of the forms on `V_j`
  rfl

/-- The character of the lift to `V_j = V″ ⊕ V°`: the product of `ν″ = firstFactorChar` and
`ν° = ν_η ^ (m / 2 - j)` is the character `charV` of `descentPair ϑ j`. All are characters of
`U(1)`, and `ν_η = upsilonU1` is the restriction of the character `υ` to the norm-one ideles. -/
lemma firstFactorChar_mul_upsilonU1_zpow :
    firstFactorChar ϑ j * upsilonU1 ^ (D.m / 2 - j : ℤ) = (D.descentPair ϑ j).charV := by
  -- `m` is even and `k - 1 = r - m`
  have h_exp : (j + (5 * D.r + D.k - 1) / 2 + (D.m / 2 - j) : ℤ) = (D.r + 5 * D.r) / 2 := by
    grind [D.m_eq_two_mul_varrho_add_two, D.r_add_one]
  have t_eq : D.t = 5 * D.r := D.t_eq_five_mul_r
  simp [firstFactorChar, firstFactorCharExp, rankTwist, mul_assoc, ← zpow_natCast, ← zpow_add, t_eq,
    D.card_rowIndex, h_exp]
  -- what remains, `D.liftChar = μ`, is the definition of `descentPair`
  rfl

/-- A good form on `W_j` is invariant under the lifts `liftMod 𝗎` of the elements `𝗎` of the group
`J̄¹` (`congruenceGroup`) of matrices modulo `ϖ²` that are `1` modulo `ϖ`, since these lifts lie in
the level `J (ϖ)` that fixes it. -/
lemma goodForm_mul_liftMod_congruenceGroup (y : D.goodForms (D.spaceW j))
    (u : (splittingV j 1).congruenceGroup) (g : G D.E (D.signsW j)) :
    (y : G D.E (D.signsW j) → ℂ) (g * (1, (liftMod u.val : Gf D.E D.RowIndex))) =
      (y : G D.E (D.signsW j) → ℂ) g := by
  have h_level : (liftMod u.val : Gf D.E D.RowIndex) ∈ levelOf D.chosenPlace ⊥ :=
    mem_levelOf.2 ⟨(liftMod u.val).prop,
      funext ((splittingV j 1).reduceAt_liftMod_congruenceGroup u)⟩
  exact Space.mem_levelSpace_formRep_iff.1 (y : D.principalForms (D.spaceW j)).prop _ h_level g

open scoped Classical in
/-- The descent to `U(W_j)` of the form `glue j ϑ ζ` on `V_j` glued from a tuple `ζ` of forms on
`V°` at the twist `ϑ`. Its conjugate at `g` is the sum, over the choices `i` and the matrices `u`
modulo `ϖ²` that are `1` modulo `ϖ` (`congruenceGroup`), of `M ^ l₁ c Ξ_i (g u) ⟨ζ_i, θ° (g u, ·)⟩`.
Here `M = D.M`, `l₁ = denominatorExponent`, `c` is the scalar `weilScalar` of the lattice of `i`,
`Ξ_i` is the theta series `firstFactorPairing j ϑ i`, the last factor is the pairing
`thetaKernelPairing` of the copy `i` of `ζ` with the theta kernel `θ°` of `W_j, V°`, and `g u` is
`g` times the lift `liftMod u`. -/
lemma conj_normalizedDescent_glue (ϑ' : D.Twist) (ζ : FormTuples j) (g : G D.E (D.signsW j)) :
    conj ((D.descentPair ϑ j).normalizedDescent (glue j ϑ ζ) g) =
      ∑ i : ChoiceIndex j, ∑ u : (splittingV j ϑ').congruenceGroup,
        D.M ^ (splittingV j ϑ').denominatorExponent * (glueLattice j ϑ' i).weilScalar *
          (firstFactorPairing j ϑ i *
            thetaKernelPairing j fun c : D.SecondFactorClasses ↦ ζ (i, c))
              (g * (1, (liftMod u.val : Gf D.E D.RowIndex))) := by
  -- The descent of one term of `glue ζ` is a sum over `u` of products of two kernels.
  let Ξ (b : ChoiceIndex j × D.SecondFactorClasses) : (D.descentPair ϑ j).FormV :=
    stdClassSum (gluingLevel j ϑ b.1.1) fun h : Gf D.E (FirstFactorIndex j) ↦
      (splittingV j ϑ).productForm (glueLattice j ϑ b.1) (h, b.2.out) (firstFactor j ϑ b.1 h) (ζ b)
  let gu (u : (splittingV j ϑ').congruenceGroup) : G D.E (D.signsW j) :=
    g * (1, (liftMod u.val : Gf D.E D.RowIndex))
  let θ (b : ChoiceIndex j × D.SecondFactorClasses) (g' : G D.E (D.signsW j)) : ℂ :=
    modKernelStdSpace (D.spaceW j) (untwistedDescentPair j).charW (upsilonU1 ^ (D.m / 2 - j : ℤ))
      (D.untwistedModulus 2) (Pi.single (inclMatrix (D.untwistedModulus 2).ResidueRing .inl) 1)
      (letterPoly (D.signsW j) (untwistedDescentPair j).numbering (-1)
        (untwistedDescentPair j).colsMinus (star (ζ b))) g' b.2.out
  have h_glue : glue j ϑ ζ = (D.M ^ (splittingV j ϑ').denominatorExponent : ℂ) • ∑ b, Ξ b :=
    glue_apply j ϑ ζ
  have h_term (b : ChoiceIndex j × D.SecondFactorClasses) :
      (D.descentPair ϑ j).normalizedDescent (Ξ b) g = conj ((glueLattice j ϑ' b.1).weilScalar *
        ∑ u, firstFactorPairing j ϑ b.1 (gu u) * θ b (gu u)) :=
    (splittingV j ϑ).normalizedDescent_stdClassSum_productForm (isGlued_glueLattice j ϑ b.1)
      (firstFactorChar_mul_upsilonU1_zpow j ϑ) b.2.out (firstFactor j ϑ b.1) (ζ b) g
  have h_pairing (i : ChoiceIndex j) (g' : G D.E (D.signsW j)) :
      thetaKernelPairing j (fun c ↦ ζ (i, c)) g' = ∑ c, θ (i, c) g' := rfl
  have h_descent : (D.descentPair ϑ j).normalizedDescent (glue j ϑ ζ) g =
      (D.M ^ (splittingV j ϑ').denominatorExponent : ℂ) *
        ∑ b, (D.descentPair ϑ j).normalizedDescent (Ξ b) g := by
    rw [h_glue, map_smul, map_sum]
    exact congrArg (fun z : ℂ ↦ (D.M ^ (splittingV j ϑ').denominatorExponent : ℂ) * z)
      (Finset.sum_apply g univ fun b ↦ (D.descentPair ϑ j).normalizedDescent (Ξ b))
  simp only [h_descent, h_term, h_pairing, Pi.mul_apply, mul_sum, map_sum, map_mul,
    map_pow, map_natCast, Complex.conj_conj, sum_prod_type (α₂ := D.SecondFactorClasses), mul_assoc]
  exact sum_congr rfl fun i _ ↦ sum_comm

/-- Let `y` be a good form on `W_j`, `D.goodLift ϑ j y` its theta lift to `V_j` at the twist `ϑ`,
and `ζ` a tuple of forms on `V°`. The inner product of `ζ` with the adjoint of the gluing map
`glue j ϑ` at the lift is the integral, over `U(W_j)` modulo its rational points (`quotMeasure`), of
`y` against the conjugate of the descent `normalizedDescent` of `glue j ϑ ζ`, its pairing with the
theta kernel. -/
lemma inner_adjoint_glue_goodLift_eq_integral (y : D.goodForms (D.spaceW j)) (ζ : FormTuples j) :
    inner ℂ ζ ((glue j ϑ).adjoint (D.goodLift ϑ j y)) =
      ∫ g : G D.E (D.signsW j), (y : G D.E (D.signsW j) → ℂ) g *
        conj ((D.descentPair ϑ j).normalizedDescent (glue j ϑ ζ) g) ∂(D.spaceW j).quotMeasure := by
  -- The lift of `y` is `∫ y(g) θ(g, ·) dg`, and `⟨θ(g, ·), glue ζ⟩` is the descent of `glue ζ`.
  set μ : Measure (G D.E (D.signsW j)) := (D.spaceW j).quotMeasure
  let θ (g : G D.E (D.signsW j)) : (D.descentPair ϑ j).FormV :=
    (D.descentPair ϑ j).vectorKernelForm g
  have h_lift : D.goodLift ϑ j y = ∫ g, (y : G D.E (D.signsW j) → ℂ) g • θ g ∂μ :=
    D.singleLift_eq_integral ϑ y.val
  have h_integrable : Integrable (fun g ↦ (y : G D.E (D.signsW j) → ℂ) g • θ g) μ :=
    (D.descentPair ϑ j).integrable_smul_vectorKernelForm (D.fitsParams_descentPair ϑ j) y.val.val
  have h_descent (g : G D.E (D.signsW j)) :
      (D.descentPair ϑ j).normalizedDescent (glue j ϑ ζ) g = inner ℂ (θ g) (glue j ϑ ζ) :=
    (D.descentPair ϑ j).normalizedDescent_eq_inner_vectorKernelForm (glue j ϑ ζ) g
  rw [adjoint_inner_right, h_lift, ← integral_inner h_integrable]
  simp [h_descent, inner_smul_right]

/-- The product of a good form `y` on `W_j`, the series `Ξ_i = firstFactorPairing j ϑ i` and the
pairing `⟨ζ, θ° (g, ·)⟩` (`thetaKernelPairing`) is a rapidly decreasing automorphic function. -/
lemma mul_mul_thetaKernelPairing_mem_rapidFunctions (y : D.goodForms (D.spaceW j))
    (i : ChoiceIndex j) (ζ : D.SecondFactorClasses → SecondFactorFormValues j) :
    (y : G D.E (D.signsW j) → ℂ) * firstFactorPairing j ϑ i * thetaKernelPairing j ζ ∈
      (D.spaceW j).rapidFunctions := by
  -- the pairing is a finite sum of theta kernels
  simp only [funext (thetaKernelPairing.eq_1 j ζ), ← Finset.sum_fn, Finset.mul_sum]
  exact (D.spaceW j).rapidFunctions.toSubmodule.sum_mem fun c _ ↦
    mul_modKernel_mem_rapidFunctions (hasWeight_upsilonU1_zpow _) (by simp)
      (mul_firstFactorPairing_mem_rapidFunctions j ϑ y i) _ _ (1, c.out)

/-- Let `y` be a good form on `W_j`, `D.goodLift ϑ j y` its theta lift to `V_j` at the twist `ϑ`,
and `ζ` a tuple of forms on `V°` with one copy `ζ_i` for each choice `i`. The inner product of `ζ`
with the adjoint of the gluing map `glue j ϑ` at the lift is the sum over `i` of
`M ^ l₁ c #J̄¹ ∫ y (g) Ξ_i (g) ⟨ζ_i, θ° (g, ·)⟩ dg`. Here `M = D.M` is the principal level,
`l₁ = denominatorExponent`, `c` is the scalar `weilScalar` of the lattice of `i` and `J̄¹`
(`congruenceGroup`) the group of matrices modulo `ϖ²` that are `1` modulo `ϖ`, all taken at the
trivial twist `1`. The series `Ξ_i` is `firstFactorPairing j ϑ i`, `thetaKernelPairing` pairs with
the theta kernel `θ°` of `W_j, V°`, and `quotMeasure` integrates over the quotient of `U(W_j)` by
its rational points. -/
lemma inner_adjoint_glue_goodLift_eq_sum_integral (y : D.goodForms (D.spaceW j))
    (ζ : FormTuples j) :
    inner ℂ ζ ((glue j ϑ).adjoint (D.goodLift ϑ j y)) =
      ∑ i : ChoiceIndex j, D.M ^ (splittingV j 1).denominatorExponent *
        (glueLattice j 1 i).weilScalar *
        Nat.card (splittingV j 1).congruenceGroup *
        ∫ g : G D.E (D.signsW j),
          (y : G D.E (D.signsW j) → ℂ) g * firstFactorPairing j ϑ i g *
            thetaKernelPairing j (fun c : D.SecondFactorClasses ↦ ζ (i, c)) g
              ∂(D.spaceW j).quotMeasure := by
  classical
  -- Write the theta integral of `glue j ϑ ζ` against `y` as a sum over `i` and `𝗎 ∈ J̄¹` of
  -- translates of `a i * f i`. Translation does not change the integral, so both sides are the
  -- sum of `a i * ∫ f i` over all `i` and all `𝗎`.
  let V := splittingV j 1
  set μ : Measure (G D.E (D.signsW j)) := (D.spaceW j).quotMeasure
  let f (i : ChoiceIndex j) : G D.E (D.signsW j) → ℂ :=
    (y : G D.E (D.signsW j) → ℂ) * firstFactorPairing j ϑ i * thetaKernelPairing j fun c ↦ ζ (i, c)
  let a (i : ChoiceIndex j) : ℂ := D.M ^ V.denominatorExponent * (glueLattice j 1 i).weilScalar
  -- the point `(1, 𝗎)` of `U(W_j)` given by the lift of `𝗎 ∈ J̄¹`
  let k (u : V.congruenceGroup) : G D.E (D.signsW j) := (1, (liftMod u.val : Gf D.E D.RowIndex))
  -- The measure is invariant under right translation, so all `𝗎` give the same integral.
  have h_same (i : ChoiceIndex j) (u : V.congruenceGroup) :
      ∫ g, f i (g * k u) ∂μ = ∫ g, f i g ∂μ ∧ Integrable (fun g ↦ f i (g * k u)) μ := by
    obtain ⟨⟨h_cont, h_rat⟩, h_rapid⟩ :=
      mul_mul_thetaKernelPairing_mem_rapidFunctions j ϑ y i fun c ↦ ζ (i, c)
    exact (Space.integral_comp_mul_right (V := D.spaceW j) (liftMod u.val) h_rat h_cont).imp_right
      fun ⟨_, h_integrable⟩ ↦ h_integrable (h_rapid.integrable h_cont)
  -- Expand the descent of the glued form; the form `y` is invariant under the points `k u`.
  have h_point (g : G D.E (D.signsW j)) :
      (y : G D.E (D.signsW j) → ℂ) g * conj ((D.descentPair ϑ j).normalizedDescent (glue j ϑ ζ) g) =
      ∑ x : ChoiceIndex j × V.congruenceGroup, a x.1 * f x.1 (g * k x.2) := by
    rw [conj_normalizedDescent_glue j ϑ 1, sum_prod_type (α₂ := V.congruenceGroup)]
    simp only [a, f, k, V, Pi.mul_apply, goodForm_mul_liftMod_congruenceGroup j y, mul_sum,
      mul_assoc, mul_left_comm ((y : G D.E (D.signsW j) → ℂ) g)]
  calc inner ℂ ζ ((glue j ϑ).adjoint (D.goodLift ϑ j y))
      = ∫ g, (y : G D.E (D.signsW j) → ℂ) g *
          conj ((D.descentPair ϑ j).normalizedDescent (glue j ϑ ζ) g) ∂μ :=
        inner_adjoint_glue_goodLift_eq_integral j ϑ y ζ
    _ = ∑ x : ChoiceIndex j × V.congruenceGroup, a x.1 * ∫ g, f x.1 g ∂μ := by
        rw [funext h_point, integral_finsetSum _ fun x _ ↦ (h_same ..).2.const_mul (a x.1)]
        simp only [integral_const_mul, h_same]
    _ = ∑ i : ChoiceIndex j, a i * Nat.card V.congruenceGroup * ∫ g, f i g ∂μ := by
        simp [sum_prod_type (α₂ := V.congruenceGroup), mul_assoc,
          mul_left_comm (Fintype.card _ : ℂ)]
    _ = _ := by simp only [a, f, V, Pi.mul_apply]

/-! ### Integrality and size of the gluing map -/

/-- The gluing map `glue j ϑ`, from tuples of forms on `V°` to forms on `V_j`, keeps integrality.
Let `l` be a prime coprime to `ϑ.1.normQ`, the product of the norms of the places in the set Q of
the twist `ϑ`. Let `φ` be an embedding of `ℂ` in `ℂ_l` (`PadicPlace l`). If all values of the tuple
`ζ` are integral at `φ`, so are all values of `glue j ϑ ζ`. -/
lemma glue_mem_integralForms {l : ℕ} [Fact l.Prime] (φ : PadicPlace l)
    (hl : l.Coprime ϑ.1.normQ) {ζ : FormTuples j} (hζ : IsIntegralFormTuple φ ζ) :
    glue j ϑ ζ ∈ LevelForm.integralForms φ := by
  -- All stabilisers are trivial, so `glue ζ` is `M ^ l₁` times a plain sum of forms supported on
  -- one class, and it is enough to bound the gauge of each term.
  simp_rw [glue_apply, classSum, finsum_eq_sum_of_fintype, smul_sum]
  refine sum_mem fun b _ ↦ sum_mem fun h _ g ↦ ?_
  simp only [classAut_gluingLevel_eq_bot j ϑ b.1.1, Subgroup.card_bot, Nat.cast_one, inv_one,
    one_smul]
  have h_M_mem : ↑D.M ∈ ((D.descentPair ϑ j).levelModulus 1 false).ideal :=
    D.ideal_untwistedModulus_eq_span.ge (by simp [← piM_mul_star, Ideal.mul_mem_right])
  -- The gauge of such a form is at most that of its vector `φ″ (h) · ζ (h°)`, and this is at most
  -- `‖M‖⁻¹ ^ l₁` times the gauges of the two integral factors. Default transparency is needed to
  -- recognise that product vector inside the form.
  grw (transparency := default) [weylGauge_smul, weylGauge_deltaForm_le isOfFinOrder_level_char,
    (splittingV j ϑ).weylGauge_cartanProduct_le h_M_mem (isGlued_glueLattice j ϑ b.1),
    weylGauge_firstFactor_le_one j ϑ _ _ l hl, hζ b]
  · simp [mul_inv_le_one]
  · simp [weylGauge]

/-- For the untwisted descent pair `untwistedDescentPair j`, at each infinite place `τ` and height
`i`, the number `colsMinus τ i` of columns of the diagram `μ⁻` is at most `D.gap`. -/
lemma colsMinus_le (τ : NumberField.InfinitePlace D.E) (i : ℕ) :
    (untwistedDescentPair j).colsMinus τ i ≤ D.gap := by
      grind [add_mul, descentPair, targetParameter_eq]

variable (D) in
/-- The rank of `V°` is at most `t = 5 r`. -/
lemma card_secondFactorIndex_le : card D.SecondFactorIndex ≤ D.t := by
  rw [Fintype.card_sum, Fintype.card_fin, D.card_rowIndex]
  grind [D.hundred_mul_m_add_nine_lt_k, D.r_add_one, D.t_eq_five_mul_r]

/-- The diagram `μ⁻` has few boxes: at each place it has at most `D.gap` columns of each height, and
the heights are below the rank of `V°`, which is at most `t`. -/
lemma sum_mul_colsMinus_le :
    ∑ τ : D.Φ, ∑ i ∈ range (card D.SecondFactorIndex), i * (untwistedDescentPair j).colsMinus τ i ≤
      card D.Φ * (D.t * (D.t * D.gap)) := by
  have h_rank : card D.SecondFactorIndex ≤ D.t := card_secondFactorIndex_le D
  have h_term (τ : NumberField.InfinitePlace D.E) (i : ℕ)
    (hi : i ∈ range (card D.SecondFactorIndex)) :
      i * (untwistedDescentPair j).colsMinus τ i ≤ D.t * D.gap :=
    Nat.mul_le_mul ((mem_range_le hi).trans h_rank) (colsMinus_le j τ i)
  grw [sum_le_sum fun τ _ ↦ sum_le_card_nsmul _ _ _ (h_term τ), h_rank]
  simp

/-- The diagram `μ⁻` has few boxes, so its hook number (`hookNumberMinus`) is at most
`exp (x ^ 999)`, with `x = D.x` the length of the prime sum. -/
lemma hookNumberMinus_le : (hookNumberMinus j : ℝ) ≤ exp (D.x ^ 999) := by
  set L : ℕ := card D.Φ * (D.t * (D.t * D.gap)) with hL
  have h_hook : hookNumberMinus j ≤ ((L : ℤ) ^ L) ^ 3 := hookNumber_le (sum_mul_colsMinus_le j)
  have h_size : (3 : ℝ) * (L * L) ≤ D.x ^ 999 := by simpa [hL] using D.le_of_hasLogBound
  calc (hookNumberMinus j : ℝ) ≤ ((L : ℝ) ^ L) ^ 3 := mod_cast h_hook
    _ ≤ exp (3 * (L * L)) := by
        refine le_exp_of_log_le ?_
        grw [log_pow, log_pow, log_le_self (Nat.cast_nonneg L), Nat.cast_ofNat]
    _ ≤ exp (D.x ^ 999) := exp_le_exp.2 h_size

/-- The diagram `μ⁻` has few boxes, so the number of basis tensors of its shape with rows indexed by
the basis `D.SecondFactorIndex` of `V°` (`ColumnFilling`) is at most `exp (x ^ 999)`, with `x = D.x`
the length of the prime sum. -/
lemma card_columnFilling_colsMinus_le :
    (Nat.card (ColumnFilling (fun _ : NumberField.InfinitePlace D.E ↦ D.SecondFactorIndex)
      (untwistedDescentPair j).colsMinus) : ℝ) ≤ exp (D.x ^ 999) := by
  set L : ℕ := card D.Φ * (D.t * (D.t * D.gap)) with hL
  have h_card : Nat.card (ColumnFilling (fun _ ↦ D.SecondFactorIndex)
      (untwistedDescentPair j).colsMinus) ≤ (D.t + 1) ^ L :=
    GL.card_columnFilling_le (by omega)
      (fun _ ↦ (card_secondFactorIndex_le D).trans D.t.le_succ) (sum_mul_colsMinus_le j)
  have h_size : (L : ℝ) * (D.t + 1 : ℕ) ≤ D.x ^ 999 := by simpa [hL] using D.le_of_hasLogBound
  grw [h_card]
  refine le_exp_of_log_le ?_
  grw [← h_size, Nat.cast_pow, log_pow,
    log_le_self (Nat.cast_nonneg _)]

variable {j} in
/-- If the index type `n` has at most `2 * D.n D.m` elements, a level `K` that contains `J (ϖ²)`
(`principalLevel n (D.piM ^ 2)`) has at most `exp D.b` classes (`StdClasses K`). -/
lemma card_stdClasses_le_exp_of_le {n : Type} [Fintype n] [DecidableEq n] {K : Subgroup (Gf D.E n)}
    (hK : principalLevel n (D.piM ^ 2) ≤ K) (hn : card n ≤ 2 * D.n D.m) :
    Nat.card (StdClasses K) ≤ exp D.b := by
  have hK' : principalLevel n ((D.M ^ 2 : ℕ) : NumberField.RingOfIntegers D.E) ≤ K :=
    (principalLevel_le_of_dvd (by simp [← piM_mul_star])).trans hK
  exact (D.card_stdClasses_le_exp_mul_log _ hn hK').trans (exp_le_exp.2 D.le_of_hasLogBound)

/-- At the trivial twist the level `J_Λ` (`gluingLevel`) of a choice, whose matrix `Λ` is its
first component, contains `J (ϖ²)`. -/
lemma principalLevel_le_gluingLevel (i : ChoiceIndex j) :
    principalLevel (FirstFactorIndex j) (D.piM ^ 2) ≤ gluingLevel j 1 i.1 := by
  -- At the trivial twist the modulus of the level unfolds to `ϖ²`.
  with_unfolding_all
    exact Modulus.principalLevel_le_levelOfSubgroup (D.ideal_untwistedModulus_eq_span.ge (by simp))

/-- The bound `(M ^ l₁)² · exp b · (n · exp b · G)² ≤ exp (f m b log² b)`. Here `M = D.M` is the
principal level, `l₁ = DividedSplitting.denominatorExponent` the exponent of `M` in the denominator
for the splitting `V_j = V″ ⊕ V°`, `exp b` bounds the numbers of classes of `U(V_j)` and `U(V″)`,
`n` the number of pairs of a choice and a class of `U(V°)`, `G = D.chosenGroupOrder` the bound on
the orders of the stabilisers, `f = D.f` the number of infinite places, `m = D.m` the number of
lifts and `b = D.b` the weight at the `b`-places, with `log b = D.logB`. -/
lemma M_pow_denominatorExponent_sq_mul_le_exp :
    (D.M ^ (splittingV j 1).denominatorExponent) ^ 2 * (exp D.b *
      (card (ChoiceIndex j × D.SecondFactorClasses) * (exp D.b * D.chosenGroupOrder)) ^ 2) ≤
      exp (D.f * D.m * D.b * D.logB ^ 2) := by
  have hM : (1 : ℝ) ≤ D.M := mod_cast NeZero.one_le
  have h_aut : 0 < D.chosenGroupOrder := NeZero.pos _
  set L : ℕ := card D.Φ * (D.t * (D.t * D.gap)) with hL
  have h_det (τ : NumberField.InfinitePlace D.E) :
      ∑ i ∈ range (card (FirstFactorIndex j)), (untwistedDescentPair j).colsPlus τ i ≤
        D.natB + D.offWeight + D.gap + D.m * D.gap := by grind [card_detIndex j τ]
  set e : ℕ := card D.Φ * (3 * D.m * (D.natB + D.offWeight + D.gap + D.m * D.gap)) + L with he
  have h_exponent : (splittingV j 1).denominatorExponent ≤ e := by
    grw [DividedSplitting.denominatorExponent, h_det, colsMinus_le]
    simp only [sum_const, Finset.card_range, card_univ, smul_eq_mul]
    grw [card_secondFactorIndex_le D]
    simp [he, hL, mul_add, ← Nat.succ_mul]
  have h_ring : Nat.card (D.untwistedModulus 2).ResidueRing ≤
      (D.M ^ 2) ^ (2 * Core.numInfPlaces (P.E D.towerExp)) :=
    Modulus.card_residueRing_le (D.ideal_untwistedModulus_eq_span.ge
      (by simp [← piM_mul_star, Ideal.mem_span_singleton])) (NeZero.pos _)
  have h_card : card (ChoiceIndex j × D.SecondFactorClasses) ≤
      (Nat.card (D.untwistedModulus 2).ResidueRing ^ card (FirstFactorIndex j)) ^ card
        D.CarrierIndex *
        (exp D.b * ((card D.FlatIndex ^ (2 * D.m)) ^ D.reducedHalfGap) ^ card D.Φ) * exp D.b := by
    -- Each of the two sets of classes has at most `exp b` elements.
    have h_flat : Nat.card (StdClasses (principalLevel D.FlatIndex (D.piM ^ 2))) ≤ exp D.b :=
      card_stdClasses_le_exp_of_le le_rfl (by
        grind [Fintype.card_fin, D.six_mul_r_le_n, D.hundred_mul_m_add_nine_lt_k, D.r_add_one])
    have h_second :
        Nat.card (StdClasses (principalLevel D.SecondFactorIndex (D.piM ^ 2))) ≤ exp D.b :=
      card_stdClasses_le_exp_of_le le_rfl (by
        grind [card_secondFactorIndex_le D, D.six_mul_r_le_n, D.t_eq_five_mul_r])
    nth_grw 1 [← h_flat]
    grw [← h_second]
    -- What is left counts the matrices, the two sets of classes and the selections of rows.
    simp [↓Nat.card_prod, ↓card_eq_nat_card (α := _ × _), Matrix, mul_assoc]
  -- The logarithms of the bounds on the number of matrices and of selections of rows.
  set a : ℝ := card D.CarrierIndex * (card (FirstFactorIndex j) *
    ((2 * Core.numInfPlaces (P.E D.towerExp) : ℕ) * (2 * log D.M))) with ha
  have h_rows : card D.Φ * (D.reducedHalfGap * ((2 * D.m : ℕ) * log (card D.FlatIndex))) ≤
      card D.Φ * (D.halfGap * ((2 * D.m : ℕ) * (card D.FlatIndex : ℝ))) := by
    grw [log_le_self (Nat.cast_nonneg _), reducedHalfGap, Nat.sub_le]
  have h_size : 2 * (e * log D.M) + (D.b + 2 * (a + (D.b +
      card D.Φ * (D.halfGap * ((2 * D.m : ℕ) * (card D.FlatIndex : ℝ)))) + D.b +
      (D.b + log D.chosenGroupOrder))) ≤ D.f * D.m * D.b * D.logB ^ 2 := by
    simpa [ha, he, hL, D.t_eq_five_mul_r, card_firstFactorIndex j, add_assoc] using
      D.le_of_hasLogBound
  have h_flat_pos : 0 < card D.FlatIndex := Fintype.card_pos
  grw [h_exponent, h_card, h_ring]
  refine le_exp_of_log_le ?_
  grw [← h_size, ← h_rows]
  simp (disch := positivity) only [ha, log_mul, log_pow, log_exp, Nat.cast_pow, Nat.cast_ofNat,
    le_refl]

/-- One term of the gluing map at the trivial twist. Let `p = (i, c)` be a choice and a class of
`U(V°)`, `h` a finite point of `U(V″)` and `g` one of `U(V_j)`. Take the form on `V_j`
(`productForm`) supported on the class of `(h, c.out)` times the matrix of `glueLattice j 1 i`, made
from the product of the vectors `firstFactor j 1 i h` and `ζ p`. Let `σ` be a field automorphism of
`ℂ`. The squared norm (`weylNormSq`) of the value of this form at `g`, moved by `σ`, is at most
`A² exp (f m b log² b) ‖ζ‖_σ²`. Here `‖ζ‖_σ² = formTupleNormSq σ ζ`, `A = D.chosenGroupOrder` bounds
the orders of the stabilisers, `f` is the number of infinite places, `m` the number of lifts and `b`
the weight `exp D.logB`. -/
lemma weylNormSq_evalForm_productForm_le (ζ : FormTuples j) (σ : ℂ ≃+* ℂ)
    (p : ChoiceIndex j × D.SecondFactorClasses) (h : Gf D.E (FirstFactorIndex j))
    (g : Gf D.E (D.RowIndex ⊕ Fin D.t)) :
    weylNormSq (σ ∘ evalForm g ((splittingV j 1).productForm (glueLattice j 1 p.1) (h, p.2.out)
        (firstFactor j 1 p.1 h) (ζ p))) ≤
      D.chosenGroupOrder ^ 2 * (exp (D.f * D.m * D.b * D.logB ^ 2) * formTupleNormSq σ ζ) := by
  obtain ⟨h_plus, h_minus⟩ := (splittingV j 1).hasColumnsBelow
  let V := splittingV j 1
  let x : Gf D.E (D.RowIndex ⊕ Fin D.t) := U.block V.ε (h, p.2.out) * (glueLattice j 1 p.1).point
  let a : ℕ := Nat.card (classAut stdEmbFin.range (D.descentPair (1 : D.Twist) j).levelGroup x)
  have h_aut : a ≤ D.chosenGroupOrder :=
    Nat.le_of_dvd (NeZero.pos _) (D.card_classAut_dvd_chosenGroupOrder
      (card_rowIndex_sum_fin_le_two_mul_n D) levelOf_le_stdLevel x)
  have h_map : σ ∘ cartanProduct V.ε 1 (firstFactor j 1 p.1 h) (ζ p) =
      cartanProduct V.ε 1 (σ ∘ firstFactor j 1 p.1 h) (σ ∘ ζ p) :=
    map_cartanProduct h_plus h_minus V.ε (firstFactor j 1 p.1 h) (ζ p) σ.toRingHom
  have h_first : weylNormSq (σ ∘ firstFactor j 1 p.1 h) ≤ exp (D.f * D.m * D.b * D.logB ^ 2) :=
    weylNormSq_firstFactor_le j p.1 h σ
  have h_second : weylNormSq (σ ∘ ζ p) ≤ formTupleNormSq σ ζ :=
    single_le_sum (fun q _ ↦ weylNormSq_nonneg (σ ∘ ζ q)) (mem_univ p)
  -- A form supported on one class costs the order of a stabiliser, and the norm of the product
  -- vector is the product of the norms.
  calc _ ≤ a ^ 2 * weylNormSq (σ ∘ cartanProduct V.ε 1 (firstFactor j 1 p.1 h) (ζ p)) :=
        weylNormSq_deltaForm_le isOfFinOrder_level_char σ x _ g
    _ = a ^ 2 * (weylNormSq (σ ∘ firstFactor j 1 p.1 h) * weylNormSq (σ ∘ ζ p)) :=
        by rw [h_map, weylNormSq_cartanProduct h_plus h_minus]
    _ ≤ _ := mul_le_mul (by gcongr)
        (mul_le_mul h_first h_second (weylNormSq_nonneg _) (exp_pos _).le)
        (mul_nonneg (weylNormSq_nonneg _) (weylNormSq_nonneg _)) (sq_nonneg _)

/-- At the trivial twist `1`, every place `placeAt i` of the level of `V_j` (the places of
`descentPair 1 j`) contains `piM ^ 2`. -/
lemma piM_sq_mem_placeAt_descentPair_one
    (i : (D.descentPair (1 : D.Twist) j).ChosenIndex ⊕ (D.descentPair (1 : D.Twist) j).TwistIndex) :
    D.piM ^ 2 ∈ ((D.descentPair (1 : D.Twist) j).placeAt i).asIdeal := by
  obtain ⟨w, -, h_mem, -⟩ | i := i
  · exact Ideal.pow_mem_of_mem _ h_mem 2 two_pos
  · exact nomatch i

/-- Norm bound for the gluing map at the trivial twist: for a tuple `ζ` of forms on `V°` and an
automorphism `σ` of `ℂ`, the squared norm `normSqAt σ` of the form `glue j 1 ζ` on `V_j` is at most
`exp (2 f m b log² b)` times `‖ζ‖_σ²` (`formTupleNormSq`). Here `f` is the number of infinite
places, `m` the number of lifts and `b` the weight `exp D.logB`. -/
lemma normSqAt_glue_le (ζ : FormTuples j) (σ : ℂ ≃+* ℂ) :
    (glue j (1 : D.Twist) ζ).normSqAt σ ≤
      exp (2 * (D.f * D.m * D.b * D.logB ^ 2)) * formTupleNormSq σ ζ := by
  -- Each value of each term of `glue ζ` has norm at most `√(chosenGroupOrder ^ 2 * S)`. The norm of
  -- a sum is at most its number of terms times this; `M_pow_denominatorExponent_sq_mul_le_exp`
  -- collects these numbers and `M ^ l₁`.
  rw [two_mul, exp_add, mul_assoc]
  set S : ℝ := exp (D.f * D.m * D.b * D.logB ^ 2) * formTupleNormSq σ ζ
  have hS : 0 ≤ S := by simp [S, formTupleNormSq, exp_pos, Finset.sum_nonneg]
  let v (g : Gf D.E (D.RowIndex ⊕ Fin D.t)) := ∑ p : ChoiceIndex j × D.SecondFactorClasses,
    stdClassSum (gluingLevel j 1 p.1.1) fun h ↦ evalForm g ((splittingV j 1).productForm
      (glueLattice j 1 p.1) (h, p.2.out) (firstFactor j 1 p.1 h) (ζ p))
  set N : ℕ := card (ChoiceIndex j × D.SecondFactorClasses)
  set c : ℝ := (D.M ^ (splittingV j 1).denominatorExponent) ^ 2 with hc
  let K : Subgroup (Gf D.E (D.RowIndex ⊕ Fin D.t)) := (D.descentPair (1 : D.Twist) j).levelGroup
  have h_value (g : Gf D.E (D.RowIndex ⊕ Fin D.t)) :
      √(weylNormSq (σ ∘ v g)) ≤ N • (exp D.b * √(D.chosenGroupOrder ^ 2 * S)) := by
    refine (sqrt_weylNormSq_sum_le ..).trans (sum_le_card_nsmul _ _ _ fun p _ ↦ ?_)
    grw [← card_stdClasses_le_exp_of_le (principalLevel_le_gluingLevel j p.1)
      (card_firstFactorIndex_le_two_mul_n j)]
    exact sqrt_weylNormSq_classSum_le σ fun h ↦
      sqrt_le_sqrt (weylNormSq_evalForm_productForm_le j ζ σ p h g)
  have h_classes : Nat.card (DoubleCosets stdRatPoints K) ≤ exp D.b :=
    card_stdClasses_le_exp_of_le (principalLevel_le_levelOf (piM_sq_mem_placeAt_descentPair_one j))
      (card_rowIndex_sum_fin_le_two_mul_n D)
  calc (glue j (1 : D.Twist) ζ).normSqAt σ
      = c * classSum stdRatPoints K fun g ↦ weylNormSq (σ ∘ v g) := by
        simp only [glue_apply, LevelForm.normSqAt, apply_eq_evalForm]
        simp [hc, v, K, ← mul_classSum, map_classSum]
    _ ≤ c * (exp D.b * (N • (exp D.b * √(D.chosenGroupOrder ^ 2 * S))) ^ 2) := by
        grw [classSum_le_card_mul_sq h_value, h_classes]
    _ = c * (exp D.b * (N * (exp D.b * D.chosenGroupOrder)) ^ 2) * S := by
        simp (disch := positivity) [mul_pow, sq_sqrt, mul_assoc]
    _ ≤ exp (D.f * D.m * D.b * D.logB ^ 2) * S := by
        grw [M_pow_denominatorExponent_sq_mul_le_exp j]

/-! ### Periods of false lifts -/

open scoped Classical in
/-- Let `Ξ` be a form on `V_j`, for the pair `W_j, V_j` at the twist `ϑ` (`descentPair ϑ j`), in the
image of the idempotent `D.e₀` of the group algebra of `∏ GL_r (k_w)` over the residue fields `k_w`
of the chosen places `w`. Let `v` give a vector in `k_w ^ r` at each chosen place, not `0` at the
place `i`. Then `Ξ` is killed by the pure tensor of the elements `∑ χ_w (det h)⁻¹ h`, summed over
the invertible `h = 1 + u vᵀ` (`hyperplaneSum`), where `χ_w` is the residue character `tamePart`. -/
lemma hyperplaneSum_apply_eq_zero {Ξ : (D.descentPair ϑ j).FormV}
    (hΞ : Ξ ∈ (groupAlgAction (D.descentPair ϑ j) D.e₀).range) (i : (D.descentPair ϑ j).ChosenIndex)
    (v : ∀ k : (D.descentPair ϑ j).ChosenIndex,
      D.RowIndex → ResField ((D.descentPair ϑ j).chosenPlace k)) (hv : v i ≠ 0) :
    (D.descentPair ϑ j).formAction.asAlgebraHom
      (piTensorElem fun k : (D.descentPair ϑ j).ChosenIndex ↦
        hyperplaneSum ((D.descentPair ϑ j).tamePart ((D.descentPair ϑ j).chosenPlace k)) (v k)) Ξ =
          0 := by
  obtain ⟨x, rfl⟩ := hΞ
  have h_mem : D.piM ∈ (D.chosenPlace i).asIdeal := by
    obtain ⟨k, w, h_mem, -⟩ := i
    exact h_mem
  have h_tame : ϑ.tamePart (D.chosenPlace i) = 1 := ϑ.tamePart_eq_one _ fun h_mem_Q ↦ by
    obtain ⟨-, h_notMem, -⟩ := D.normQ_mem_and_notMem_of_mem_Q ϑ (.inl h_mem_Q)
    exact h_notMem h_mem
  set T : MonoidAlgebra ℂ ((D.descentPair ϑ j).ChosenGL D.RowIndex) := piTensorElem fun k ↦
    hyperplaneSum ((D.descentPair ϑ j).tamePart ((D.descentPair ϑ j).chosenPlace k)) (v k)
  let e₀ : MonoidAlgebra ℂ ((D.descentPair ϑ j).ChosenGL D.RowIndex) := D.e₀
  have h_kill : T * e₀ = 0 :=
    D.hyperplaneSum_mul_e₀ (x := fun k ↦ hyperplaneSum
      ((D.descentPair ϑ j).tamePart ((D.descentPair ϑ j).chosenPlace k)) (v k))
      i (D.chiMLocal_zpow_mul_pow_eq_one j h_tame) hv rfl
  let ρ := (D.descentPair ϑ j).formAction.asAlgebraHom
  calc ρ T (ρ e₀ x) = ρ (T * e₀) x := (LinearMap.congr_fun (map_mul ρ T e₀) x).symm
    _ = 0 := by rw [h_kill, map_zero, LinearMap.zero_apply]

/-- Let `Ξ` be a form on `V_j`, for the pair `W_j, V_j` at the twist `ϑ` (`descentPair ϑ j`). If `Ξ`
lies in the image of the idempotent `D.e₀` and is orthogonal to the theta lifts `D.goodLift ϑ j y`
of all good forms `y` on `W_j` (principal level, in the image of `D.e₀`), then its descent
`normalizedDescent Ξ`, the function on `U(W_j)` that pairs `Ξ` with the theta kernel, vanishes. -/
lemma normalizedDescent_eq_zero_of_mem_orthogonal {Ξ : (D.descentPair ϑ j).FormV}
    (hΞ : Ξ ∈ (groupAlgAction (D.descentPair ϑ j) D.e₀).range)
    (h_orth : Ξ ∈ (D.goodLift ϑ j).rangeᗮ) : (D.descentPair ϑ j).normalizedDescent Ξ = 0 := by
  -- For every `y`, `⟨Θ y, Ξ⟩ = ⟨Θ y, e₀ Ξ⟩ = ⟨e₀ Θ y, Ξ⟩`, and `e₀ Θ y` is the lift of a good form.
  have h_fix : (D.descentPair ϑ j).groupAlgAction D.e₀ Ξ = Ξ :=
    (D.isCentralProj_e₀.1.map _).mem_range_iff.1 hΞ
  refine (D.normalizedDescent_eq_zero_iff ϑ Ξ).2 fun y ↦ ?_
  have h_lift : (D.descentPair ϑ j).groupAlgAction D.e₀ (D.singleLift ϑ j y) ∈
    (D.goodLift ϑ j).range :=
    ⟨⟨_, _, rfl⟩, singleLift_asAlgebraHom ..⟩
  calc _ = inner ℂ (D.singleLift ϑ j y) ((D.descentPair ϑ j).groupAlgAction D.e₀ Ξ) := by rw [h_fix]
    _ = inner ℂ ((D.descentPair ϑ j).groupAlgAction D.e₀ (D.singleLift ϑ j y)) Ξ :=
        (innerAt_groupAlgAction _ D.isCentralProj_e₀ ..).symm
    _ = 0 := h_orth _ h_lift

/-- For the pair `descentPair ϑ j`, its `tamePart` is not `1` at any place `twistPlace i`, that is,
at any place of its set `Q`. -/
lemma tamePart_twistPlace_ne_one (i : (D.descentPair ϑ j).TwistIndex) :
    (D.descentPair ϑ j).tamePart ((D.descentPair ϑ j).twistPlace i) ≠ 1 :=
  (liftTamePart_eq_of_mem_Q ..).trans_ne (ϑ.tamePart_ne_one _ i.2)

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.sum Finset.prod in
/-- Periods of false lifts on `V_j` vanish, for the pair `W_j, V_j` at the twist `ϑ`. Let `Ξ` be a
false lift (`falseLiftsAt`): it lies in the image of `D.e₀`, is killed by the Hecke polynomial
operator for a split place `w` off the level at the value `liftHeckeRoot w`, and is orthogonal to
the lifts of good forms. Let `ε` split `V_j` as `V″ ⊕ V°`, with bases `N` and `l` and
`r + 2 rk V″ + 3 < t`. Let `h₁` be a finite point of `U(V″)` and `x` one of `U(V_j)` supported on
the places of the level and their conjugates. Let `κ` be a diagram given by column counts at the
infinite places, and `k` a function on the finite points of `U(V°)` with values vectors of weight
`κ`, whose coordinates, moved by the real points (`GInf`), are multiples of conjugate theta kernels
`pairTheta` of `W_j, V°` with Schwartz data `φ` fixed by the projection `Space.projOn` for the
places off the level. Let the conjugate-linear map `C` carry these vectors to the space of values of
`Ξ`, equivariantly for the representations `conjWeylRep` of `U(V°)_∞`. Then the pairing of `C (k h)`
with `Ξ ((h₁, h) x)` is left invariant under the rational points, and its class sum is zero at every
level `K` that fixes it. This is `stdClassSum_gramForm_eq_zero` for `descentPair ϑ j`. -/
theorem stdClassSum_gramForm_eq_zero_of_mem_falseLiftsAt {N l : Type} [Fintype N] [DecidableEq N]
    [Fintype l] [DecidableEq l] {w : FinPlace D.E} {hw : star w ≠ w}
    {hS : w ∉ (D.descentPair ϑ j).places.conjClosure} {Ξ : (D.descentPair ϑ j).FormV}
    (hΞ : Ξ ∈ (D.descentPair ϑ j).falseLiftsAt hw hS D.e₀ (D.goodLift ϑ j).rangeᗮ)
    (ε : N ⊕ l ≃ D.RowIndex ⊕ Fin D.t) (h_rank : D.r + 2 * card N + 3 < D.t)
    {κ : NumberField.InfinitePlace D.E → ℕ → ℕ}
    (C : (WeylIndex l κ → ℂ) →ₗ⋆[ℂ] WeylIndex (D.RowIndex ⊕ Fin D.t) (D.descentPair ϑ j).columnCount
      → ℂ)
    (hC : ∀ (g : GInf D.E (1 : D.RowIndex ⊕ Fin D.t → ℤˣ)) (y : GInf D.E (1 : l → ℤˣ))
      (ζ : WeylIndex l κ → ℂ),
      (∀ τ : NumberField.InfinitePlace D.E,
          (g τ : GL (D.RowIndex ⊕ Fin D.t) ℂ) = reindexGL ε (blockGL (1, y τ))) →
        conjWeylRep (D.descentPair ϑ j).columnCount (D.descentPair ϑ j).detExp g (C ζ) = C
          (conjWeylRep κ 0 y ζ))
    (k : Gf D.E l → WeylIndex l κ → ℂ)
    (h_kernels : ∀ i : WeylIndex l κ, ∃ (c : ℂ) (g : G D.E (D.signsW j)) (b : AutChar D.E)
      (φ : 𝒮 ((D.descentPair ϑ j).W.hom (stdSpace D.E l))),
      Space.projOn ((D.descentPair ϑ j).W.hom (stdSpace D.E l))
          (D.descentPair ϑ j).places.conjClosureᶜ φ = φ ∧
        ∀ (u : GInf D.E (1 : l → ℤˣ)) (h : Gf D.E l), conjWeylRep κ 0 u⁻¹ (k h) i =
          c * conj (pairTheta (D.descentPair ϑ j).W (stdSpace D.E l) (D.descentPair ϑ j).charW b φ
            (g, u, h)))
    (h₁ : Gf D.E N) {x : Gf D.E (D.RowIndex ⊕ Fin D.t)}
    (hx : x ∈ Gf.supportedOn (D.RowIndex ⊕ Fin D.t) (D.descentPair ϑ j).places) :
    let f (h : Gf D.E l) : ℂ := gramForm (C (k h)) (Ξ (U.block ε (h₁, h) * x))
    (∀ δ ∈ (stdSpace D.E l).Γ, ∀ h : Gf D.E l, f (δ.2 * h) = f h) ∧
      ∀ (K : Subgroup (Gf D.E l)) [IsLevel K], K ≤ rightStabilizer f → stdClassSum K f = 0 := by
  obtain ⟨⟨hΞ_range, hΞ_hecke⟩, hΞ_orth⟩ := hΞ
  have h_gap : 2 * card D.RowIndex + 2 * card N + 3 < card (D.RowIndex ⊕ Fin D.t) := by
    rw [D.card_rowIndex_sum_fin, D.card_rowIndex]
    linarith [D.t_eq_five_mul_r]
  exact stdClassSum_gramForm_eq_zero (D.fitsParams_descentPair ϑ j) (tamePart_twistPlace_ne_one j ϑ)
    (hyperplaneSum_apply_eq_zero j ϑ hΞ_range)
    (normalizedDescent_eq_zero_of_mem_orthogonal j ϑ hΞ_range hΞ_orth) hΞ_hecke
    h_gap ε C hC k h_kernels h₁ hx

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.univ in
/-- Slices of false lifts vanish. Let `w` be a split place (`star w ≠ w`) off the level of the pair
`descentPair ϑ j`, and let `Ξ` be a false lift at `w`: a form on `V_j = V″ ⊕ V°` in the image of the
projection `e₀` that is killed by the Hecke polynomial operator at `w` and is orthogonal to the
lifts of good forms. Let `h` be a finite point of `U(V″)`, `y` any vector of weight `μ⁺`
(`colsPlus`) on `V″` and `g` a point of `U(W_j)`. Then the sum, over the classes of `U(V°)` with
representative `h° = c.out`, of the pairing of `Ξ ((h, h°) 𝗀)` with the product (`cartanProduct`) of
`y` and `θ° (g, h°)` is `0`. Here `θ°`, the conjugate of `kernelVector`, is the theta kernel of
`W_j, V°` of weight `μ⁻` (`colsMinus`), any datum `Ψ` modulo `ϖ²` (`ϖ = D.piM`) and any character
`b`, and `𝗀 = L.point` is the matrix of a lattice `L` between `ϖ 𝒪ⁿ` and `𝒪ⁿ`. -/
lemma sum_slice_eq_zero_of_mem_falseLiftsAt {w : FinPlace D.E} {hw : star w ≠ w}
    {hS : w ∉ (D.descentPair ϑ j).places.conjClosure} {Ξ : (D.descentPair ϑ j).FormV}
    (hΞ : Ξ ∈ (D.descentPair ϑ j).falseLiftsAt hw hS D.e₀ (D.goodLift ϑ j).rangeᗮ)
    (L : DividedLattice (D.descentPair ϑ j)) (h : Gf D.E (FirstFactorIndex j))
    (y : WeylIndex (FirstFactorIndex j) (D.descentPair ϑ j).colsPlus → ℂ) (b : AutChar D.E)
    (Ψ : Matrix D.SecondFactorIndex D.RowIndex (D.descentPair ϑ j).chosenModulusSq.ResidueRing → ℂ)
    (g : G D.E (D.signsW j)) :
    ∑ c : D.SecondFactorClasses, gramForm
      (cartanProduct (splittingV j ϑ).ε 1 y (star (kernelVector (D.descentPair ϑ j) b
        (D.descentPair ϑ j).chosenModulusSq Ψ (D.descentPair ϑ j).colsMinus g c.out)))
      (Ξ (U.block (splittingV j ϑ).ε (h, c.out) * L.point)) = 0 := by
  classical
  obtain ⟨⟨hΞ_range, hΞ_ker⟩, hΞ_orth⟩ := hΞ
  have h_gap : 2 * card D.RowIndex + 2 * card (FirstFactorIndex j) + 3 < card
    (D.RowIndex ⊕ Fin D.t) := by
    rw [D.card_rowIndex_sum_fin, D.card_rowIndex, card_firstFactorIndex]
    grind [D.hundred_mul_m_add_nine_lt_k, D.r_add_one, D.t_eq_five_mul_r]
  -- Periods of false lifts vanish, here for the point `(h, h°) 𝗀`, the map `ζ ↦ y · ζ` and the
  -- level `J (ϖ²)`, which fixes the pairing, as its conjugate by `𝗀` fixes `Ξ`.
  have h_period : stdClassSum (principalLevel D.SecondFactorIndex (D.piM ^ 2))
      (fun h' : Gf D.E D.SecondFactorIndex ↦ inner ℂ ((splittingV j ϑ).productForm L (h, h') y
        (star (kernelVector (D.descentPair ϑ j) b (D.descentPair ϑ j).chosenModulusSq Ψ
          (D.descentPair ϑ j).colsMinus g h'))) Ξ) = 0 :=
    (splittingV j ϑ).stdClassSum_inner_productForm_eq_zero (D.fitsParams_descentPair ϑ j)
      (tamePart_twistPlace_ne_one j ϑ) (hyperplaneSum_apply_eq_zero j ϑ hΞ_range)
      (normalizedDescent_eq_zero_of_mem_orthogonal j ϑ hΞ_range hΞ_orth) hΞ_ker h_gap
      D.ideal_untwistedModulus_eq_span L h y b Ψ g
  -- The level `J (ϖ²)` on `V°` is sufficiently small, so the class sum is a plain sum.
  have h_small (h' : Gf D.E D.SecondFactorIndex) :
      classAut stdRatPoints (principalLevel D.SecondFactorIndex (D.piM ^ 2)) h' = ⊥ :=
    D.classAut_eq_bot_of_le_chosenLevel (D.principalLevel_le_chosenLevel ⟨_, sq _⟩)
      (by grind [card_secondFactorIndex_le D, D.six_mul_r_le_n, D.t_eq_five_mul_r]) h'
  -- The inner product with a form supported on one class is the pairing with the value there.
  simpa [↓h_small, classSum, ↓ finsum_eq_sum_of_fintype, DividedSplitting.productForm,
    inner_classForm] using! h_period

set_option backward.isDefEq.respectTransparency false in
/-- Let `Ξ` be a false lift on `V_j` at a split place `w` off the level of `descentPair ϑ j`: a form
in the image of `D.e₀` that is killed by the Hecke polynomial operator at `w` and is orthogonal to
the lifts of good forms. The adjoint of the gluing map `glue j ϑ` takes `Ξ` to a tuple of forms on
`V°`, one for each choice `i`, given by values at the classes `c`. Each of them has pairing `0` with
the theta kernel `θ° (g, ·)` of `W_j, V°` at every `g` in `U(W_j)`. -/
lemma thetaKernelPairing_adjoint_glue_eq_zero {w : FinPlace D.E} {hw : star w ≠ w}
    {hS : w ∉ (D.descentPair ϑ j).places.conjClosure} {Ξ : (D.descentPair ϑ j).FormV}
    (hΞ : Ξ ∈ (D.descentPair ϑ j).falseLiftsAt hw hS D.e₀ (D.goodLift ϑ j).rangeᗮ)
    (i : ChoiceIndex j) (g : G D.E (D.signsW j)) :
    thetaKernelPairing j (fun c : D.SecondFactorClasses ↦ (glue j ϑ).adjoint Ξ (i, c)) g = 0 := by
  classical
  -- The conjugate of the value is the product of the period with the tuple `η` of the values of
  -- `θ° (g, ·)` in the copy `i`, and the period is a sum of slices of `Ξ`.
  let θ (c : D.SecondFactorClasses) : SecondFactorFormValues j :=
    star ∘ kernelVector (untwistedDescentPair j) (upsilonU1 ^ (D.m / 2 - j : ℤ))
      (D.untwistedModulus 2) (Pi.single (inclMatrix _ inl) 1) (untwistedDescentPair j).colsMinus g
      c.out
  let η : FormTuples j := .toLp 2 fun b ↦ if b.1 = i then θ b.2 else 0
  have h_slice (i' : ChoiceIndex j) (h : Gf D.E (FirstFactorIndex j)) :
      ∑ c : D.SecondFactorClasses,
        gramForm (cartanProduct (splittingV j ϑ).ε 1 (firstFactor j ϑ i' h) (η (i', c)))
          (Ξ (U.block (splittingV j ϑ).ε (h, c.out) * (glueLattice j ϑ i').point)) = 0 := by
    by_cases hi : i' = i
    · simp only [η, ite_eq_left hi]
      exact sum_slice_eq_zero_of_mem_falseLiftsAt j ϑ hΞ (glueLattice j ϑ i') h _ _ _ g
    · simp [η, hi]
  refine star_eq_zero.1 ?_
  calc star (thetaKernelPairing j (fun c ↦ (glue j ϑ).adjoint Ξ (i, c)) g)
      = ∑ c, inner ℂ (θ c) ((glue j ϑ).adjoint Ξ (i, c)) := by
        -- The kernel is linear in its polynomial; expand both sides in the basis of weight `μ⁻`.
        simp [θ, thetaKernelPairing, kernelVector, inner, letterPoly, toPoly,
          linearCombination_apply, ← modKernelBilin_apply, Matrix.mulVec, dotProduct]
        rfl
    _ = ∑ i', ∑ c, inner ℂ (η (i', c)) ((glue j ϑ).adjoint Ξ (i', c)) := by
        rw [Fintype.sum_eq_single i (by simp +contextual [η])]
        simp [η]
    _ = inner ℂ η ((glue j ϑ).adjoint Ξ) := by
        rw [PiLp.inner_apply, sum_prod_type (α₂ := D.SecondFactorClasses)]
    _ = 0 := by
        rw [inner_adjoint_glue]
        refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun i' _ ↦ ?_)
        simp only [classSum, finsum_eq_sum_of_fintype]
        rw [sum_comm]
        refine Finset.sum_eq_zero fun h _ ↦ ?_
        rw [← smul_sum, h_slice, smul_zero]

/-! ### The map `Θ°`, the seesaw identity and the false lifts -/

/-- The number `c°_i = M ^ l₁ c_𝗀 #J̄¹ c″` of the choice `i`, with `c_𝗀` the scalar of the lattice,
`J̄¹` the group `congruenceGroup` and `c″ = firstFactorScale j`. It does not depend on the twist. -/
def glueFactor (i : ChoiceIndex j) : ℂ :=
  D.M ^ (splittingV j 1).denominatorExponent * (glueLattice j 1 i).weilScalar *
    Nat.card (splittingV j 1).congruenceGroup * firstFactorScale j

lemma glueFactor_ne_zero (i : ChoiceIndex j) : glueFactor j i ≠ 0 := by
  simp [glueFactor, DividedLattice.weilScalar, NeZero.ne, firstFactorScale_ne_zero]

/-- Let `y` be a good form on `W_j` and `ζ` a tuple of forms on `V°`. Take the inner product of `ζ`
with the adjoint of the gluing map `glue j ϑ` at the theta lift of `y`, and multiply it by
`twistFactor j ϑ`, the scalar that carries the dependence of the series `firstFactorPairing` on the
twist `ϑ`. The result is the sum over the choices `i` of the number `glueFactor j i` times the
integral over `U(W_j)` modulo rational points of `y`, the function `choiceFn j i` and the pairing of
the copy `i` of `ζ` with the theta kernel of `W_j, V°`. -/
lemma twistFactor_mul_inner_adjoint_glue (y : D.goodForms (D.spaceW j)) (ζ : FormTuples j) :
    twistFactor j ϑ * inner ℂ ζ ((glue j ϑ).adjoint (D.goodLift ϑ j y)) =
      ∑ i : ChoiceIndex j, glueFactor j i *
        ∫ g : G D.E (D.signsW j), (y : G D.E (D.signsW j) → ℂ) g * choiceFn j i g *
          thetaKernelPairing j (fun c : D.SecondFactorClasses ↦ ζ (i, c)) g
            ∂(D.spaceW j).quotMeasure := by
  rw [inner_adjoint_glue_goodLift_eq_sum_integral, mul_sum]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [mul_left_comm, glueFactor, mul_assoc _ (firstFactorScale j),
    ← integral_const_mul (firstFactorScale j),
    ← integral_const_mul (twistFactor j ϑ)]
  refine congrArg _ (integral_congr_ae (.of_forall fun g ↦ ?_))
  have h_series : twistFactor j ϑ * firstFactorPairing j ϑ i g = firstFactorScale j * choiceFn j i
    g :=
    twistFactor_mul_firstFactorPairing j ϑ i g
  linear_combination
    (y : G D.E (D.signsW j) → ℂ) g * thetaKernelPairing j (fun c ↦ ζ (i, c)) g * h_series

/-- The map `Θ°` from the good forms on `W_j` to tuples of forms on `V°` whose copy `i` is
`c°_i ∫ y (g) 𝖥_i (g) θ° (g, ·) dg` (`inner_periodLift`). It is defined as `c′_1 glue_1* Θ_{j,1}`,
the left side of the seesaw identity at the trivial twist. -/
def periodLift : D.goodForms (D.spaceW j) →ₗ[ℂ] FormTuples j :=
  twistFactor j 1 • (glue j 1).adjoint ∘ₗ D.goodLift (1 : D.Twist) j

/-- The product of `Θ° y` with a tuple `ζ` is the sum over the choices `i` of `c°_i` times the
integral of `y 𝖥_i` against the pairing of `θ° (g, ·)` with the copy `i` of `ζ`. -/
lemma inner_periodLift (y : D.goodForms (D.spaceW j)) (ζ : FormTuples j) :
    inner ℂ ζ (periodLift j y) = ∑ i : ChoiceIndex j, glueFactor j i *
      ∫ g : G D.E (D.signsW j), (y : G D.E (D.signsW j) → ℂ) g * choiceFn j i g *
        thetaKernelPairing j (fun c : D.SecondFactorClasses ↦ ζ (i, c)) g
          ∂(D.spaceW j).quotMeasure := by
  simpa [periodLift] using twistFactor_mul_inner_adjoint_glue j 1 y ζ

/-- The seesaw identity `c′_ϑ glue_ϑ* Θ_{j,ϑ} = Θ°`: the number `twistFactor j ϑ` times the
composite of the lift `goodLift` with the adjoint of the gluing map `glue` is the map
`periodLift`, which does not depend on the twist. -/
theorem twistFactor_smul_adjoint_glue_comp :
    twistFactor j ϑ • (glue j ϑ).adjoint ∘ₗ D.goodLift ϑ j = periodLift j := by
  refine ext fun y ↦ ext_inner_left ℂ fun ζ ↦ ?_
  simpa [inner_periodLift, inner_smul_right] using twistFactor_mul_inner_adjoint_glue j ϑ y ζ

/-- For a good form `y` on `W_j`, the glued form `glue j ϑ (periodLift j y)` is orthogonal to the
false lifts at every split place off the level: the forms in the image of `e₀` that are killed by
the Hecke polynomial operator and are orthogonal to the lifts. -/
theorem isOrthogonalToFalseLifts_glue_periodLift (y : D.goodForms (D.spaceW j)) :
    IsOrthogonalToFalseLifts (D.descentPair ϑ j) D.e₀ (D.goodLift ϑ j).rangeᗮ
      (glue j ϑ (periodLift j y)) := by
  intro w hw hS φ hφ
  -- `⟨φ, glue Θ° y⟩ = ⟨glue* φ, Θ° y⟩` is an integral against the products of the period of `φ`
  -- with the kernels `θ° (g, ·)`, and these vanish.
  rw [← adjoint_inner_left, inner_periodLift]
  simp [thetaKernelPairing_adjoint_glue_eq_zero j ϑ hφ]

/-! ### Injectivity of `Θ°` -/

/-- The map `periodLift j` from good forms on `W_j` to tuples of forms on `V°` is injective. -/
theorem periodLift_injective : Function.Injective (periodLift j) := by
  classical
  refine (injective_iff_map_eq_zero _).2 fun y hy ↦
    eq_zero_of_integral_choiceFn_thetaKernelPairing y fun i ζ ↦ ?_
  -- Test `Θ° y = 0` against the tuple that is `ζ` in the copy `i` and zero elsewhere.
  let η : FormTuples j := .toLp 2 fun b : ChoiceIndex j × D.SecondFactorClasses ↦
    if b.1 = i then ζ b.2 else 0
  have h_test := inner_periodLift j y η
  -- The copies other than `i` contribute nothing.
  rw [hy, inner_zero_right, Fintype.sum_eq_single i fun i' hi' ↦ by
    simp [η, hi', thetaKernelPairing, ← modKernelBilin_apply]] at h_test
  -- What is left is `c°_i` times the integral to be shown `0`.
  simpa [η, glueFactor_ne_zero] using h_test.symm

/-- The number `twistFactor j ϑ` is not `0`, since `Θ° = periodLift j` is injective and there is a
nonzero good form. -/
theorem twistFactor_ne_zero : twistFactor j ϑ ≠ 0 := by
  intro h_zero
  have h_lift : periodLift j = 0 := by simp [← twistFactor_smul_adjoint_glue_comp j ϑ, h_zero]
  exact D.finrank_targetForms_ne_zero <| (D.targetDim_eq_finrank_goodForms_spaceW j).trans <|
    finrank_zero_iff_forall_zero.2 fun y ↦ periodLift_injective j (by simp [h_lift])

end New.Rows

end
