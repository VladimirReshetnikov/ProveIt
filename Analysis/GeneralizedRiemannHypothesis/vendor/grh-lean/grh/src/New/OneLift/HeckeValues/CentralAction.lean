import New.OneLift.ComparisonOperator.GluedLattices
import New.OneLift.HeckeValues.CharacterLiftNorm
import New.UpperBound.Size.ShortColumns

/-!
# Central action on lifts from U(1) and a rank-one denominator bound

For a lift from the definite `U(1)` to the definite `U(n)` (data `New.LValueData`, kernel
`New.LValueData.kernelForm`, lift `New.LValueData.trivialLift` of the trivial character), the finite
adelic `U(1)` acts on forms on `U(n)` through the centre. This file defines this action,
`New.LValueData.centralRep`, and its twist `New.LValueData.normalizedCentralOp`, which fixes the
lift. The central translations commute with Hecke polynomials at split places off the level. The
file uses this action to bound the denominator of the product of the projections of two test forms
to the line of the lift, given a bound `New.Selmer.DenominatorLe` on that line.

## Main definitions and results

* `New.Selmer.DenominatorLe.norm_inner_starProjection_le`: a bound `New.Selmer.DenominatorLe` on the
  line of the lift bounds the denominator of the product of the projections of two test forms to
  that line, at the cost of the class number of `U(1)` at the chosen level.
* `New.LValueData.normalizedCentralOp_trivialLift`: the twisted central translations fix the lift
  of the constant function.

## Relation to the literature

See `New.OneLift.HeckeValues.TwistedValueHeights` for related work.
-/

noncomputable section

namespace New

open Matrix Submodule Real Seesaw LValueData

variable {P : Parameters} {D : Data P} {n : Type} [Fintype n] [DecidableEq n]
variable (Y : LValueData D.E n)

/-- The finite points of `U(1)` act on the forms on `U(n)` for the lift data `Y` through translation
by scalar matrices. -/
def LValueData.centralRep : Representation ℂ (Gf D.E Unit) Y.descentPair.FormV :=
  algFormCentralRep.comp (U.det (by simp))

/-- Translation by the scalar `z`, multiplied by the value at `det z` of `Y.descentPair.charV`, the
character by which the kernel of the lift twists the action of `U(1)`. -/
def LValueData.normalizedCentralOp (z : Gf D.E Unit) : Module.End ℂ Y.descentPair.FormV :=
  (Y.descentPair.charV.val (detFin 1 z) : ℂ) • Y.centralRep z

/-- Under `Y.centralRep`, an element `z` of `Gf D.E Unit` acts on the underlying algebraic forms by
right translation (`algFormRep`) by the scalar matrix `scalarFin n` of `det z`. -/
lemma LValueData.coe_centralRep_apply (z : Gf D.E Unit) (y : Y.descentPair.FormV) :
    (Y.centralRep z y).val =
      algFormRep Y.descentPair.columnCount Y.descentPair.detExp (scalarFin n (U.det (by simp) z))
        y.val :=
  rfl

/-- Translation by a scalar preserves the inner product of forms on `U(n)`. -/
lemma LValueData.inner_centralRep_centralRep (z : Gf D.E Unit) (x y : Y.descentPair.FormV) :
    inner ℂ (Y.centralRep z x) (Y.centralRep z y) = inner ℂ x y := by
  change (Y.centralRep z x).innerAt 1 (Y.centralRep z y) = x.innerAt 1 y
  -- The product is a multiple of the translation-invariant pairing `smoothPairing`.
  unfold LevelPlaces.LevelForm.innerAt
  exact congrArg (_ * ·) (smoothPairing_formTranslation _ _ x.toSmoothForm y.toSmoothForm)

/-- For data `Y` of a lift from `U(1)` to `U(n)` and `z` in `U(1)(𝔸_f)`, the adjoint of the
normalized translation `T z = Y.normalizedCentralOp z` is `T z⁻¹`: `⟪x, T z y⟫ = ⟪T z⁻¹ x, y⟫`. -/
lemma LValueData.inner_normalizedCentralOp (z : Gf D.E Unit) (x y : Y.descentPair.FormV) :
    inner ℂ x (Y.normalizedCentralOp z y) = inner ℂ (Y.normalizedCentralOp z⁻¹ x) y := by
  have h_adj : inner ℂ x (Y.centralRep z y) = inner ℂ (Y.centralRep z⁻¹ x) y := by
    rw [← Y.inner_centralRep_centralRep z (Y.centralRep z⁻¹ x), Representation.self_inv_apply]
  have h_conj :
      starRingEnd ℂ (Y.descentPair.charV.val (detFin 1 z⁻¹)) = Y.descentPair.charV.val
        (detFin 1 z) := by
    simp [← Circle.coe_inv_eq_conj, ← MonoidHom.inr_apply]
  simp only [normalizedCentralOp, LinearMap.smul_apply, inner_smul_left, inner_smul_right, h_adj,
    h_conj]

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.sum in
/-- For lift data `Y` and `z`, `g` in `Gf D.E Unit` (the finite adelic `U(1)`), the normalized
translation `normalizedCentralOp` at `z⁻¹` carries the theta kernel at `g`, as a form on `U(n)`
(`kernelForm`), to the kernel at `g * z`. -/
lemma LValueData.normalizedCentralOp_kernelForm (z g : Gf D.E Unit) :
    Y.normalizedCentralOp z⁻¹ (Y.kernelForm g) = Y.kernelForm (g * z) := by
  -- `z⁻¹` is the scalar `ν = det z⁻¹`, and the pair of scalars `(ν, ν)` acts in the Weil
  -- representation on `blockDatum` by a number. So translating the kernel by `ν` on `U(n)` amounts
  -- to translating it by `z` on `U(1)`, up to the scalar in `Y.normalizedCentralOp`.
  let ν : unitary (𝔸f D.E) := U.det (by simp) z⁻¹
  have hν : scalarFin Unit ν = z⁻¹ := by ext; simp [ν, Gf.atPlace, scalarFin, U.det]
  let χ : ℂ := Y.descentPair.charV.val (detFin 1 z⁻¹)
  have h_datum :
      pairWeilFinite (stdSpace D.E Unit) (stdSpace D.E n) Y.descentPair.charW Y.descentPair.charV
        (z⁻¹, scalarFin n ν) Y.descentPair.blockDatum = χ⁻¹ • Y.descentPair.blockDatum := by
    simp [← hν, pairWeilFinite_scalarFin, χ, Prod.mk_one_one]
  refine Subtype.ext ?_
  ext k : 2
  change χ • Y.kernelValue 1 Y.descentPair.blockDatum g (k * scalarFin n ν) =
    Y.kernelValue 1 Y.descentPair.blockDatum (g * z) k
  simpa [χ, kernelValue, ← mul_apply_eq_comp, ← map_mul, eq_inv_smul_iff₀, smul_mulVec] using
    congrArg (fun f ↦ Y.kernelValue 1 f.val (g * z) k) h_datum

/-- The normalized central translations fix the lift of the constant function. -/
lemma LValueData.normalizedCentralOp_trivialLift (z : Gf D.E Unit) :
    Y.normalizedCentralOp z Y.trivialLift = Y.trivialLift :=
  calc Y.normalizedCentralOp z Y.trivialLift
      = stdClassSum Y.chosenLevel fun g ↦ Y.normalizedCentralOp z (Y.kernelForm g) :=
        map_classSum _ _
    _ = stdClassSum Y.chosenLevel fun g ↦ Y.kernelForm (g * z⁻¹) := by
        simp [← normalizedCentralOp_kernelForm]
    _ = Y.trivialLift := (Y.trivialLift_eq_stdClassSum_translate z⁻¹).symm

/-- On algebraic forms of the weight of `Y`, translation by a scalar matrix commutes with every
translation. -/
lemma LValueData.commute_algFormRep_scalarFin (ν : unitary (𝔸f D.E)) (g : Gf D.E n) :
    Commute (algFormRep Y.descentPair.columnCount Y.descentPair.detExp (scalarFin n ν))
      (algFormRep Y.descentPair.columnCount Y.descentPair.detExp g) :=
  (commute_scalarFin g).map _

/-- On an algebraic form `φ` of the weight of `Y`, translation (`algFormRep`) by the scalar matrix
`scalarFin n ν` commutes with translation by `g`: applying the two in either order gives the same
form. -/
lemma LValueData.algFormRep_scalarFin_apply_comm (ν : unitary (𝔸f D.E)) (g : Gf D.E n)
    (φ : AlgForm (E := D.E) n Y.descentPair.columnCount Y.descentPair.detExp) :
    algFormRep Y.descentPair.columnCount Y.descentPair.detExp (scalarFin n ν)
        (algFormRep Y.descentPair.columnCount Y.descentPair.detExp g φ) =
      algFormRep Y.descentPair.columnCount Y.descentPair.detExp g
        (algFormRep Y.descentPair.columnCount Y.descentPair.detExp (scalarFin n ν) φ) := by
  rw [← Module.End.mul_apply, (Y.commute_algFormRep_scalarFin ν g).eq, Module.End.mul_apply]

/-- Central translations preserve the image of an element `e` of the group algebra of the residue
units at the chosen places. -/
lemma LValueData.centralRep_mem_range_groupAlgAction (z : Gf D.E Unit)
    {e : MonoidAlgebra ℂ (Y.descentPair.ChosenGL Unit)} {y : Y.descentPair.FormV}
    (hy : y ∈ (Y.descentPair.groupAlgAction e).range) :
    Y.centralRep z y ∈ (Y.descentPair.groupAlgAction e).range := by
  refine DescentPair.range_groupAlgAction_mem_invtSubmodule _
    (fun g ↦ LinearMap.ext fun x ↦ Subtype.ext ?_) hy
  -- The action `Y.descentPair.formAction g` is a right translation times a number.
  rw [Module.End.mul_apply, Module.End.mul_apply, coe_centralRep_apply, DescentPair.coe_formAction,
    DescentPair.coe_formAction, coe_centralRep_apply, map_smul,
    algFormRep_scalarFin_apply_comm]

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.univ in
/-- Let `Y` be data for a theta lift from `U(1)` to the definite `U(n)` over the CM field `D.E`,
with space of algebraic forms `Y.descentPair.FormV` on `U(n)`. Translation `Y.centralRep z` by a
scalar `z ∈ U(1)(𝔸_f)` commutes with the operator
`heckePolyOnForms = ∑ i, (-X) ^ i q ^ (i (i - 1) / 2) T_{w,i}`, for any number `X` and any split
place `w` of norm `q` such that `w` and its conjugate are off the level. -/
lemma LValueData.centralRep_heckePolyOnForms (z : Gf D.E Unit) {w : FinPlace D.E}
    (hw : star w ≠ w) (hS : w ∉ Y.descentPair.places.conjClosure) (X : ℂ)
      (y : Y.descentPair.FormV) :
    Y.centralRep z (Y.descentPair.heckePolyOnForms hw hS X y) =
      Y.descentPair.heckePolyOnForms hw hS X (Y.centralRep z y) := by
  -- `Y.centralRep z` is translation by a scalar matrix, which commutes with every translation.
  have h_coe (x : Y.descentPair.FormV) : (Y.descentPair.heckePolyOnForms hw hS X x).val =
      heckePolyOp (algFormRep Y.descentPair.columnCount Y.descentPair.detExp) hw X x.val := rfl
  refine Subtype.ext ?_
  rw [coe_centralRep_apply, h_coe, h_coe, coe_centralRep_apply]
  refine map_heckePolyOp (σ := RingHom.id ℂ) _ X fun g _ ↦ ?_
  exact Y.algFormRep_scalarFin_apply_comm _ g y.val

/-- Let `Y` be data for a theta lift from `U(1)` to the definite `U(n)` over the CM field `D.E`,
with space of algebraic forms `Y.descentPair.FormV` on `U(n)`, and `T z = Y.normalizedCentralOp z`
the translation by the scalar `z ∈ U(1)(𝔸_f) = Gf D.E Unit` times the value of the character
`Y.descentPair.charV` at `z`. Let `j : ℂ → ℂ_ℓ` be an embedding for a prime `ℓ`. If `z` is integral
at the places above `ℓ`, then `T z⁻¹` preserves the forms whose values are all integral at `j`
(`integralForms j`). -/
lemma LValueData.normalizedCentralOp_inv_mem_integralForms {ℓ : ℕ} [Fact ℓ.Prime] (j : PadicPlace ℓ)
    {z : Gf D.E Unit} (hz : z ∈ integralAbove Unit ℓ) {Ξ : Y.descentPair.FormV}
    (hΞ : Ξ ∈ LevelPlaces.LevelForm.integralForms j) :
    Y.normalizedCentralOp z⁻¹ Ξ ∈ LevelPlaces.LevelForm.integralForms j := by
  intro g
  let k : Gf D.E n := scalarFin n (U.det (by simp) z⁻¹)
  have hk : k ∈ integralAbove n ℓ := by
    -- The entries of `k` and `k⁻¹` are `0` or the entry of `z⁻¹`, resp. `z`.
    simp only [mem_localLevel, mem_intGL, ← map_inv, k] at hz ⊢
    simp_all [scalarFin, U.det, diagonal, apply_ite, Gf.atPlace, -map_inv]
  have h_norm : ‖ιₚ (Y.descentPair.charV.1 (detFin 1 z⁻¹) : ℂ)‖ = 1 :=
    Y.charV_hasWeight.norm_apply_detFin_eq_one (hg := inv_mem hz)
  have h_value : Y.normalizedCentralOp z⁻¹ Ξ g = (Y.descentPair.charV.1 (detFin 1 z⁻¹) : ℂ) • Ξ
    (g * k) := rfl
  calc weylGauge Y.descentPair.columnCount Y.descentPair.detExp g (Y.normalizedCentralOp z⁻¹ Ξ g)
      = weylGauge Y.descentPair.columnCount Y.descentPair.detExp g (Ξ (g * k)) := by
        rw [h_value, weylGauge_smul, h_norm, one_mul]
    _ = weylGauge Y.descentPair.columnCount Y.descentPair.detExp (g * k) (Ξ (g * k)) :=
        (weylGauge_mul_of_mem_integralAbove (hk := hk) ..).symm
    _ ≤ 1 := hΞ (g * k)

/-- Let `Y` be data for a theta lift from `U(1)` to the definite `U(n)` over the CM field `D.E`,
with space of algebraic forms `Y.descentPair.FormV` on `U(n)`, lift `Y.trivialLift`, and
`T z = Y.normalizedCentralOp z` the translation by the scalar `z ∈ U(1)(𝔸_f) = Gf D.E Unit` times
the value of the character `Y.descentPair.charV` at `z`. Let all stabilisers `classAut` of `U(1)` at
the chosen level be trivial, and let `s c` represent the class `c` modulo the rational points `Γf`
and that level. If `y` is orthogonal to `Y.trivialLift`, then the descent
`Y.descentPair.normalizedDescent` from `U(n)` to `U(1)`, the adjoint of the lift, kills
`∑ c, T (s c) y`. -/
lemma LValueData.sum_normalizedCentralOp_mem_ker_normalizedDescent
    (h_aut : ∀ g : Gf D.E Unit, classAut stdRatPoints Y.chosenLevel g = ⊥)
    {s : StdClasses Y.chosenLevel → Gf D.E Unit}
    (hs : ∀ c : StdClasses Y.chosenLevel,
      DoubleCoset.mk (stdSpace D.E Unit).Γf Y.chosenLevel (s c) = c)
    {y : Y.descentPair.FormV} (hy : y ∈ (ℂ ∙ Y.trivialLift)ᗮ) :
    ∑ c : StdClasses Y.chosenLevel, Y.normalizedCentralOp (s c) y ∈
      Y.descentPair.normalizedDescent.ker := by
  -- At `(x, g)` the descent is the inner product with `Y.kernelForm g`, and the translates of this
  -- kernel add up to `Y.trivialLift`.
  funext ⟨x, g⟩
  have h_rep (c : StdClasses Y.chosenLevel) : Y.kernelForm c.out = Y.kernelForm (s c) := by
    simpa [hs] using Y.kernelForm_invariant.elim apply_doubleCoset_out (s c)
  have h_lift : Y.trivialLift = ∑ c : StdClasses Y.chosenLevel, Y.kernelForm (s c) := by
    rw [trivialLift, stdClassSum, classSum, finsum_eq_sum_of_fintype]
    refine Finset.sum_congr rfl fun c _ ↦ ?_
    rw [h_aut, h_rep]
    simp
  have h_translate :
      ∑ c : StdClasses Y.chosenLevel, Y.normalizedCentralOp (s c)⁻¹ (Y.kernelForm g) =
        Y.trivialLift := by
    rw [← Y.normalizedCentralOp_trivialLift g⁻¹, h_lift, map_sum]
    simp only [normalizedCentralOp_kernelForm, mul_comm' g]
  calc Y.descentPair.normalizedDescent (∑ c, Y.normalizedCentralOp (s c) y) (x, g)
      = inner ℂ (∑ c, Y.normalizedCentralOp (s c)⁻¹ (Y.kernelForm g)) y := by
        simp only [normalizedDescent_eq_inner_kernelForm, inner_sum, sum_inner,
          inner_normalizedCentralOp]
    _ = 0 := by
        rw [h_translate]
        exact mem_orthogonal_singleton_iff_inner_right.1 hy

/-- Let `Y` be data for a theta lift from `U(1)` to the definite `U(n)` over the CM field `D.E`,
with space of algebraic forms `Y.descentPair.FormV` on `U(n)`, lift `Y.trivialLift`, and
`T z = Y.normalizedCentralOp z` the translation by the scalar `z ∈ U(1)(𝔸_f) = Gf D.E Unit` times
the value of the character `Y.descentPair.charV` at `z`. Let all stabilisers of `U(1)` at the chosen
level be trivial and let `s c` represent the class `c`. Let `e` be an element of the group algebra
of the residue units at the chosen places. For a subspace `Z` the false lifts at a split place `w`
off the level are the forms in `Z` and in the image of `e` that the Hecke polynomial
`heckePolyOnForms` of `w`, evaluated at `liftHeckeRoot w`, kills. Let `Ξ` be orthogonal to them at
all such `w` for `Z` the kernel of the descent `normalizedDescent` to `U(1)`. Then
`∑ c, T (s c)⁻¹ Ξ` is orthogonal to them for `Z` the orthogonal complement of the line
`ℂ ∙ Y.trivialLift`. -/
lemma LValueData.isOrthogonalToFalseLifts_sum_normalizedCentralOp_inv
    (h_aut : ∀ g : Gf D.E Unit, classAut stdRatPoints Y.chosenLevel g = ⊥)
    {s : StdClasses Y.chosenLevel → Gf D.E Unit}
    (hs : ∀ c : StdClasses Y.chosenLevel,
      DoubleCoset.mk (stdSpace D.E Unit).Γf Y.chosenLevel (s c) = c)
    {e : MonoidAlgebra ℂ (Y.descentPair.ChosenGL Unit)} {Ξ : Y.descentPair.FormV}
    (hΞ : Y.descentPair.IsOrthogonalToFalseLifts e Y.descentPair.normalizedDescent.ker Ξ) :
    Y.descentPair.IsOrthogonalToFalseLifts e (ℂ ∙ Y.trivialLift)ᗮ
      (∑ c : StdClasses Y.chosenLevel, Y.normalizedCentralOp (s c)⁻¹ Ξ) := by
  rintro w hw hS y ⟨⟨hy_range, hy_hecke⟩, hy_orth⟩
  -- The scalars preserve the image of `e` and the kernel of the Hecke polynomial.
  have h_mem (z : Gf D.E Unit) :
      Y.normalizedCentralOp z y ∈ (Y.descentPair.groupAlgAction e).range ⊓
        (Y.descentPair.heckePolyOnForms hw hS (Y.descentPair.liftHeckeRoot w)).ker := by
    refine smul_mem _ _ ⟨Y.centralRep_mem_range_groupAlgAction z hy_range, ?_⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, ← centralRep_heckePolyOnForms,
      LinearMap.mem_ker.1 hy_hecke, map_zero]
  -- So the sum of the translates of `y` lies in the space to which `Ξ` is orthogonal.
  have h_zero : inner ℂ (∑ c, Y.normalizedCentralOp (s c) y) Ξ = 0 :=
    hΞ w hw hS _ ⟨sum_mem fun c _ ↦ h_mem (s c),
      Y.sum_normalizedCentralOp_mem_ker_normalizedDescent h_aut hs hy_orth⟩
  simpa [inner_sum, inner_normalizedCentralOp, ← sum_inner] using h_zero

open scoped Classical in
/-- Let `Y` be data for a theta lift from `U(1)` to the definite `U(n)` over the CM field `D.E`,
with space of algebraic forms `Y.descentPair.FormV` on `U(n)` and lift `φ = Y.trivialLift`, let `ℓ`
be a prime and `ι : ℂ ≃ ℚ̄_ℓ`. Let the projection to the line `ℂ φ` have denominator at most `exp β`
at `ι` (`DenominatorLe`): an operator on the line, of determinant at least `exp (-β)` in norm, makes
integral the projection of every integral form that is orthogonal to the false lifts. Let all
stabilisers of `U(1)` at the chosen level be trivial. Let `Ξ`, `Ξ'` be integral above `ℓ` and
orthogonal to the false lifts in the kernel of the descent (`IsTestForm`). Then the class number of
`U(1)` at that level times the inner product of `Ξ` with the projection of `Ξ'` to the line has norm
at most `exp β` under `ι`. -/
lemma Selmer.DenominatorLe.norm_card_mul_inner_starProjection_le {ℓ : ℕ} [Fact ℓ.Prime]
    {ι : ℂ ≃+* PadicAlgCl ℓ} {β : ℝ}
    (h_denom : DenominatorLe ι Y.descentPair
      (tupleIdem Unit fun _ : Y.descentPair.ChosenIndex ↦ Polynomial.X - 1) (ℂ ∙ Y.trivialLift) β)
    (h_aut : ∀ g : Gf D.E Unit, classAut stdRatPoints Y.chosenLevel g = ⊥)
    {Ξ Ξ' : Y.descentPair.FormV} (hΞ : Y.descentPair.IsTestForm ℓ Ξ)
      (hΞ' : Y.descentPair.IsTestForm ℓ Ξ') :
    ‖ι (Nat.card (StdClasses Y.chosenLevel) *
      inner ℂ Ξ ((ℂ ∙ Y.trivialLift).starProjection Ξ'))‖ ≤ exp β := by
  -- Apply the bound on the line to `Ξ` and to the sum `Ξ''` of the twisted translates of `Ξ'` by
  -- the inverses of scalars `s c`, one for each class of `U(1)`. The twisted translations fix
  -- `Y.trivialLift`, so its pairing with `Ξ''` is the class number times its pairing with `Ξ'`.
  by_cases h_zero : Y.trivialLift = 0
  · simp [h_zero, exp_nonneg]
  obtain ⟨s, hs_mk, hs_int⟩ : ∃ s : StdClasses Y.chosenLevel → Gf D.E Unit,
      (∀ c, DoubleCoset.mk (stdSpace D.E Unit).Γf Y.chosenLevel (s c) = c) ∧
        ∀ c, s c ∈ integralAbove Unit ℓ :=
    exists_reps_integralAbove (K := Y.chosenLevel) ℓ
  obtain ⟨hΞ_int, -⟩ := hΞ
  obtain ⟨hΞ'_int, hΞ'_test⟩ := hΞ'
  let Ξ'' : Y.descentPair.FormV := ∑ c, Y.normalizedCentralOp (s c)⁻¹ Ξ'
  have h_int (j : PadicPlace ℓ) : Ξ'' ∈ LevelPlaces.LevelForm.integralForms j :=
    sum_mem fun c _ ↦ Y.normalizedCentralOp_inv_mem_integralForms j (hs_int c) (hΞ'_int j)
  have h_test : Y.descentPair.IsOrthogonalToFalseLifts (tupleIdem Unit fun _ ↦ Polynomial.X - 1)
      (ℂ ∙ Y.trivialLift)ᗮ Ξ'' :=
    Y.isOrthogonalToFalseLifts_sum_normalizedCentralOp_inv h_aut hs_mk hΞ'_test
  have h_proj : (ℂ ∙ Y.trivialLift).starProjection Ξ'' =
      (Nat.card (StdClasses Y.chosenLevel) : ℂ) • (ℂ ∙ Y.trivialLift).starProjection Ξ' := by
    simp [Ξ'', inner_sum, inner_normalizedCentralOp, normalizedCentralOp_trivialLift,
      starProjection_singleton ℂ, smul_smul, mul_div_assoc]
  -- On a line the operator `Λ` that clears the denominators is a number `μ`, its determinant.
  obtain ⟨Λ, h_det, h_clear⟩ := h_denom
  have h_rank : Module.finrank ℂ (ℂ ∙ Y.trivialLift) = 1 := finrank_span_singleton h_zero
  obtain ⟨μ, rfl⟩ : ∃ μ : ℂ, Λ = μ • LinearMap.id :=
    (Λ.existsUnique_eq_smul_id_of_finrank_eq_one h_rank).exists
  have hμ : exp (-β) ≤ ‖ι μ‖ := by simpa [h_rank] using h_det
  obtain ⟨-, h_inner⟩ := h_clear Ξ'' (h_int _) h_test
  have h_one : ‖ι μ‖ * ‖ι (inner ℂ Ξ ((ℂ ∙ Y.trivialLift).starProjection Ξ''))‖ ≤ 1 := by
    simpa [inner_smul_right] using h_inner Ξ hΞ_int
  grw [← hμ] at h_one
  rwa [Real.exp_neg, inv_mul_le_iff₀ (exp_pos β), mul_one, h_proj, inner_smul_right] at h_one

open scoped Classical in
/-- Let `Y` be data for a theta lift from `U(1)` to the definite `U(n)` over the CM field `D.E`,
with space of algebraic forms `Y.descentPair.FormV` on `U(n)` and lift `φ = Y.trivialLift`, let `ℓ`
be a prime and `ι : ℂ ≃ ℚ̄_ℓ`. Let the projection to the line `ℂ φ` have denominator at most `exp β`
at `ι` (`DenominatorLe`): an operator on the line, of determinant at least `exp (-β)` in norm, makes
integral the projection of every integral form that is orthogonal to the false lifts. Let all
stabilisers of `U(1)` at the chosen level be trivial. Let `Ξ`, `Ξ'` be integral above `ℓ` and
orthogonal to the false lifts in the kernel of the descent (`IsTestForm`). Then the inner product of
their projections to the line has norm under `ι` at most `exp β` times the `ℓ`-part of the class
number of `U(1)` at that level. -/
lemma Selmer.DenominatorLe.norm_inner_starProjection_le {ℓ : ℕ} [Fact ℓ.Prime]
    {ι : ℂ ≃+* PadicAlgCl ℓ} {β : ℝ}
    (h_denom : DenominatorLe ι Y.descentPair
      (tupleIdem Unit fun _ : Y.descentPair.ChosenIndex ↦ Polynomial.X - 1) (ℂ ∙ Y.trivialLift) β)
    (h_aut : ∀ g : Gf D.E Unit, classAut stdRatPoints Y.chosenLevel g = ⊥)
    {Ξ Ξ' : Y.descentPair.FormV} (hΞ : Y.descentPair.IsTestForm ℓ Ξ)
      (hΞ' : Y.descentPair.IsTestForm ℓ Ξ') :
    ‖ι (inner ℂ ((ℂ ∙ Y.trivialLift).starProjection Ξ) ((ℂ ∙ Y.trivialLift).starProjection Ξ'))‖ ≤
      exp (β + padicValNat ℓ (Nat.card (StdClasses Y.chosenLevel)) * log ℓ) := by
  set N : ℕ := Nat.card (StdClasses Y.chosenLevel)
  have hℓ : (0 : ℝ) < ℓ := Nat.cast_pos.2 (Fact.out : ℓ.Prime).pos
  have h_norm : ‖ι N‖ = (ℓ : ℝ)⁻¹ ^ padicValNat ℓ N := by
    rw [← norm_natCast_eq_inv_pow_padicValNat Nat.card_pos.ne', map_natCast,
      ← PadicComplex.norm_extends ℓ]
    exact congrArg norm (map_natCast (algebraMap (PadicAlgCl ℓ) ℂ_[ℓ]) N)
  have h_bound : ‖ι (N * inner ℂ Ξ ((ℂ ∙ Y.trivialLift).starProjection Ξ'))‖ ≤ exp β :=
    h_denom.norm_card_mul_inner_starProjection_le Y h_aut hΞ hΞ'
  rw [map_mul, norm_mul, h_norm, inv_pow, inv_mul_le_iff₀ (by positivity)] at h_bound
  rwa [inner_starProjection_left_eq_right,
    starProjection_eq_self_iff.2 (starProjection_apply_mem _ Ξ'), exp_add, exp_nat_mul,
    exp_log hℓ, mul_comm]

end New

end
