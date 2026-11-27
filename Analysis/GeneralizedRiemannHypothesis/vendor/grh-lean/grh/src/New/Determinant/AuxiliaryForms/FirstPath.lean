import New.Determinant.AuxiliaryForms.DeepLevelVanishing
import New.Determinant.AuxiliaryForms.GridFirstColumns
import New.Determinant.Chain.ChainNorms

/-!
# The maps `Θ^♭` and `res^♭`, and the first path

The first path consists of the spaces `Ỹ^m_0, …, Ỹ^0_0` and `Y₀, …, Y_m`, which are hermitian spaces
over the CM field `D.E`. These are the nodes `(z, 0, i)`, the first columns of the two grids:
`(false, 0, i)` is `Y_i` and `(true, 0, i)` is `Ỹ^i_0`. The iterated transposed lifts
`New.Data.transposedChain` along such a column are the transposes of the chain of theta lifts
`New.Exchange.weightedChain`. In the grid of the `Ỹ` the composite of all `m` of them is
`Θ^♭ = D.transposedChain 1 true 0`. The letter `ϑ` stands for an `m`-fold twist (`D.MFoldTwist`): a
tame character whose powers up to the `m`-th are non-trivial at each place of its modulus `Q`.

Notions from other files:
* `New.Data.GridForm` and `New.Data.TriangleForm`: in the grid of the `Y` (the Boolean `false`) the
  conjugate forms and the forms at a node; in the grid of the `Ỹ` (the Boolean `true`) the forms and
  the conjugate forms.
* `New.Data.triangleModulus`: the modulus of the point data along the first column of a grid. It is
  `𝔪₀ = π_M Q` for the `Y` and `𝔟 = π_M ^ b` for the `Ỹ`, with `π_M = D.piM`.
* `New.Data.triangleGLCard`: the index `n_𝔪₀(Y_i)` or `n_𝔟(Ỹ^i_0)` of the level of that modulus.
  Each lift and each transposed lift along the column is multiplied by the index of its smaller
  space; for the `Ỹ` these factors are constants.
* `New.Data.principalForms`: the forms of the level `J_M = D.chosenLevel`, here on `Y₀`.
* `New.Data.lowerChainUpTo`: the chain of twisted lifts from `Y₀` to `Y_j`; for `j = m` it is `Θ_ϑ`.

## Main definitions and results

* `New.Data.eq_zero_of_weightedChain_triangleLift_eq_zero`,
  `New.Data.gridLevelForms_eq_map_transposedChain`: the chain of the `Ỹ` is injective on level `𝔟`,
  and its transpose `Θ^♭` is onto that level.
* `New.Data.IsFlatRestriction`: the map `res^♭`, given by its pairings;
  `New.Data.exists_isFlatRestriction_range_eq_top`: at a suitable real point it is onto.
* `New.Data.exists_isPathDatum_integral_eq`: the pairing with the lifts of a restriction is a
  constant multiple of a period of path data on the first path.

## Relation to the literature

See `New.Determinant.AuxiliaryForms.DeepLevelVanishing` for related work.
-/

namespace New.Data

/-! ## Transposes of the chains of lifts, and surjectivity of `Θ^♭` -/

section DescentOnto

open Space Submodule MeasureTheory Modulus

variable {P : Parameters} (D : Data P)

/-- Grid `z` is the grid of the `Y` for `z = false` and that of the `Ỹ` for `z = true`; its first
column has the nodes `0, …, m`. Let `χ = gridChar ϑ (!z) i n'` be the idele class character of
`U(1)` attached to the edge between the nodes `i` and `i + 1` of this column. It carries the twist
`ϑ ^ (i + 1)` for the `Y` and no twist for the `Ỹ`; the type `n'` enters only through the exponent
of the restriction `upsilonU1` to `U(1)` of the splitting character of the Weil representation.
Then `χ` is trivial on the determinant `detFin s u` of every finite integral point `u` of a unitary
group that is trivial modulo `triangleModulus z ϑ`, the ideal `π_M Q` for the `Y` and
`π_M ^ D.natB` for the `Ỹ`. The signs `s` are those of the hermitian form at the infinite places
and do not matter at the finite ones. -/
lemma gridChar_detFin_eq_one (z : Bool) (ϑ : D.MFoldTwist) (i : ℕ) (n' : Type) [Fintype n']
    {n : Type} [Fintype n] [DecidableEq n] (s : n → ℤˣ) {u : stdLevel D.E n}
    (hu : (triangleModulus z ϑ).reductionGL u = 1) :
    (gridChar ϑ (!z) i n').val (detFin s u.val) = 1 := by
  -- The tame part is trivial outside the modulus, so the value depends only on `u` modulo it.
  have h_unramified (w : FinPlace D.E) (hw : w ∉ (triangleModulus z ϑ).places) :
      gridTamePart ϑ (!z) i w = 1 := by
    -- The places of the modulus are the chosen and twist places, outside which the part is trivial.
    cases z <;> rw [Rows.places_levelModulus] at hw
    · exact (D.descentPair (ϑ.pow (i + 1)) (i + 1)).tame_eq_one w hw
    · exact (D.descentPair .one (i + 1)).tame_eq_one w hw
  have h_value : ((gridChar ϑ (!z) i n').val (detFin s u.val) : ℂ) =
      (triangleModulus z ϑ).charOfTamePart (gridTamePart ϑ (!z) i)
        ((triangleModulus z ϑ).reductionGL u).val.det :=
    (gridChar_hasWeight ϑ (!z) i n').apply_det_eq_charOfTamePart h_unramified u
  ext
  simp [h_value, hu]

/-- Let `S` and `T` be the hermitian spaces `D.gridSpace 0 z 0 i` and `D.gridSpace 0 z 0 (i + 1)` at
the nodes `i` and `i + 1` of the first column of the grid of the `Y` (`z = false`) or of the `Ỹ`
(`z = true`); the first argument `0`, the offset, selects the grids themselves. The product of their
adelic unitary groups acts on the data on `Hom(S, T)` by `New.pairWeil`, the Weil representation
times the characters `gridChar` of the edge on the two determinants. A pair `(u, u')` of finite
integral points that are trivial modulo the ideal `𝔫 = triangleModulus z ϑ` fixes the datum
`New.modDatum S T 𝔫 Ψ v`. This is the product of `v` at the infinite places, a vector of the Fock
model for the signs of `Hom(S, T)`, the function `Ψ` of matrices modulo `𝔫` at the places of `𝔫`,
and the vacuum elsewhere. -/
lemma pairWeil_gridChar_modDatum_eq_self (z : Bool) (ϑ : D.MFoldTwist) (i : ℕ)
    {u : stdLevel D.E (D.GridIndex z 0 i)} (hu : (triangleModulus z ϑ).reductionGL u = 1)
    {u' : stdLevel D.E (D.GridIndex z 0 (i + 1))} (hu' : (triangleModulus z ϑ).reductionGL u' = 1)
    (Ψ : Matrix (D.GridIndex z 0 (i + 1)) (D.GridIndex z 0 i) (triangleModulus z ϑ).ResidueRing → ℂ)
    (v : Heisenberg.IsVacuum.Model
      (Fock.realHeisenberg
        (realSigns D.E (homSigns (D.gridSigns z 0 0 i) (D.gridSigns z 0 0 (i + 1)))))) :
    pairWeil (D.gridSpace 0 z 0 i) (D.gridSpace 0 z 0 (i + 1))
        (gridChar ϑ (!z) i (D.GridIndex z 0 i)) (gridChar ϑ (!z) i (D.GridIndex z 0 (i + 1)))
        ((1, u.val), 1, u'.val)
        (modDatum (D.gridSpace 0 z 0 i) (D.gridSpace 0 z 0 (i + 1)) (triangleModulus z ϑ) Ψ v) =
      modDatum (D.gridSpace 0 z 0 i) (D.gridSpace 0 z 0 (i + 1)) (triangleModulus z ϑ) Ψ v := by
  -- The pair acts through its reduction modulo the modulus and through the two characters.
  rw [pairWeil_modDatum_stdLevel, D.gridChar_detFin_eq_one z ϑ i _ _ hu,
    D.gridChar_detFin_eq_one z ϑ i _ _ hu', hu, hu']
  simp

/-- Let `φ` be an element of `GridForm z 0 D.m`: a conjugate form on `Y_m` for `z = false`, a form
on `Ỹ^m_0` for `z = true`. For a node `i < m` of that column, `transposedChain ϑ z i φ` is the image
of `φ` at the node `i` under the composite of the transposed theta lifts between neighbouring nodes,
a form with the weight `gridKernel z 0 i true`. Right translation `formRep` by a finite integral
point `u` that is trivial modulo `triangleModulus z ϑ` fixes this image. -/
lemma formRep_transposedChain_eq_self (z : Bool) (ϑ : D.MFoldTwist) {i : ℕ} (hi_lt : i < D.m)
    (φ : D.GridForm z 0 D.m) (u : stdLevel D.E (D.GridIndex z 0 i))
    (hu : (triangleModulus z ϑ).reductionGL u = 1) :
    (D.gridSpace 0 z 0 i).formRep (D.gridKernel z 0 i true) u.val (transposedChain ϑ z i φ) =
      transposedChain ϑ z i φ := by
  -- The last transposed lift has a datum that `(u, 1)` fixes.
  have h_pointLift_fixed (x : D.GridForm z 0 (i + 1)) :
      (D.gridSpace 0 z 0 i).formRep (D.gridKernel z 0 i true) u.val (pointTransposedLift ϑ z i x) =
        pointTransposedLift ϑ z i x := by
    obtain ⟨-, h_arrow⟩ := (isEdgeFamily_grid_succ_right (z := z) id zero_le hi_lt).isArrow_modDatum
      (i := ϑ) (S := D.gridSpace 0 z 0 i) (T := D.gridSpace 0 z 0 (i + 1))
      (Ψ := Exchange.pointDatum (triangleModulus z ϑ).ResidueRing)
    let transposedLift : D.GridForm z 0 (i + 1) →ₗ[ℂ] D.GridForm z 0 i :=
      Exchange.modTransposedLift (D.gridSpace 0 z 0 i) (D.gridSpace 0 z 0 (i + 1))
        (gridChar ϑ (!z) i)
        (D.gridHarmonic 0 false (!z) i z 0 i 0 (i + 1))
        (Exchange.pointDatum (triangleModulus z ϑ).ResidueRing)
        (D.gridKernel z 0 (i + 1) true) (D.gridKernel z 0 i true)
    -- As `(u, 1)` fixes the datum, `u` fixes every transposed lift.
    have h_datum := D.pairWeil_gridChar_modDatum_eq_self z ϑ i hu (u' := 1) (map_one _)
    have h_law : (D.gridSpace 0 z 0 i).formRep (D.gridKernel z 0 i true) u.val (transposedLift x) =
        transposedLift x := by
      simpa using! h_arrow.formRep_formLift_of_eq_smul (c := 1)
        ((h_datum _ _).trans (one_smul ℂ _).symm) x
    have h_weight :
        pointTransposedLift ϑ z i x = (triangleGLCard z ϑ i : ℂ) • transposedLift x := rfl
    rw [h_weight, map_smul, h_law]
  rw [transposedChain_of_lt ϑ hi_lt, LinearMap.comp_apply, h_pointLift_fixed]

/-- The space `TriangleForm z 0 i` consists of forms on `Y_i` for `z = false` and of conjugate forms
on `Ỹ^i_0` for `z = true`. For `0 < i ≤ m` let `y` be such a form at the node `0`. Its image under
the weighted chain of the `i` theta lifts `triangleLift` between neighbouring nodes, the one from
the node `b` multiplied by `triangleGLCard z ϑ b`, is fixed under right translation `triangleRep` by
every finite integral point `u` of the unitary group at the node `i` that is trivial modulo
`triangleModulus z ϑ`. -/
lemma triangleRep_weightedChain_eq_self (z : Bool) (ϑ : D.MFoldTwist) {i : ℕ} (hi_ne : i ≠ 0)
    (hi_le : i ≤ D.m) (y : D.TriangleForm z 0 0) (u : stdLevel D.E (D.GridIndex z 0 i))
    (hu : (triangleModulus z ϑ).reductionGL u = 1) :
    D.triangleRep z 0 i u.val (Exchange.weightedChain (D.triangleGLCard z) (D.triangleLift z) ϑ 0 i
      y) =
      Exchange.weightedChain (D.triangleGLCard z) (D.triangleLift z) ϑ 0 i y := by
  -- The last lift has a datum that `(1, u)` fixes.
  obtain ⟨i, rfl⟩ : ∃ j : ℕ, i = j + 1 := Nat.exists_eq_succ_of_ne_zero hi_ne
  have h_lift (x : D.TriangleForm z 0 i) :
      D.triangleRep z 0 (i + 1) u.val (D.triangleLift z ϑ 0 i x) = D.triangleLift z ϑ 0 i x := by
    obtain ⟨h_arrow, -⟩ := (isEdgeFamily_grid_succ_right (z := z) id zero_le hi_le).isArrow_modDatum
      (i := ϑ) (S := D.gridSpace 0 z 0 i) (T := D.gridSpace 0 z 0 (i + 1))
      (Ψ := Exchange.pointDatum (triangleModulus z ϑ).ResidueRing)
    -- As `(1, u)` fixes the datum, `u` fixes every lift.
    have h_datum := D.pairWeil_gridChar_modDatum_eq_self z ϑ i (u := 1) (map_one _) hu
    simpa using! h_arrow.formRep_formLift_of_eq_smul (c := 1)
      ((h_datum _ _).trans (one_smul ℂ _).symm) x
  rw [Exchange.weightedChain_succ_apply, map_smul, h_lift]

/-- For a node `i ≤ m`, let `U` be the image of `y` under the weighted chain of the `i` theta lifts
`triangleLift`, the one from the node `b` multiplied by `triangleGLCard z ϑ b`, the index at `b` of
the level of modulus `triangleModulus z ϑ`. Let `T b = transposedChain ϑ z b` be the composite of
the transposed lifts, equally weighted, from the node `m` to the node `b`; it acts on `φ`, which has
the conjugate weight to that of `y`. Then `∫ T i φ * U = ∫ T 0 φ * y`, each integral over the adelic
unitary group `New.G` of the node with its measure `quotMeasure` on the automorphic quotient. -/
lemma integral_transposedChain_mul_weightedChain (z : Bool) (ϑ : D.MFoldTwist) {i : ℕ}
    (hi_le : i ≤ D.m) (y : D.TriangleForm z 0 0) (φ : D.GridForm z 0 D.m) :
    ∫ g : New.G D.E (D.gridSigns z 0 0 i),
        transposedChain ϑ z i φ g *
          Exchange.weightedChain (D.triangleGLCard z) (D.triangleLift z) ϑ 0 i y g
        ∂(D.gridSpace 0 z 0 i).quotMeasure =
      ∫ g : New.G D.E (D.gridSigns z 0 0 0), transposedChain ϑ z 0 φ g * y g
        ∂(D.gridSpace 0 z 0 0).quotMeasure := by
  -- Induction on `i`; the step uses the edge from node `i` to node `i + 1`.
  induction i with
  | zero => rfl
  | succ i ih => ?_
  obtain ⟨h_lift, h_transposed⟩ :=
    (isEdgeFamily_grid_succ_right (z := z) id zero_le hi_le).isArrow_modDatum
      (i := ϑ) (S := D.gridSpace 0 z 0 i) (T := D.gridSpace 0 z 0 (i + 1))
      (Ψ := Exchange.pointDatum (triangleModulus z ϑ).ResidueRing)
  -- The lift and the transposed lift along the edge carry the same weight.
  have h_transpose (x : D.GridForm z 0 (i + 1)) (w : D.TriangleForm z 0 i) :
      ∫ g, x g * ((triangleGLCard z ϑ i : ℂ) • D.triangleLift z ϑ 0 i w) g
          ∂(D.gridSpace 0 z 0 (i + 1)).quotMeasure =
        ∫ g, pointTransposedLift ϑ z i x g * w g ∂(D.gridSpace 0 z 0 i).quotMeasure := by
    -- Move the weight inside the lift, transpose, and regroup it with the transposed lift.
    rw [← map_smul]
    refine (h_lift.integral_mul_formLift_swap h_transposed
      ((triangleGLCard z ϑ i : ℂ) • w) x).trans ?_
    congr 1 with g
    exact mul_right_comm (triangleGLCard z ϑ i : ℂ) (w g) _
  rw [Exchange.weightedChain_succ_apply, h_transpose, ← ih (Nat.le_of_succ_le hi_le),
    transposedChain_of_lt ϑ hi_le, LinearMap.comp_apply]

/-- The grid of the `Ỹ` (the Boolean `true`) has the weight of the `Y` with the opposite sign, so
its `TriangleForm`s are conjugate forms; `D.triangleBase true` consists of those on `Ỹ^0_0` of level
`𝔟 = D.piM ^ D.natB`. The weighted chain of all `D.m` theta lifts `New.Data.triangleLift` from
`Ỹ^0_0` to `Ỹ^m_0`, for the trivial twist `1`, is injective on this space. -/
lemma eq_zero_of_weightedChain_triangleLift_eq_zero {y : D.triangleBase true}
    (hy : Exchange.weightedChain (D.triangleGLCard true) (D.triangleLift true) 1 0 D.m y = 0) :
    y = 0 := by
  obtain ⟨d, h_triangle, -⟩ := D.exists_isTriangle true
  exact h_triangle.eq_zero_of_weightedChain_eq_zero D.m 0 (by simp) y hy

/-- Let `Ỹ^i_0` be the hermitian space at the node `(0, i)` of the grid of the `Ỹ` (the Boolean
`true`), and `D.gridLevelForms i` the forms of level `𝔟` on it: those fixed under right translation
by the finite integral points congruent to `1` modulo `𝔟 = D.piM ^ D.natB`, a power of the generator
of the product of the chosen places. For `i < m` the transposed theta lift from `Ỹ^(i+1)_0` to
`Ỹ^i_0` is weighted by the index of that level on `Ỹ^i_0`. The composite
`Θ^♭ = D.transposedChain 1 true 0` of all `D.m` of them, for the trivial twist `1`, maps forms of
level `𝔟` on `Ỹ^m_0` to forms of level `𝔟` on `Ỹ^0_0`. -/
lemma map_transposedChain_le_gridLevelForms :
    (D.gridLevelForms D.m).map (D.transposedChain 1 true 0) ≤ D.gridLevelForms 0 := by
  rintro _ ⟨φ, -, rfl⟩
  refine mem_levelSpace_formRep_iff.2 fun k hk g ↦ ?_
  have h_fixed : (D.gridSpace 0 true 0 0).formRep (D.gridKernel true 0 0 true) k
      (D.transposedChain 1 true 0 φ) = D.transposedChain 1 true 0 φ :=
    D.formRep_transposedChain_eq_self true 1 (Nat.pos_of_neZero D.m) φ ⟨k, hk.1⟩
      ((mem_principalLevel_iff gridModulus_one_ideal _).1 hk)
  exact congrFun (congrArg Subtype.val h_fixed) g

/-- Take the transposed theta lifts from `Ỹ^(i+1)_0` to `Ỹ^i_0` for `i < D.m`. Their composite
`Θ^♭ = D.transposedChain 1 true 0`, for the trivial twist `1`, maps the forms of level `𝔟` on
`Ỹ^m_0` onto those on `Ỹ^0_0`. -/
lemma gridLevelForms_eq_map_transposedChain :
    D.gridLevelForms 0 = (D.gridLevelForms D.m).map (D.transposedChain 1 true 0) := by
  -- The image of `Θ^♭` lies in `D.gridLevelForms 0`, so it suffices that a form `z` of this level
  -- orthogonal to the image vanishes. The chain of lifts is the transpose of `Θ^♭`
  -- (`integral_transposedChain_mul_weightedChain`), so the lift `U` of `conj z` has
  -- `‖U‖ ^ 2 = ⟪z, Θ^♭ (conj U)⟫ = 0`; and the chain is injective.
  have : Module.Finite ℂ (D.gridLevelForms D.m) :=
    finite_levelSpace (isConjKernelPair_gridKernel (by simp) _).1
      ⟨_, isOpen_principalLevel Fact.out⟩
  suffices orth_le : ((D.gridLevelForms D.m).map (D.transposedChain 1 true 0))ᗮ ⊓ D.gridLevelForms 0
    ≤ ⊥ by
    simpa [le_bot_iff.1 orth_le] using
      (sup_orthogonal_inf_of_hasOrthogonalProjection D.map_transposedChain_le_gridLevelForms).symm
  rintro z ⟨hz_orth, hz_level⟩
  -- `y` is the conjugate of `z`, `U` its chain of lifts, and `φ` the conjugate of `U`.
  let y : D.triangleBase true := ⟨conjForm (isConjKernelPair_gridKernel (by simp) true).2 z,
    mem_levelSpace_formRep_iff.2 fun k hk g ↦
      congrArg star (mem_levelSpace_formRep_iff.1 hz_level k hk g)⟩
  let U : D.TriangleForm true 0 D.m :=
    Exchange.weightedChain (D.triangleGLCard true) (D.triangleLift true) 1 0 D.m y
  let φ : D.GridForm true 0 D.m := conjForm (isConjKernelPair_gridKernel (by simp) false).2 U
  have φ_mem : φ ∈ D.gridLevelForms D.m := by
    refine mem_levelSpace_formRep_iff.2 fun k hk g ↦ ?_
    have h_fixed : D.triangleRep true 0 D.m k U = U :=
      D.triangleRep_weightedChain_eq_self true 1 (NeZero.ne D.m) le_rfl y ⟨k, hk.1⟩
        ((mem_principalLevel_iff gridModulus_one_ideal _).1 hk)
    exact congrArg star (congrFun (congrArg Subtype.val h_fixed) g)
  -- The transposition identity at `φ`; `transposedChain ϑ z D.m` is the identity.
  have h_integral : ∫ g, φ.1 g * U.1 g ∂(D.gridSpace 0 true 0 D.m).quotMeasure =
      ∫ g, y.1.1 g * (D.transposedChain 1 true 0 φ).1 g ∂(D.gridSpace 0 true 0 0).quotMeasure := by
    simpa [transposedChain_self, mul_comm (D.transposedChain 1 true 0 φ _)] using
      D.integral_transposedChain_mul_weightedChain true 1 le_rfl y φ
  -- As `φ` and `y` are the conjugates of `U` and `z`, both integrals are inner products.
  have transpose : inner ℂ U U = inner ℂ z (D.transposedChain 1 true 0 φ) := h_integral
  -- The right side vanishes, as `z` is orthogonal to the image.
  have U_zero : U = 0 := by
    simpa [inner_eq_zero_symm.1 (hz_orth _ ⟨φ, φ_mem, rfl⟩)] using transpose
  have h_conj : conjForm (isConjKernelPair_gridKernel (by simp) true).2 z = 0 :=
    congrArg Subtype.val (D.eq_zero_of_weightedChain_triangleLift_eq_zero U_zero)
  exact Subtype.ext (star_eq_zero.1 (congrArg Subtype.val h_conj))

end DescentOnto

/-!
## The first path

Restrictions of forms that come from the definite space `Ỹ^m_0` reach every form of level `J_M` on
`Y₀`, and the pairing with the chain of lifts of such a restriction is a period of path data on the
first path.
-/

section FirstPath

open MeasureTheory Function Exchange Space Submodule

variable {P : Parameters} (D : Data P)

/-- Every form is reached. Here `Y₀ = D.spaceY 0`, and `Ỹ^0_0` is its orthogonal sum with a line.
The level `J_M` consists of the finite integral points that are congruent to `1` modulo every chosen
place, that is, modulo every prime divisor of `π_M = D.piM`; `principalForms` are the forms of this
level. There is a real point `g₀` of `U(Ỹ^0_0)` such that for every such form `y ≠ 0` on `Y₀` there
is a form `φ` of level `𝔟 = π_M ^ D.natB` on the definite space `Ỹ^m_0` (`gridLevelForms D.m`) with
a nonzero pairing `diagonalPeriodForm` of the conjugate `conjForm` of `y` and `Θ^♭ φ` at `g₀`: the
integral of `star (y h)` times `(Θ^♭ φ) (h g₀)` over `U(Y₀)`. Here `Θ^♭` is
`D.transposedChain 1 true 0`, the composite of the transposed theta lifts whose datum at the places
of `𝔟` is the indicator of the inclusion matrix (`pointDatum`), each weighted by the index of the
level `𝔟` on its target. -/
lemma exists_forall_diagonalPeriodForm_ne_zero :
    ∃ g₀ : GInf D.E (D.gridSigns true 0 0 0), ∀ y ∈ D.principalForms (D.spaceY 0), y ≠ 0 →
      ∃ φ ∈ D.gridLevelForms D.m,
        diagonalPeriodForm 1 zero_le g₀ (conjForm D.gridKernel_zero_true_eq_star y)
          (D.transposedChain 1 true 0 φ) ≠ 0 := by
  -- `Θ^♭` is onto the forms of level `𝔟`, and no `y ≠ 0` is orthogonal to all their restrictions.
  obtain ⟨g₀, h_eq_zero_of_orthogonal⟩ := D.exists_eq_zero_of_orthogonal_gridLevelForms
  refine ⟨g₀, fun y hy hy_ne ↦ ?_⟩
  by_contra! h_zero
  refine hy_ne (Subtype.ext (h_eq_zero_of_orthogonal y hy fun ψ hψ ↦ ?_))
  obtain ⟨φ, hφ, rfl⟩ := D.gridLevelForms_eq_map_transposedChain.le hψ
  -- The pairing of `y` with a restriction is, by definition, the period of the conjugate of `y`.
  have h_period (F : D.GridForm true 0 0) :
      (D.spaceY 0).petersson y.val
          (fun x ↦ F (G.reindex (.refl (D.Y 0 ⊕ Unit)) D.gridSigns_true_zero.symm (.sum (x, 1)) *
            (g₀, 1))) =
        diagonalPeriodForm 1 zero_le g₀ (conjForm D.gridKernel_zero_true_eq_star y) F := by
    simp [petersson, periodPairing]
    rfl
  exact (h_period _).trans (h_zero φ hφ)

variable {D} in
/-- `r` is a restriction map `res^♭` at the real point `g` of the unitary group of `Ỹ^0_0`, the sum
of `Y₀` and a line, in the sense of its pairings: every form `y` on `Y₀` of level `𝔪₀ = π_M Q`,
where `Q` is the modulus of some twist, has the same pairing with `r φ` as with the function
`h ↦ (Θ^♭ φ) (h g)` on `U(Y₀)`. Here `φ` is a form of level `𝔟` on `Ỹ^m_0` and `Θ^♭` is
`D.transposedChain 1 true 0`. The forms `y` of the level `J_M` (that of the prime divisors of
`π_M`) are among these, and their pairings determine `r`. -/
def IsFlatRestriction (g : GInf D.E (D.gridSigns true 0 0 0))
    (r : D.gridLevelForms D.m →ₗ[ℂ] D.principalForms (D.spaceY 0)) : Prop :=
  ∀ (φ : D.gridLevelForms D.m) (ϑ : D.MFoldTwist),
    ∀ y ∈ levelSpace ((D.gridSpace 0 false 0 0).formRep (D.gridKernel false 0 0 false))
      (levelY ϑ 0),
    (D.spaceY 0).petersson y (r φ) =
      diagonalPeriodForm ϑ zero_le g (conjForm D.gridKernel_zero_true_eq_star y)
        (D.transposedChain 1 true 0 φ)

/-- Let `g` be a real point (`GInf`) of the unitary group of `Ỹ^0_0`, the sum of `Y₀ = D.spaceY 0`
and a line. Some linear map `r` from the forms of level `𝔟 = π_M ^ D.natB`, where `π_M = D.piM`, on
`Ỹ^m_0` (`gridLevelForms D.m`) to the forms on `Y₀` of level `J_M` (`principalForms`: integral
points congruent to `1` modulo the prime divisors of `π_M`) satisfies `IsFlatRestriction g`. -/
lemma exists_isFlatRestriction (g : GInf D.E (D.gridSigns true 0 0 0)) :
    ∃ r : D.gridLevelForms D.m →ₗ[ℂ] D.principalForms (D.spaceY 0), IsFlatRestriction g r := by
  obtain ⟨proj, h_proj⟩ := D.exists_petersson_eq_diagonalPeriodForm g
  let thetaFlat : D.gridLevelForms D.m →ₗ[ℂ] D.gridLevelForms 0 :=
    (D.transposedChain 1 true 0).restrict
      fun φ hφ ↦ D.gridLevelForms_eq_map_transposedChain.ge (mem_map_of_mem hφ)
  exact ⟨proj ∘ₗ thetaFlat, fun φ ↦ h_proj (thetaFlat φ)⟩

/-- Let `Ỹ^0_0` be the orthogonal sum of `Y₀` and a line. There are a real point `g` of its unitary
group and a surjective linear map `r` from the forms of level `𝔟 = π_M ^ D.natB` on `Ỹ^m_0` to the
forms on `Y₀` of level `J_M` with `IsFlatRestriction g r`: every form `y` on `Y₀` of level
`𝔪₀ = π_M Q`, for an `m`-fold twist with modulus `Q`, has the same Petersson product with `r φ` as
with the function `h ↦ (Θ^♭ φ) (h g)` on `U(Y₀)`. -/
lemma exists_isFlatRestriction_range_eq_top :
    ∃ (g : GInf D.E (D.gridSigns true 0 0 0))
      (r : D.gridLevelForms D.m →ₗ[ℂ] D.principalForms (D.spaceY 0)),
      IsFlatRestriction g r ∧ r.range = ⊤ := by
  obtain ⟨g, h_reach⟩ := D.exists_forall_diagonalPeriodForm_ne_zero
  obtain ⟨r, hr⟩ := D.exists_isFlatRestriction g
  -- The space is finite-dimensional, and a form `y` orthogonal to the range is zero.
  refine ⟨g, r, hr, orthogonal_eq_bot_iff.1 (bot_unique fun y hy ↦ Subtype.ext ?_)⟩
  by_contra hy_ne
  obtain ⟨φ, hφ, h_ne⟩ := h_reach _ y.2 hy_ne
  have h_orthogonal : (D.spaceY 0).petersson y.1.1 (r ⟨φ, hφ⟩).1.1 = 0 :=
    inner_eq_zero_symm.1 (hy _ (LinearMap.mem_range_self r ⟨φ, hφ⟩))
  -- The forms of level `J_M` have the level `𝔪₀` of the trivial twist.
  have h_pairing : (D.spaceY 0).petersson y.1.1 (r ⟨φ, hφ⟩).1.1 =
      diagonalPeriodForm 1 zero_le g (conjForm D.gridKernel_zero_true_eq_star y.val)
        (D.transposedChain 1 true 0 φ) :=
    hr ⟨φ, hφ⟩ 1 _ (levelSpace_anti (levelY_le_chosenLevel ..) y.2)
  exact h_ne (h_pairing.symm.trans h_orthogonal)

variable {D} in
/-- Let `r` be a restriction map at `g` (`IsFlatRestriction`): it sends a form `φ` of level `𝔟` on
`Ỹ^m_0` to the form on `Y₀` with the Petersson products of `h ↦ (Θ^♭ φ) (h g)`. Let `y'` be in
`GridForm false 0 D.m`, a form on `Y_m` of the conjugate weight, and `ϑ` an `m`-fold twist. Then the
integral of `y'` times `lowerChainUpTo` of `r φ`, its image under the theta lifts twisted by `ϑ` and
weighted by level indices, is the period `diagonalPeriodForm` at `g`: the integral over `U(Y₀)` of
`y'Lift h * (Θ^♭ φ) (h g)`, where `y'Lift = transposedChain ϑ false 0 y'`. -/
lemma IsFlatRestriction.integral_lowerChainUpTo {g : GInf D.E (D.gridSigns true 0 0 0)}
    {r : D.gridLevelForms D.m →ₗ[ℂ] D.principalForms (D.spaceY 0)} (hr : IsFlatRestriction g r)
    (ϑ : D.MFoldTwist) (y' : D.GridForm false 0 D.m) (φ : D.gridLevelForms D.m) :
    ∫ x, y' x * D.lowerChainUpTo ϑ D.m (r φ) x ∂(D.spaceY D.m).quotMeasure =
      diagonalPeriodForm ϑ zero_le g (transposedChain ϑ false 0 y')
        (D.transposedChain 1 true 0 φ) := by
  -- Transpose to `Y₀`; against the transposed lift `y'Lift` of `y'`, of level `𝔪₀`, one may
  -- replace `r φ` by the restriction of `Θ^♭ φ`.
  let y'Lift : D.GridForm false 0 0 := transposedChain ϑ false 0 y'
  let y'Lift_conj : (D.gridSpace 0 false 0 0).Form (D.gridKernel false 0 0 false) :=
    conjForm (isConjKernelPair_gridKernel (by simp) true).2 y'Lift
  have h_level : y'Lift_conj ∈
      levelSpace ((D.gridSpace 0 false 0 0).formRep (D.gridKernel false 0 0 false))
        (levelY ϑ 0) := by
    refine mem_levelSpace_formRep_iff.2 fun k hk x ↦ ?_
    have h_fix :
        (D.gridSpace 0 false 0 0).formRep (D.gridKernel false 0 0 true) k y'Lift = y'Lift :=
      D.formRep_transposedChain_eq_self false ϑ (Nat.pos_of_neZero D.m) y' ⟨k, (mem_levelOf.1 hk).1⟩
        ((LevelPlaces.ker_reductionGL_eq _).ge (mem_levelOf.1 hk).2)
    exact congrArg (fun F : D.GridForm false 0 0 ↦ star (F x)) h_fix
  have h_restrict :
      ∫ x, y'Lift x * (r φ).1 x ∂(D.spaceY 0).quotMeasure =
        diagonalPeriodForm ϑ zero_le g y'Lift (D.transposedChain 1 true 0 φ) := by
    simpa [y'Lift_conj, petersson, periodPairing] using! hr φ ϑ y'Lift_conj h_level
  -- The chain of lifts is `weightedChain` with the weight written as the order of a group.
  have h_chain : D.lowerChainUpTo ϑ D.m (r φ) =
      weightedChain (D.triangleGLCard false) (D.triangleLift false) ϑ 0 D.m (r φ).1 := by
    simp +unfoldPartialApp [liftY, lowerChainUpTo, ← LevelPlaces.card_GL_levelModulus]
    rfl
  -- By transposition the left side is `∫ y'Lift x * r φ x`.
  refine Eq.trans ?_ h_restrict
  simpa [transposedChain_self, h_chain] using!
    D.integral_transposedChain_mul_weightedChain false ϑ le_rfl (r φ).1 y'

/-- The twisted edges are those that carry a power of the twist `ϑ` (`IsVerticalEdge`). There are
functions `Ψ ϑ`, one for each twist `ϑ`, of tuples `EdgeTuple ϑ` and a constant `α` as follows.
* `Ψ ϑ` is a path datum (`IsPathDatum`) on the first path: a function of the matrices on its edges,
  invariant up to the edge characters under admissible families of group elements at the nodes, zero
  unless those on twisted edges have left inverses, with values sums of at most
  `edgeMatrixCountBound ϑ ^ (2 * D.m)` roots of unity.
* Whenever `r` is a restriction map at `g`, the pairing of a conjugate form `y'` on `Y_m` with the
  chain `lowerChainUpTo` of theta lifts of `r φ` is `α` times `gridPeriod`: the sum over the tuples
  `S` on the path of `Ψ ϑ S` times the period `diagonalPeriodForm` at `g` of the images of `y'` and
  `φ` under the transposed lifts with the matrices of `S` along the two halves. -/
lemma exists_isPathDatum_integral_eq :
    ∃ Ψ : ∀ ϑ : D.MFoldTwist, EdgeTuple ϑ → ℂ,
      (∀ ϑ : D.MFoldTwist,
        IsPathDatum (edgeMatrixCountBound ϑ ^ (2 * D.m)) (TwoGridPath.first D.m).edges (Ψ ϑ)) ∧
      ∃ α : ℂ, ∀ (g : GInf D.E (D.gridSigns true 0 0 0))
        (r : D.gridLevelForms D.m →ₗ[ℂ] D.principalForms (D.spaceY 0)), IsFlatRestriction g r →
        ∀ (ϑ : D.MFoldTwist) (y' : D.GridForm false 0 D.m) (φ : D.gridLevelForms D.m),
          ∫ x, y' x * D.lowerChainUpTo ϑ D.m (r φ) x ∂(D.spaceY D.m).quotMeasure =
            α * gridPeriod (.first D.m) Ψ g (ϑ, y', φ) := by
  obtain ⟨α, Ψ, hΨ⟩ := exists_isPathDatum_diagonalPeriodForm_eq (D := D)
  exact ⟨Ψ, fun ϑ ↦ (hΨ ϑ).1, α, fun g r hr ϑ y' φ ↦
    (hr.integral_lowerChainUpTo ϑ y' φ).trans ((hΨ ϑ).2 g y' φ)⟩

/-- There are functions `Ψ ϑ`, one for each twist `ϑ`, of tuples `EdgeTuple ϑ`, a real point `g`, a
constant `α` and a map `r` from the forms of level `𝔟` on `Ỹ^m_0` onto the forms on `Y₀` of level
`J_M` as follows.
* `Ψ ϑ` is a path datum (`IsPathDatum`) on the first path: a function of the matrices on its edges,
  invariant up to the edge characters under admissible families of group elements at the nodes, zero
  unless those on twisted edges have left inverses, with values sums of at most
  `edgeMatrixCountBound ϑ ^ (2 * D.m)` roots of unity.
* The pairing of a conjugate form `y'` on `Y_m` with the chain `lowerChainUpTo` of theta lifts of
  `r φ` is `α` times `gridPeriod`: the sum over the tuples `S` on the path of `Ψ ϑ S` times the
  period `diagonalPeriodForm` at `g` of the images of `y'` and `φ` under the transposed lifts with
  the matrices of `S` along the two halves. -/
lemma exists_isPathDatum_first :
    ∃ Ψ : ∀ ϑ : D.MFoldTwist, EdgeTuple ϑ → ℂ,
      (∀ ϑ : D.MFoldTwist,
        IsPathDatum (edgeMatrixCountBound ϑ ^ (2 * D.m)) (TwoGridPath.first D.m).edges (Ψ ϑ)) ∧
      ∃ (g : GInf D.E (D.gridSigns true 0 0 0)) (α : ℂ)
        (r : D.gridLevelForms D.m →ₗ[ℂ] D.principalForms (D.spaceY 0)),
        r.range = ⊤ ∧
        ∀ (ϑ : D.MFoldTwist) (y' : D.GridForm false 0 D.m) (φ : D.gridLevelForms D.m),
          ∫ x, y' x * D.lowerChainUpTo ϑ D.m (r φ) x ∂(D.spaceY D.m).quotMeasure =
            α * gridPeriod (.first D.m) Ψ g (ϑ, y', φ) := by
  obtain ⟨Ψ, hΨ, α, h_period⟩ := D.exists_isPathDatum_integral_eq
  obtain ⟨g, r, hr, h_onto⟩ := D.exists_isFlatRestriction_range_eq_top
  exact ⟨Ψ, hΨ, g, α, r, h_onto, h_period g r hr⟩

end FirstPath

end New.Data
