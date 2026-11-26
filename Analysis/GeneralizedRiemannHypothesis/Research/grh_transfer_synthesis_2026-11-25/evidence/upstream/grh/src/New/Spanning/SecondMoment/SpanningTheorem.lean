import New.Determinant.AuxiliaryForms.RegularParameters
import New.Spanning.MainTerm.BadTypes
import New.Spanning.Multiplicities.EqualMultiplicities
import New.Spanning.Unfolding.Moments
import New.Spanning.Unfolding.SeriesPeriod

/-!
# The dimension of the target and one good translate of the Poincaré map

For admissible data `D`, the finite group `Ḡ = D.chosenGL` acts on the forms on `Y₀`, and `e₀`
projects them onto the target `D.targetForms`, the good forms, of dimension `D.targetDim`. The
source `D.SourceForm` is the space of the forms that the Poincaré map `P = D.poincare` sends to
forms on `Y₀`. This file supplies the hypotheses of the lemma on one translate,
`New.isSpread_of_second_moment`, for `P` and draws its conclusion. The spanning theorem itself,
`New.Data.enough_forms`, is deduced in `New.Reduction.ShortAndEnough`.

## Main definitions and results

* `New.Data.targetDim_le_card_mul_besselDegree_mul_mass`: the target has dimension at most
  `#Ḡ · deg · mass_r`. It is counted on the definite space `D.spaceW D.m`, where the level is free.
* `New.Data.hasAmplitudeBlocks_scaledPoincare`: the blocks of `P* s P`, once `P` is scaled
  (`New.Data.scaledPoincare`).
* `New.Data.bad_types_rare`: `e₀` is a product of two central idempotents, one for each level prime,
  and their complements have a small coefficient at `1`.
* `New.Data.isNearIsometry_e₀_comp_scaledPoincare`,
  `New.Data.targetDim_mul_sum_hilbertSchmidtNorm_sq_le`: the two hypotheses of the lemma on one
  translate.
* `New.Data.isSpread_goodPoincare`: for every space of target forms, with share `α` of the
  dimension, some translate `s e₀ P` has a preimage of dimension at most about `(1 + α) / 2` times
  the dimension of the source.

Notions from other files:
* `New.Data.filling`: the data `New.Filling` attached to `D`: the level `N`, the two level primes
  with their chosen places, and Bessel systems chosen from `New.Data.exists_besselSystem`.
* `New.Filling.besselDegree`: the product `deg` of the formal degrees at the infinite places.
* `New.mass`: the mass `mass_r` of the genus of the standard lattice of rank `r`.
* `New.Data.paramW`: twice the parameter `New.Data.targetParameter`, indexed by the basis of `Y₀`.
* `New.Data.RowIndex`: the index set of the basis of `Y₀`.

## Relation to the literature

For every space `F` of target forms, with share `α` of the dimension, some translate `s e₀ P` has
rank modulo `F` at least nearly `(1 - α) / 2` times the dimension of the source. Spanning by
Poincaré series and the link between least second moment and tight frames are known in the
literature. Related work: Petersson, Über die Entwicklungskoeffizienten der automorphen Formen,
1932; Benedetto–Fickus, Finite normalized tight frames, 2003; Muić, Spectral decomposition of
compactly supported Poincaré series and existence of cusp forms, 2010.
-/

namespace New.Data

variable {P : Parameters} (D : Data P)

/-! ## The dimension of the target -/

section TargetDimension

/-- At every infinite place `v`, the parameter `D.paramW v` decreases along the numbering
`D.basisNumber` of the basis of `Y₀`: exactly `D.basisNumber i` of its entries exceed the entry at
`i` (`decreasingPosition` is the number of larger entries). -/
lemma decreasingPosition_paramW (v : D.Φ) (i : D.RowIndex) :
    decreasingPosition (D.paramW v) i = D.basisNumber i :=
  D.card_filter_basisNumber (q := fun j : D.RowIndex ↦ D.paramW v i < D.paramW v j) 0
    (D.basisNumber i) (by simp [paramW_lt_iff]) (by simp)

/-- The forms of principal level on the definite space `D.spaceW D.m`, where the level is free, have
dimension `#Ḡ · mass_r` times the product over the infinite places of the formal degrees of the
parameter `D.paramW v` for the definite signs. Here `Ḡ = D.chosenGL` and `mass_r = mass D.E D.r`. -/
lemma finrank_principalForms_spaceW :
    (Module.finrank ℂ (D.principalForms (D.spaceW D.m)) : ℝ) =
      Nat.card D.chosenGL * mass D.E D.r * ∏ v : D.Φ, (toHCParam 1 (D.paramW v)).formalDegree := by
  -- These are algebraic forms of a free level, so their dimension is the class number times the
  -- dimension of the weight `(κ, e)`, which is the product of the compact formal degrees.
  obtain ⟨κ, e, h_wt⟩ := Exchange.exists_isHCParam_of_hasGap D.hasGap_signsY_paramW
  have h_free (g : Gf D.E D.RowIndex) :
      classAut (stdSpace D.E D.RowIndex).embFin.range D.chosenLevel g = ⊥ :=
    D.classAut_eq_bot_of_le_chosenLevel le_rfl D.nat_le_of_hasLogBound g
  -- the level has index `Nat.card D.chosenGL` in the maximal one, whose class sum is the mass
  have h_classes :
      classSum (stdSpace D.E D.RowIndex).embFin.range D.chosenLevel 1 =
        (Nat.card D.chosenGL * mass D.E D.r : ℝ) := by
    rw [classSum_one_of_le levelOf_le_stdLevel, relIndex_levelOf, classSum_stdRatPoints_eq_mass,
      Subgroup.index_bot, card_rowIndex]
  calc (Module.finrank ℂ (D.principalForms (D.spaceW D.m)) : ℝ)
      = Module.finrank ℂ (levelSpace (algFormRep (n := D.RowIndex) κ e) D.chosenLevel) :=
        mod_cast (Space.algFormEquiv _ h_wt _).finrank_eq.symm
    _ = _ := by
      rw [finrank_levelSpace_smoothFormRep h_free, Nat.cast_mul, card_classes_eq_classSum h_free,
        h_classes, Module.finrank_pi, ← h_wt.prod_formalDegree]

/-- **Dimension of the target.** For admissible data `D`, the dimension `D.targetDim` of the space
of good forms on `Y₀` is at most `#Ḡ · deg · mass_r`. -/
theorem targetDim_le_card_mul_besselDegree_mul_mass :
    D.targetDim ≤ Nat.card D.chosenGL * D.filling.besselDegree * mass D.E D.r := by
  -- The target has the dimension of the good forms on `D.spaceW D.m`, which are among the forms
  -- of principal level there.
  obtain ⟨κ, e, h_wt⟩ := Exchange.exists_isHCParam_of_hasGap D.hasGap_signsY_paramW
  -- both degrees are given by Weyl's dimension formula
  have h_deg : ∏ v, (toHCParam 1 (D.paramW v)).formalDegree = D.filling.besselDegree := by
    simp [Filling.besselDegree, (D.filling_fits.isDiscreteSeriesBessel _).deg_eq,
      Orbital.harish_chandra_degree_and_orbital, h_wt.hasGap]
  calc (D.targetDim : ℝ)
      = Module.finrank ℂ (D.goodForms (D.spaceW D.m)) :=
        mod_cast D.targetDim_eq_finrank_goodForms_spaceW ⟨D.m, D.nat_le_of_hasLogBound, le_rfl⟩
    _ ≤ Module.finrank ℂ (D.principalForms (D.spaceW D.m)) := mod_cast Submodule.finrank_le _
    _ = Nat.card D.chosenGL * D.filling.besselDegree * mass D.E D.r := by
      rw [D.finrank_principalForms_spaceW, h_deg, mul_right_comm]

end TargetDimension

/-! ## One translate of the Poincaré map -/

section Spreading

open Module Submodule Filling Fintype

/-- The map `#Ḡ · e₀ s P` from all source forms to the target forms. Here `Ḡ = D.chosenGL`, the map
`P = D.poincare` is the unscaled Poincaré map and `e₀ = D.e₀` projects onto the good forms. As `e₀`
is central, it is the translate by `s` of `#Ḡ · e₀ P`. -/
noncomputable def goodPoincare (s : D.chosenGL) : D.SourceForm →ₗ[ℂ] D.targetForms :=
  D.goodProjTranslate s ∘ₗ D.poincare

/-- The action of the finite group `Ḡ` on the forms of principal level, with the chosen places
sorted by the level prime below them. -/
noncomputable def levelRepresentation :
    Representation ℂ D.filling.ResidueGL (D.principalForms (D.spaceY 0)) :=
  .comp (D.principalRep (D.spaceY 0)) (.mk' Sigma.uncurry fun _ _ ↦ rfl)

/-- The representation `D.levelRepresentation` sends an element `s` of `D.filling.ResidueGL`, the
finite group with the chosen places sorted by the level prime below them, to the action under
`D.principalRep (D.spaceY 0)` of its uncurried form `Sigma.uncurry s`. -/
lemma levelRepresentation_apply (s : D.filling.ResidueGL) :
    D.levelRepresentation s = D.principalRep (D.spaceY 0) (Sigma.uncurry s) :=
  rfl

/-- The representation `D.levelRepresentation` is unitary. -/
lemma inner_levelRepresentation (s : D.filling.ResidueGL) (x y : D.principalForms (D.spaceY 0)) :
    inner ℂ (D.levelRepresentation s x) (D.levelRepresentation s y) = inner ℂ x y :=
  Space.inner_formRep ..

/-- The factor `(vol J · ν) ^ (-1/2)` that makes the Poincaré map almost an isometry. Here `J` is
the principal level and `ν` the covolume of its unipotent points. -/
noncomputable def poincareScale : ℝ :=
  √(MeasureTheory.volume.real D.filling.stdPrincipalLevel.carrier * D.filling.unipotentCovolume)⁻¹

/-- The scale of the Poincaré map is positive, as the principal level has positive volume. -/
lemma poincareScale_pos : 0 < D.poincareScale :=
  Real.sqrt_pos.2 (inv_pos.2
    (mul_pos (measureReal_pos_of_isLevel (K := D.chosenLevel)) D.filling.unipotentCovolume_pos))

/-- The Poincaré map times `D.poincareScale`, in the coordinates `D.sourceFormCoords` of the source
forms, whose standard inner product serves as the inner product of the source. -/
noncomputable def scaledPoincare :
    EuclideanSpace ℂ (D.filling.Classes × D.filling.BesselCoord) →ₗ[ℂ]
      D.principalForms (D.spaceY 0) :=
  (D.poincareScale : ℂ) • D.poincare ∘ₗ D.sourceFormCoords.symm.toLinearMap

/-- **Unfolding.** Let `S = D.filling` and let `P = D.scaledPoincare` be the scaled Poincaré map.
Let `s` lie in `S.ResidueGL`, the product of the general linear groups over the residue fields at
the chosen places above each of the two level primes. For classes `c, c'` and Bessel coordinates
`i, j`, with basis vectors `e` of the source, `⟪s P e_(c', j), P e_(c, i)⟫ = ν⁻¹ ∑_γ A_γ(i, j)`. The
sum is over the rational `γ` such that `h_c⁻¹ γ h_c'` is integral with reduction `s` (`S.termsOver`,
where `h_c = S.classRep c`). The amplitude `A_γ = S.amplitude .full c c' γ` is an integral over the
infinite places of `W(y) ⊗ W(γ⁻¹ y)^*` against cutoffs, where `.full` selects the Bessel function
`W` itself and not its cut. The explicit number `ν = S.unipotentCovolume` is the covolume, the same
for all `c`, of the group `S.classUnipotent c` of rational unipotent points in the real unipotent
group. -/
theorem hasAmplitudeBlocks_scaledPoincare :
    D.filling.HasAmplitudeBlocks D.levelRepresentation D.scaledPoincare := by
  have h_series :
      D.poincare ∘ₗ D.sourceFormCoords.symm.toLinearMap = D.filling_fits.poincareMap := by
    rw [D.poincare_eq_poincareMap_comp]
    exact LinearMap.ext fun φ ↦
      congrArg D.filling_fits.poincareMap (D.sourceFormCoords.apply_symm_apply φ)
  rw [scaledPoincare, h_series]
  exact hasAmplitudeBlocks_smul_of_inner_eq (measureReal_pos_of_isLevel (K := D.chosenLevel))
    fun _ ⟨c, i⟩ ⟨c', i'⟩ ↦ D.filling_fits.petersson_poincare c c' i i'
      (reduceFamily_liftResidue (w := D.chosenPlace) _)

open scoped Classical in
/-- The idempotent `e_{p_i}` for the level prime `p_i = D.levelPrime i`: the sum of the
`⊗_w e_{c_w}` over the tuples `c` of allowed polynomials of degree `r` at the chosen places above
`p_i` that have a primitive member. -/
noncomputable def goodIdempotentAbove (i : Fin 2) :
    MonoidAlgebra ℂ (∀ w : D.filling.chosenPlaces i, GL D.RowIndex (ResField w.val)) :=
  ∑ c ∈ goodTuples (P.q₂ D.towerExp) (card D.RowIndex),
    tupleIdem (k := fun w : D.filling.chosenPlaces i ↦ ResField w.val) D.RowIndex c

/-- The element `e_{p_i} = D.goodIdempotentAbove i` is a central idempotent of the group algebra at
the level prime `p_i`. -/
lemma isCentralProj_goodIdempotentAbove (i : Fin 2) : IsCentralProj (D.goodIdempotentAbove i) := by
  classical
  exact isCentralProj_sum_tupleIdem

/-- The tensor product of the two idempotents `D.goodIdempotentAbove i` acts through
`D.levelRepresentation` as the projector `D.e₀` onto the good forms. -/
lemma levelRepresentation_goodIdempotentAbove_eq :
    D.levelRepresentation.asAlgebraHom (piTensorElem D.goodIdempotentAbove) =
      (D.principalRep (D.spaceY 0)).asAlgebraHom D.e₀ := by
  classical
  have : Fintype D.chosenGL := .ofFinite D.chosenGL
  -- Both coefficients are the sum over the families of the products over all chosen places.
  have h_tensor (s : D.filling.ResidueGL) : (piTensorElem D.goodIdempotentAbove).coeff s =
      ∑ c ∈ piFinset fun _ : Fin 2 ↦ goodTuples (P.q₂ D.towerExp) (card D.RowIndex),
        ∏ i : Fin 2, ∏ w : D.filling.chosenPlaces i,
          (labelIdem D.RowIndex (c i w)).coeff (s i w) := by
    simp [goodIdempotentAbove, tupleIdem, Finset.prod_univ_sum]
  have h_proj (t : D.chosenGL) : D.e₀.coeff t =
      ∑ c ∈ piFinset fun _ : Fin 2 ↦ goodTuples (P.q₂ D.towerExp) (card D.RowIndex),
        ∏ i : Fin 2, ∏ w : D.ChosenPlace i,
          (labelIdem D.RowIndex (c i w)).coeff (t ⟨i, w⟩) := by
    simp [e₀, goodTupleFamilies, tupleIdem, prod_sigma, Sigma.uncurry]
  simp_rw [asAlgebraHom_eq_sum]
  refine Fintype.sum_equiv (κ := D.chosenGL) (Equiv.piCurry _).symm _ _ fun s ↦ ?_
  rw [h_tensor, h_proj, levelRepresentation_apply]
  rfl -- the definition of `Sigma.uncurry`

/-- The share of the bad types, those that the idempotent `e_{p_i} = D.goodIdempotentAbove i` kills,
is small at the level prime `p_i = D.levelPrime i`: the coefficient of `1 - e_{p_i}` at the identity
has real part at most `b⁻⁸ / 2`, where `b = D.b` is the weight at the places `D.bPlaces`. -/
lemma re_coeff_one_sub_goodIdempotentAbove_le (i : Fin 2) :
    ((1 - D.goodIdempotentAbove i).coeff 1).re ≤ (D.b ^ 8)⁻¹ / 2 := by
  classical
  -- The share of the bad types is at most `f ε + b⁻⁹`, with `ε = (1 + q₂ + 2 r) / p_i`.
  have h_small : D.f * ((1 + P.q₂ D.towerExp + 2 * card D.RowIndex) / D.levelPrime i) +
      Real.exp (-(9 * D.logB)) ≤ (D.b ^ 8)⁻¹ / 2 := D.le_of_hasLogBound
  have h_one_lt_card : 1 < card D.RowIndex := D.nat_lt_of_hasLogBound
  have h_card_lt_prime : card D.RowIndex < D.levelPrime i := D.nat_lt_of_hasLogBound
  have h_ratio_le_one : (1 + P.q₂ D.towerExp + 2 * card D.RowIndex : ℝ) / D.levelPrime i ≤ 1 :=
    D.le_of_hasLogBound
  have h_le_f : 2 * card D.RowIndex *
      (2 * (card D.RowIndex * Real.log (D.levelPrime i)) + 1) * (9 * D.logB) ≤ (D.f : ℝ) :=
    D.le_of_hasLogBound
  exact (re_coeff_one_sub_sum_tupleIdem_le (q := D.levelPrime i) _ (9 * D.logB)
    (card_resField_eq_levelPrime _ i) rfl
    (card_chosenPlaces _ i) h_one_lt_card h_card_lt_prime h_ratio_le_one le_rfl h_le_f).trans
    h_small

/-- **Bad types are rare.** The two elements `e_{p_i} = D.goodIdempotentAbove i` of the group
algebras at the level primes `p_i` are central idempotents. Their tensor product
`piTensorElem D.goodIdempotentAbove` acts through `D.levelRepresentation` as the projector `D.e₀`
onto the good forms. The share of the bad types, those that `e_{p_i}` kills, is small: the
coefficient of `1 - e_{p_i}` at the identity has real part at most `b⁻⁸ / 2`, where `b = D.b`. -/
theorem bad_types_rare :
    (∀ i : Fin 2, IsCentralProj (D.goodIdempotentAbove i)) ∧
    D.levelRepresentation.asAlgebraHom (piTensorElem D.goodIdempotentAbove) =
      (D.principalRep (D.spaceY 0)).asAlgebraHom D.e₀ ∧
    ∀ i : Fin 2, ((1 - D.goodIdempotentAbove i).coeff 1).re ≤ (D.b ^ 8)⁻¹ / 2 :=
  ⟨D.isCentralProj_goodIdempotentAbove, D.levelRepresentation_goodIdempotentAbove_eq,
    D.re_coeff_one_sub_goodIdempotentAbove_le⟩

/-- **Good forms.** The composite `e₀ P` of the scaled Poincaré map `P = D.scaledPoincare` with the
projector `e₀ = D.e₀` onto the good forms on `Y₀` is almost an isometry in mean square
(`IsNearIsometry`): `‖e₀ P pr_U‖² ≥ dim U - 5 b⁻⁴ D_X` for every subspace `U` of the source. Here
`‖·‖` is the Hilbert–Schmidt norm, `pr_U` the orthogonal projection onto `U`, `b = D.b`, and `D_X`
is the dimension of the source. -/
theorem isNearIsometry_e₀_comp_scaledPoincare :
    IsNearIsometry ((D.principalRep (D.spaceY 0)).asAlgebraHom D.e₀ ∘ₗ D.scaledPoincare)
      (5 * (D.b ^ 4)⁻¹) := by
  obtain ⟨h_central, h_proj_eq, h_bad⟩ := D.bad_types_rare
  rw [← h_proj_eq]
  exact D.hasAmplitudeBlocks_scaledPoincare.isNearIsometry_piTensorElem_comp
    D.inner_levelRepresentation
    h_central h_bad

/-- **Second moment.** For the scaled Poincaré map `P = D.scaledPoincare`, the sum over `s` in
`Ḡ = D.chosenGL` of the squared Hilbert–Schmidt norm `hilbertSchmidtNorm` of `P* s P` is at most
`1 + 9 b⁻⁴` times `D.filling.mainSecondMoment = D_X² / (deg · mass_r)`, where `D_X` is the dimension
of the source. -/
theorem sum_hilbertSchmidtNorm_scaledPoincare_sq_le [Fintype D.chosenGL] :
    ∑ s : D.chosenGL,
        hilbertSchmidtNorm (D.scaledPoincare.adjoint ∘ₗ D.principalRep (D.spaceY 0) s ∘ₗ
          D.scaledPoincare) ^ 2 ≤
      (1 + 9 / D.b ^ 4) * D.filling.mainSecondMoment := by
  -- The bound holds for the group with the chosen places sorted by primes; uncurry the index.
  refine le_of_eq_of_le (Eq.symm ?_)
    (D.hasAmplitudeBlocks_scaledPoincare.sum_hilbertSchmidtNorm_sq_le D.inner_levelRepresentation)
  refine Finset.sum_equiv (κ := D.chosenGL) (Equiv.piCurry _).symm (by simp) fun s _ ↦ ?_
  rw [levelRepresentation_apply]
  -- `congr` compares only the two group elements; a plain `rfl` unfolds the representation.
  congr 4

/-- The second moment with the bound for the dimension of the target: `D.targetDim` times the sum
over `s` in `D.chosenGL` of `‖L* s L‖²` is at most
`#D.chosenGL (1 + 9 / D.b ^ 4) D.filling.sourceDim²`. Here `L = D.scaledPoincare` is the Poincaré
map times `D.poincareScale`, and `L*` is its adjoint. `‖·‖` is the Hilbert–Schmidt norm, `D.b` is
the scale `b` of the data, and `D.filling.sourceDim` is the dimension of the source. -/
lemma targetDim_mul_sum_hilbertSchmidtNorm_sq_le [Fintype D.chosenGL] :
    D.targetDim * ∑ s : D.chosenGL,
        hilbertSchmidtNorm (D.scaledPoincare.adjoint ∘ₗ D.principalRep (D.spaceY 0) s ∘ₗ
          D.scaledPoincare) ^ 2 ≤
      card D.chosenGL * ((1 + 9 / D.b ^ 4) * D.filling.sourceDim ^ 2) := by
  -- The factor `deg · mass_r` in the bound for the dimension cancels the denominator of
  -- `mainSecondMoment = D_X² / (deg · mass_r)`.
  have h_deg : 0 < D.filling.besselDegree := D.filling.besselDegree_pos
  have h_mass : 0 < mass D.E D.r := mass_pos D.E D.r
  calc _ ≤ (Nat.card D.chosenGL * D.filling.besselDegree * mass D.E D.r) *
        ((1 + 9 / D.b ^ 4) * D.filling.mainSecondMoment) :=
      mul_le_mul D.targetDim_le_card_mul_besselDegree_mul_mass
        D.sum_hilbertSchmidtNorm_scaledPoincare_sq_le (by positivity) (by positivity)
    _ = _ := by
      rw [mainSecondMoment, Shape.r, card_rowIndex, Nat.card_eq_fintype_card]
      field

/-- The target is not zero, as the almost isometry `e₀ P` from the source has a range of positive
dimension. -/
lemma finrank_targetForms_ne_zero : finrank ℂ D.targetForms ≠ 0 :=
  (D.isNearIsometry_e₀_comp_scaledPoincare.finrank_range_pos D.lt_of_hasLogBound).ne'

/-- Let `s` lie in the finite group `D.chosenGL`, let `e₀ = D.e₀` be the projector onto the target
forms and let `P = D.scaledPoincare` be the scaled Poincaré map. A space `F` of target forms has the
same preimage under `e₀ s P` as under `D.goodPoincare s` read in the coordinates
`D.sourceFormCoords` of the source: the two maps differ only by nonzero factors. -/
lemma comap_scaledPoincare_eq_comap_goodPoincare (s : D.chosenGL) (F : Submodule ℂ D.targetForms) :
    F.comap (((D.principalRep (D.spaceY 0)).asAlgebraHom D.e₀).rangeRestrict ∘ₗ
        D.principalRep (D.spaceY 0) s ∘ₗ D.scaledPoincare) =
      (F.comap (D.goodPoincare s)).comap D.sourceFormCoords.symm.toLinearMap := by
  have h_scale : (D.poincareScale : ℂ) ≠ 0 := mod_cast D.poincareScale_pos.ne'
  have h_card : (Nat.card D.chosenGL : ℂ) ≠ 0 := mod_cast Nat.card_pos.ne'
  ext φ
  set e := ((D.principalRep (D.spaceY 0)).asAlgebraHom D.e₀).rangeRestrict
  let y : D.targetForms := e (D.principalRep (D.spaceY 0) s
    (D.poincare (D.sourceFormCoords.symm φ)))
  have h_scaled : (e ∘ₗ D.principalRep (D.spaceY 0) s ∘ₗ D.scaledPoincare) φ =
      (D.poincareScale : ℂ) • y := by
    rw [scaledPoincare, LinearMap.comp_smul, LinearMap.comp_smul]
    rfl
  -- by definition `D.goodPoincare s` takes the value `#Ḡ • y` here
  change _ ∈ F ↔ (Nat.card D.chosenGL : ℂ) • y ∈ F
  rw [h_scaled, F.smul_mem_iff h_scale, F.smul_mem_iff h_card]

/-- **One translate.** For `s` in the finite group `Ḡ = D.chosenGL`, the map `D.goodPoincare s` is
`#Ḡ · e₀ s Π`: the unscaled Poincaré map `Π = D.poincare` from the source forms `D.SourceForm` to
the forms on `Y₀`, then the translation by `s`, then the projector `e₀ = D.e₀` onto the target
forms. These maps spread (`IsSpread`): for every space `F` of target forms, with share `α` of the
dimension of the target, the preimage of `F` under one of them has dimension at most
`(1 + α + 3 ε₀) / 2 · D_X`, where `ε₀ = b⁻² / 8`. Here `b = D.b` is the weight at the places
`D.bPlaces`, and `D_X` is the dimension of `D.SourceForm`. -/
theorem isSpread_goodPoincare : IsSpread D.goodPoincare (3 / 2 * (8 * D.b ^ 2)⁻¹) := by
  have : Fintype D.chosenGL := .ofFinite D.chosenGL
  let ρ : Representation ℂ D.chosenGL (D.principalForms (D.spaceY 0)) := D.principalRep (D.spaceY 0)
  have h_unitary (s : D.chosenGL) (x y : D.principalForms (D.spaceY 0)) :
      inner ℂ (ρ s x) (ρ s y) = inner ℂ x y := Space.inner_formRep ..
  have h_comm (s : D.chosenGL) : Commute (ρ.asAlgebraHom D.e₀) (ρ s) := by
    simpa using ((D.isCentralProj_e₀.2.commute (.single s 1)).map ρ.asAlgebraHom).symm
  -- The two hypotheses of the lemma on one translate, for the scaled map and `ε₀ = b⁻² / 8`.
  have h_isom : IsNearIsometry (ρ.asAlgebraHom D.e₀ ∘ₗ D.scaledPoincare) (8 * D.b ^ 2)⁻¹ :=
    D.isNearIsometry_e₀_comp_scaledPoincare.mono D.le_of_hasLogBound
  have h_moment : finrank ℂ (ρ.asAlgebraHom D.e₀).range *
      ∑ s : D.chosenGL,
        hilbertSchmidtNorm (D.scaledPoincare.adjoint ∘ₗ ρ s ∘ₗ D.scaledPoincare) ^ 2 ≤
      card D.chosenGL * ((1 + (8 * D.b ^ 2)⁻¹) *
        finrank ℂ (EuclideanSpace ℂ (D.filling.Classes × D.filling.BesselCoord)) ^ 2) := by
    have h_error : 9 / D.b ^ 4 ≤ (8 * D.b ^ 2)⁻¹ := D.le_of_hasLogBound
    grw [finrank_source_eq_sourceDim, ← h_error]
    exact D.targetDim_mul_sum_hilbertSchmidtNorm_sq_le
  -- Neither the coordinates nor the nonzero factors change the dimension of a preimage.
  intro F α
  obtain ⟨s, hs⟩ := isSpread_of_second_moment h_unitary
    (D.isCentralProj_e₀.isSymmetricProjection h_unitary) h_comm (by positivity) h_isom h_moment F
  refine ⟨s, ?_⟩
  rwa [D.comap_scaledPoincare_eq_comap_goodPoincare s F,
    (D.sourceFormCoords.symm.ofSubmodule' _).finrank_eq,
    ← D.sourceFormCoords.finrank_eq] at hs

end Spreading

end New.Data
