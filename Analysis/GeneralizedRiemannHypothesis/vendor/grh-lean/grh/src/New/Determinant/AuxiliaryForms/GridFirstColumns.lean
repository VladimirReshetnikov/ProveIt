import New.Determinant.AuxiliaryForms.PathData
import New.Determinant.Chain.Moduli
import New.OneLift.ComparisonOperator.GluedLattices
import New.UpperBound.Seesaw.LevelIdeles

/-!
# Periods on the diagonal and path data on the first path

The first path goes from `Ỹ^m_0` to `Ỹ^0_0 = Y₀ ⊕ E ẽ₀` and from `Y₀` to `Y_m`. Its spaces are the
nodes `(z, 0, i)`, the first columns of the two grids: `(false, 0, i)` is `Y_i` and `(true, 0, i)`
is `Ỹ^i_0`. A form on `Ỹ^m_0` and a conjugate form on `Y_m` move down these columns by transposed
lifts and meet at `i = 0`. The product `Ψ¹` of the point data of the edges computes the period of
the two iterated transposed lifts `New.Data.transposedChain`. The sum `Ψ⁰` of the translates of
`Ψ¹`, weighted by the characters of the edges, is a path datum, and its period is the number of
translates times that of `Ψ¹`.

## Main definitions and results

* `New.Data.exists_petersson_eq_diagonalPeriodForm`: the period with a form on `Ỹ^0_0`, as a
  functional of the form on `Y₀`, is a Petersson product.
* `New.Data.diagonalPeriodForm_tupleAction`: translating the matrices by a family that is `1` at
  the ends and `diag(g, 1)` at `(0, 0)` of the `Ỹ`, `g` being its member at `(0, 0)` of the `Y`,
  multiplies the period by the characters of the edges.
* `New.Data.firstPointDatum`, `New.Data.firstPathDatum`: the functions `Ψ¹` and `Ψ⁰`.
* `New.Data.exists_isPathDatum_diagonalPeriodForm_eq`: the period of the iterated transposed lifts
  is a constant times the period of path data on the first path.

Notions from other files:
* `New.Data.triangleModulus`: the modulus `𝔪₀ = π_M Q` for the chain of the `Y` and `𝔟 = π_M ^ b`
  for that of the `Ỹ`, with `π_M = D.piM`. `New.Data.gridModulus` is `𝔪 = 𝔟Q`, where `Q` comes
  from the twist `ϑ`. `New.Data.triangleGLCard` is the index `n_𝔪₀(Y_i)` or `n_𝔟(Ỹ^i_0)`.
* `New.Data.levelIndex`: the index of the level `New.Data.nodeLevel` at a node, which is the level
  `𝔪` at the `Y_i` and the level `𝔟` elsewhere.
* `New.Data.diagonalPeriodForm`: the period of a conjugate form on `Y^j_j` and a form on `Ỹ^j_j`
  along the embedding of unitary groups, shifted on the line by a scalar from the twist, at a real
  point.
* `New.Data.EdgeTuple`: a matrix modulo `𝔪` for each pair of nodes. A `NodeFamily` of invertible
  matrices acts on it by `New.Data.tupleAction`; `New.Data.edgeCharProd` is the product of the
  characters of the edges at the determinants of such a family.
* `New.GridPath.formMap`: the composite of the maps by the matrices of a tuple along a path.
-/

noncomputable section

namespace New.Data

/-!
## Periods on the diagonal and translates along the first column

The period of a conjugate form on `Y^j_j` and a form on `Ỹ^j_j` does not see a common translation.
-/
section GridStart

open Function Matrix Fintype Finset Exchange Rows Ideal Quotient Space Gf LevelPlaces

variable {P : Parameters}

/-- The mean of the indicator of the invertible matrices over a finite ring is the share of
invertible matrices. -/
lemma finMean_isUnit_indicator {n R : Type} [Fintype n] [DecidableEq n] [CommRing R] [Fintype R]
    [DecidablePred fun x : Matrix n n R ↦ IsUnit x] [Fintype (GL n R)] :
    finMean (fun x : Matrix n n R ↦ if IsUnit x then (1 : ℂ) else 0) =
      card (GL n R) / card R ^ card n ^ 2 := by
  simp [finMean, card_congr of.symm, sq, pow_mul, ↓finsum_eq_sum_of_fintype,
    (card_congr (.ofInjective _ Units.val_injective)).trans (card_subtype IsUnit)]

/-- The edges of a first column in the two grids are disjoint. -/
lemma disjoint_edges_column {D : Data P} {b : ℕ} (hb : b ≤ D.m) :
    Disjoint ((GridPath.column hb).edges false) ((GridPath.column hb).edges true) := by
  rw [disjoint_left]
  rintro ⟨u, v⟩ h_false h_true
  have hu_false : u.1 = false := (GridPath.eq_and_le_of_mem_edges h_false).1
  have hu_true : u.1 = true := (GridPath.eq_and_le_of_mem_edges h_true).1
  simp [hu_false] at hu_true

/-- Reduction modulo `𝔪₀ = π_M Q` from the residue ring of `𝔪 = 𝔟Q` (`reduceToTriangle ϑ false`, for
the grid of the `Y`) is a local homomorphism, because the two moduli have the same primes. -/
instance (D : Data P) (ϑ : D.MFoldTwist) : IsLocalHom (reduceToTriangle ϑ false) where
  -- A unit modulo an ideal `I` is a unit modulo `I ^ D.natB`, which lies in the ideal of `𝔪`.
  map_nonunit := Quot.ind fun _ h ↦
    ((isUnit_mk_pow_iff_isUnit_mk _ (NeZero.ne D.natB)).2 h).map
      (factor (by simp [levelModulus, mul_pow, mul_mono, pow_le_self NeZero.out]))

/-- Let `π_M = D.piM`, let `Q` be the product of the places of a twist `ϑ`, and put `𝔪₀ = π_M Q` and
`𝔪 = π_M ^ D.natB * Q` (`gridModulus ϑ`). For the space `Y_j` at the node `(false, 0, j)`, the order
`triangleGLCard false ϑ j` of `GL(Y_j)` modulo `𝔪₀` is a number `C`, the same for all `ϑ`, times
`levelIndex ϑ false 0 j`. -/
lemma exists_triangleGLCard_eq_mul_levelIndex (D : Data P) (j : ℕ) :
    ∃ C : ℂ, ∀ ϑ : D.MFoldTwist, D.triangleGLCard false ϑ j = C * levelIndex ϑ false 0 j := by
  -- Both sides count invertible matrices, the left one modulo `𝔪₀` and the right one modulo `𝔪`.
  refine ⟨(card (D.triangleModulus false 1).ResidueRing / card (D.gridModulus 1).ResidueRing) ^
    card (D.Y j) ^ 2, fun ϑ ↦ ?_⟩
  let R₀ : Type := (D.triangleModulus false ϑ).ResidueRing
  let R : Type := (gridModulus ϑ).ResidueRing
  -- The level at `Y_j` is trivial by definition.
  have h_index : levelIndex ϑ false 0 j = card (GL (D.Y j) R) :=
    congrArg Nat.cast (Subgroup.index_bot.trans Nat.card_eq_fintype_card)
  -- The reduction from `𝔪` to `𝔪₀` is onto and local, so it keeps the share of invertible
  -- matrices, which is the mean of their indicator.
  have h_share : (D.triangleGLCard false ϑ j : ℂ) / card R₀ ^ card (D.Y j) ^ 2 =
      card (GL (D.Y j) R) / card R ^ card (D.Y j) ^ 2 := by
    let π := (reduceToTriangle ϑ false).mapMatrix (m := D.Y j)
    have h_surj : Surjective (reduceToTriangle ϑ false) := factor_surjective _
    have h_unit (x : Matrix (D.Y j) (D.Y j) R) : IsUnit (π x) ↔ IsUnit x := by
      simp [π, isUnit_iff_isUnit_det, ← RingHom.map_det, -RingHom.mapMatrix_apply]
    calc _ = finMean fun x ↦ if IsUnit (π x) then (1 : ℂ) else 0 :=
        finMean_isUnit_indicator.symm.trans (finMean_comp_surjective π.toAddMonoidHom
          h_surj.comp_left.comp_left fun x ↦ if IsUnit x then 1 else 0).symm
      _ = _ := by simpa only [h_unit] using finMean_isUnit_indicator
  -- In the ratio of the norms of `𝔪₀` and `𝔪` the factor from the primes of `ϑ` cancels.
  have h_ratio : (card (D.triangleModulus false 1).ResidueRing / card
    (D.gridModulus 1).ResidueRing : ℂ) =
      card R₀ / card R := by simp [R₀, R, card_residueRing_twistModulus, mul_div_mul_right,
        prod_eq_zero_iff]
  rw [h_index, h_ratio, div_pow, div_mul_comm, ← h_share, div_mul_cancel₀ _ (by simp)]

/-- The period of a conjugate form `y` on `Y^j_j` (grid `false`) and a form `φ` on `Ỹ^j_j` (grid
`true`) at the real point `g` does not change when `y` is translated by a finite adelic point `u` of
the unitary group and `φ` by the block matrix `diag(u, 1)`. -/
lemma diagonalPeriodForm_formRep (D : Data P) (ϑ : D.MFoldTwist) {j : ℕ} {hj : j ≤ D.m}
    {g : GInf D.E (D.gridSigns true 0 j j)} (u : Gf D.E (D.GridIndex false j j))
    (y : D.GridForm false j j) (φ : D.GridForm true j j) :
    diagonalPeriodForm ϑ hj g
        ((D.gridSpace 0 false j j).formRep (D.gridKernel false j j true) u y)
        ((D.gridSpace 0 true j j).formRep (D.gridKernel true j j true)
          (U.block (D.gridDiagEquiv j) (u, 1)) φ) =
      diagonalPeriodForm ϑ hj g y φ := by
  -- Both periods are integrals of `F`, the left one translated by `u`; `F` is invariant under the
  -- rational points, so its integral does not change.
  let ι (x : New.G D.E (D.gridSigns false 0 j j)) : New.G D.E (D.gridSigns true 0 j j) :=
    .reindex (D.gridDiagEquiv j) (D.sumElim_gridSigns_comp_gridDiagEquiv_symm hj)
      (.sum (x, 1, (gridModulus ϑ).flipScalar ^ j))
  let F (x : New.G D.E (D.gridSigns false 0 j j)) : ℂ := y.1 x * φ.1 (ι x * (g, 1))
  have h_rat : (gridSpace 0 false j j).Γ.FixesLeft F := fun γ hγ x ↦ by
    let γ' : New.G D.E (D.gridSigns true 0 j j) :=
      .reindex (D.gridDiagEquiv j) (D.sumElim_gridSigns_comp_gridDiagEquiv_symm hj) (.sum (γ, 1))
    -- Membership in `Γ` is rationality; the block sum with `1` keeps it.
    have hγ' : γ' ∈ (gridSpace 0 true j j).Γ := by
      simp_all [γ', gridSpace_diag hj, mem_Gamma_iff_range, Space.reindex, Space.sum, ← map_inv,
        reindex_equiv (D.gridDiagEquiv j), -coe_units_inv, -RingHom.mem_range, fromBlocks_multiply]
    have h_mul : ι (γ * x) = γ' * ι x := by simp [ι, γ', ← map_mul]
    simp only [F, h_mul, mul_assoc, y.2.rat_mul _ hγ, φ.2.rat_mul _ hγ']
  have h_cont : Continuous F := y.2.continuous.mul (φ.2.continuous.comp (by fun_prop))
  have h_int (y : D.GridForm false j j) (φ : D.GridForm true j j) : diagonalPeriodForm ϑ hj g y φ =
      ∫ x, y.1 x * φ.1 (ι x * (g, 1)) ∂(D.gridSpace 0 false j j).quotMeasure := by
    simp [periodPairing, ι]
  have h_mul (x) : ι (x * (1, u)) = ι x * (1, U.block (D.gridDiagEquiv j) (u, 1)) := by
    refine Prod.ext ?_ ?_
    · simp [ι, Prod.mul_def]
      rfl
    · refine .trans ?_ ((U.block _).map_mul (x.2, (gridModulus ϑ).flipScalar Unit ^ j) (u, 1))
      simp
      rfl
  rw [h_int, h_int, ← (integral_comp_mul_right u h_rat h_cont).1]
  simp only [F, h_mul] -- before `Prod.mul_def` takes the product in `h_mul` apart
  simp [Prod.mul_def]

/-- Let `𝔟` be `D.gridLevelGen = D.piM ^ D.natB`. A form `φ` in `D.gridLevelForms 0`, that is of
level `𝔟` on `Ỹ^0_0`, is fixed under `formRep` by the block matrix
`U.block (D.gridDiagEquiv 0) (u, 1)`, written `diag(u, 1)`, for every `u` on `Y₀` in
`principalLevel` of `𝔟`. -/
lemma formRep_block_one_eq_self (D : Data P) (φ : D.gridLevelForms 0)
    {u : Gf D.E (D.GridIndex false 0 0)}
    (hu : u ∈ principalLevel (D.GridIndex false 0 0) D.gridLevelGen) :
    (D.gridSpace 0 true 0 0).formRep (D.gridKernel true 0 0 true)
      (U.block (D.gridDiagEquiv 0) (u, 1)) φ.val = φ.val := by
  have h_mem : U.block (D.gridDiagEquiv 0) (u, 1) ∈
      principalLevel (D.GridIndex true 0 0) D.gridLevelGen := by
    obtain ⟨hu_Kf, hu_entry⟩ := hu
    refine ⟨by simp_all [mem_stdLevel, reindex_equiv (D.gridDiagEquiv 0), Matrix.one_apply],
      (D.gridDiagEquiv 0).surjective.forall₂.2 ?_⟩
    -- Off the block of `u` the entries are those of the identity, so there the witness is `0`.
    rintro (i | i) (j | j) <;> simp_all [Matrix.one_apply]
    all_goals exact ⟨0, by simp⟩
  exact (φ.2 ⟨_, h_mem⟩).trans (one_smul ℂ φ.1)

/-- At the node `Y^0_0` of grid `Y`, the kernel `gridKernel false 0 0 true`, that of the conjugate
forms `GridForm false 0 0`, is the complex conjugate (`star`) of `gridKernel false 0 0 false`, the
kernel of the forms on `Y^0_0`. -/
lemma gridKernel_zero_true_eq_star (D : Data P) :
    D.gridKernel false 0 0 true = star (D.gridKernel false 0 0 false) :=
  (isConjKernelPair_gridKernel ⟨D.m.zero_le, D.m.zero_le⟩ false).right

/-- The period with a form `φ` on `Ỹ^0_0`, as a functional of the forms `y` on `Y₀`, is a Petersson
product. The chosen places are the prime divisors of `π_M = D.piM`, and `J_M = D.chosenLevel` is the
group of integral points that reduce to `1` at them. The family `(D.levelPlaces ϑ).placeAt` adds the
places of the modulus `Q` of a twist `ϑ`, so its level `levelOf … ⊥` is the level `𝔪₀ = π_M Q`. The
space `gridLevelForms 0` consists of the forms on `Ỹ^0_0` of principal level `𝔟 = π_M ^ D.natB`. At
a real point `g` there is a linear map `periodRepr` from it to the forms on `Y₀` of level `J_M` such
that, for every `ϑ` and every form `y` on `Y₀` of level `𝔪₀`, the Petersson product of `y` and
`periodRepr φ` is the period at `g` of the conjugate of `y` and `φ`. -/
lemma exists_petersson_eq_diagonalPeriodForm (D : Data P)
    (g : GInf D.E (D.gridSigns true 0 0 0)) :
    ∃ periodRepr : D.gridLevelForms 0 →ₗ[ℂ]
        levelSpace ((D.gridSpace 0 false 0 0).formRep (D.gridKernel false 0 0 false)) D.chosenLevel,
      ∀ (φ : D.gridLevelForms 0) (ϑ : D.MFoldTwist),
        ∀ y ∈ levelSpace ((D.gridSpace 0 false 0 0).formRep (D.gridKernel false 0 0 false))
          (levelOf (D.levelPlaces ϑ).placeAt ⊥),
        (D.gridSpace 0 false 0 0).petersson y (periodRepr φ) =
          diagonalPeriodForm ϑ zero_le g (conjForm D.gridKernel_zero_true_eq_star y) φ := by
  -- `periodRepr φ` represents the functional `conjPeriod φ`, the conjugate of the period, on the
  -- finite-dimensional space of forms of level `J_M`. For `y` of level `𝔪₀`, translation by `J_M`
  -- changes neither side of the identity, so `y` may be replaced by its mean over `J_M`.
  let ρ := (D.gridSpace 0 false 0 0).formRep (D.gridKernel false 0 0 false)
  have he_cusp : IsCuspKernel 0 (D.gridKernel false 0 0 false) :=
    (isConjKernelPair_gridKernel ⟨D.m.zero_le, D.m.zero_le⟩ false).left
  have he_star : D.gridKernel false 0 0 true = star (D.gridKernel false 0 0 false) :=
    D.gridKernel_zero_true_eq_star
  have : IsSmoothRep ρ := ⟨fun y ↦ by
    obtain ⟨K, hK⟩ := y.2.exists_level
    filter_upwards [K.mem_nhds_one] with k hk using Subtype.ext (funext (hK k hk))⟩
  have : Module.Finite ℂ (levelSpace ρ D.chosenLevel) :=
    finite_levelSpace he_cusp ⟨D.chosenLevel, isOpen_levelOf⟩
  let conjPeriod := (diagonalPeriodForm 1 zero_le g ∘ₛₗ conjForm he_star).flip.compr₂ₛₗ
    (starLinearEquiv ℂ).toLinearMap
  have conjPeriod_apply (φ : D.GridForm true 0 0) (y) :
      conjPeriod φ y = star (diagonalPeriodForm 1 zero_le g (conjForm he_star y) φ) := rfl
  let periodRepr : D.gridLevelForms 0 →ₗ[ℂ] levelSpace ρ D.chosenLevel :=
    LinearMap.applyₗ 1 ∘ₗ LinearMap.adjoint.toLinearMap ∘ₛₗ
      conjPeriod.domRestrict₁₂ (D.gridLevelForms 0) (levelSpace ρ D.chosenLevel)
  -- `periodRepr φ` is the value at `1` of the adjoint of the functional `conjPeriod φ`.
  have h_repr (φ : D.gridLevelForms 0) (y : levelSpace ρ D.chosenLevel) :
      innerₛₗ ℂ (periodRepr φ).1 y = conjPeriod φ y := by
    simpa [-diagonalPeriodForm] using!
      ((conjPeriod φ).domRestrict (levelSpace ρ D.chosenLevel)).adjoint_inner_left y 1
  refine ⟨periodRepr, fun φ ϑ y hy ↦ star_injective ?_⟩
  have h_petersson (u : Gf D.E (D.GridIndex false 0 0)) (hu : u ∈ D.chosenLevel) :
      innerₛₗ ℂ (periodRepr φ).1 (ρ u y) =
        star ((D.gridSpace 0 false 0 0).petersson y (periodRepr φ)) := by
    have h_fix : ρ u (periodRepr φ).1 = (periodRepr φ).1 :=
      ((periodRepr φ).2 ⟨u, hu⟩).trans (one_smul ℂ (periodRepr φ).1)
    simpa [ρ, h_fix] using! inner_formRep u (periodRepr φ).1 y
  -- Translation by `J_M` does not change the period of the conjugate of `y` and `φ`.
  have h_period (u : Gf D.E (D.GridIndex false 0 0)) (hu : u ∈ D.chosenLevel) :
      conjPeriod φ (ρ u y) = star (diagonalPeriodForm ϑ zero_le g (conjForm he_star y) φ) := by
    lift u to stdLevel D.E (D.GridIndex false 0 0) using levelOf_le_stdLevel hu
    -- Take `v` supported on the places of `𝔟` and their conjugates, with `u * v` of level `𝔟`.
    -- Then `v` lies in `J_M` and is trivial at the places of `ϑ`, so it has level `𝔪₀` and fixes
    -- `y`, and `(u * v, 1)` fixes `φ`.
    obtain ⟨v, hv_supp, hv_red⟩ := exists_reductionGL_eq ((D.gridModulus 1).reductionGL u)⁻¹
    have huv : (u * v).1 ∈ principalLevel (D.GridIndex false 0 0) D.gridLevelGen :=
      (Modulus.mem_principalLevel_iff gridModulus_one_ideal (u * v)).2 (by simp [hv_red])
    have hv_chosen : v.1 ∈ D.chosenLevel := (D.chosenLevel.mul_mem_cancel_left hu).1
      (D.principalLevel_le_chosenLevel piM_dvd_gridLevelGen huv)
    have hv : v.1 ∈ levelOf (D.levelPlaces ϑ).placeAt ⊥ := by
      refine D.chosenLevel_inf_trivialOn_le ϑ ⟨hv_chosen, ?_⟩
      -- At the primes of `ϑ` it is trivial: they are none of those on which it is supported.
      simp_all [places_twistModulus, IsChosen, mem_supportedOn.1 hv_supp,
        toAutChar_one_and_toTwist_one_and_Q_one,
        normQ_mem_and_notMem_of_mem_Q _ ϑ.1.1]
    calc conjPeriod φ (ρ u y)
      _ = star (diagonalPeriodForm ϑ zero_le g ((D.gridSpace 0 false 0 0).formRep
            (D.gridKernel false 0 0 true) (u * v).1 (conjForm he_star y)) φ) := by
        simp [conjPeriod_apply, ρ, periodPairing, ← mem_levelSpace_formRep_iff.1 hy v hv (_ * u.1)]
      _ = _ := by rw [← diagonalPeriodForm_formRep D ϑ (u * v).1 (conjForm he_star y),
        formRep_block_one_eq_self D φ huv]
  calc
    _ = innerₛₗ ℂ (periodRepr φ).1 (compactMean ρ D.chosenLevel y) :=
      (map_compactMean_of_const _ h_petersson).symm
    _ = conjPeriod φ (compactMean ρ D.chosenLevel y) := h_repr φ ⟨_, compactMean_mem_levelSpace y⟩
    _ = _ := map_compactMean_of_const _ h_period

/-- Put `m = D.m` and `𝔪 = gridModulus ϑ`. Let `S` be a tuple of matrices modulo `𝔪`, one for each
pair of nodes, and `F` a form at the end `(z, 0, m)` of the first column. Let the family `g` of
invertible matrices modulo `𝔪` be `1` at that end, and let `k` be an integral lift of `g (z, 0, b)`,
equal to `1` if `b = m`. Translate `S` by `g`, map `F` down the column to `(z, 0, b)` by `formMap`,
and translate the image on the right by `k`. The result is the image of `F` for `S` times
`edgeCharProd g`, the product over the edges from `p` to `q` of the column of their characters at
`det (g q) / det (g p)`. -/
lemma formRep_formMap_column_tupleAction {D : Data P} {ϑ : D.MFoldTwist} {g : NodeFamily ϑ}
    {z : Bool} {b : ℕ} (hb : b ≤ D.m)
    (hg_end : g (z, 0, D.m) = 1) (S : EdgeTuple ϑ) (F : D.GridForm z 0 D.m)
    (k : stdLevel D.E (D.NodeIndex (z, 0, b))) (hk : g (z, 0, b) = (gridModulus ϑ).reductionGL k)
    (hk_end : b = D.m → k = 1) :
    (D.gridSpace 0 z 0 b).formRep (D.gridKernel z 0 b true) k.val
        ((GridPath.column hb).formMap (tupleAction g S) z F) =
      edgeCharProd g ((GridPath.column hb).edges z) • (GridPath.column hb).formMap S z F := by
  -- Downward induction on `b`: across the edge from `(0, b)` to `(0, b + 1)` the translation by
  -- `k` becomes one by a lift `u` of `g (z, 0, b + 1)`, at the price of the character of the edge.
  induction hb using Nat.decreasingInduction with
  | self => simp [GridPath.column_self, GridPath.formMap, GridPath.edges, edgeCharProd, hk_end rfl]
  | of_succ b hb ih =>
    let u : stdLevel D.E (D.NodeIndex (z, 0, b + 1)) :=
      if b + 1 = D.m then 1 else Rows.liftMod (g (z, 0, b + 1))
    have hu : g (z, 0, b + 1) = (gridModulus ϑ).reductionGL u := by grind [reductionGL_liftMod]
    have h_edge (x : D.GridForm z 0 (b + 1)) :
        (D.gridSpace 0 z 0 b).formRep (D.gridKernel z 0 b true) k.1
            (transposedMove (tupleAction g S (columnEdge z 0 b)) x) =
          edgeCharProd g {columnEdge z 0 b} • transposedMove (S (columnEdge z 0 b))
            ((D.gridSpace 0 z 0 (b + 1)).formRep (D.gridKernel z 0 (b + 1) true) u.1 x) := by
      simp only [tupleAction, hk, hu]
      -- The Weil representation moves the translations from the matrix to the two forms.
      refine ((D.isEdgeFamily_grid_succ_right (z := z) id zero_le hb).isArrow_modDatum.2
        |>.formRep_formLift_of_eq_smul (pairWeil_modDatum_single k u) _).trans ?_
      simp [gridChar_det, edgeCharProd, edgeChar, hk, hu, div_eq_mul_inv]
      rfl -- Both sides are the transposed lift that defines `transposedMove`.
    have he : columnEdge z 0 b ∉ (GridPath.column hb).edges z := by
      intro h_mem
      obtain ⟨-, -, h_le, -⟩ := GridPath.eq_and_le_of_mem_edges h_mem
      simp at h_le
    simp only [GridPath.column_of_lt hb, GridPath.formMap, GridPath.edges, LinearMap.comp_apply]
    rw [h_edge, ih u hu (ite_eq_left ·), map_smul, smul_smul]
    simp [edgeCharProd, prod_insert he]

/-- Let `g` be a family of invertible matrices modulo `gridModulus ϑ`, one at each node, that is `1`
at the ends `(z, 0, D.m)` of both first columns and is the block matrix `diag(g (false, 0, 0), 1)`
at `(true, 0, 0)`. Map a conjugate form `y'` on `Y_m` and a form `φ` on `Ỹ^m_0` down these columns
by the matrices `S`, and take the period at the real point `gInf`. Replacing the matrix from `p` to
`q` by `(g q)⁻¹ * S (p, q) * g p` multiplies this period by `edgeCharProd`, the product over the
edges of both columns of their characters at `det (g q) / det (g p)`. -/
lemma diagonalPeriodForm_tupleAction {D : Data P} {ϑ : D.MFoldTwist} {g : NodeFamily ϑ}
    (hg_end : ∀ z : Bool, g (z, 0, D.m) = 1)
    (hg_diag : g (true, 0, 0) = blockInlGL (D.gridDiagEquiv 0) (g (false, 0, 0)))
    (gInf : GInf D.E (D.gridSigns true 0 0 0)) (y' : D.GridForm false 0 D.m)
    (φ : D.GridForm true 0 D.m) (S : EdgeTuple ϑ) :
    diagonalPeriodForm ϑ zero_le gInf
        ((GridPath.column D.m.zero_le).formMap (tupleAction g S) false y')
        ((GridPath.column D.m.zero_le).formMap (tupleAction g S) true φ) =
      edgeCharProd g (TwoGridPath.first D.m).edges * diagonalPeriodForm ϑ zero_le gInf
        ((GridPath.column D.m.zero_le).formMap S false y')
        ((GridPath.column D.m.zero_le).formMap S true φ) := by
  -- A lift `u` of `g (false, 0, 0)` translates both forms, and the period does not see it.
  let u : stdLevel D.E (D.NodeIndex (false, 0, 0)) := Rows.liftMod (g (false, 0, 0))
  have hu : (gridModulus ϑ).reductionGL u = g (false, 0, 0) := reductionGL_liftMod _
  obtain ⟨h_block, h_red⟩ := map_block_eq_blockGL (gridModulus ϑ).reduction (D.gridDiagEquiv 0) u 1
  let u' : stdLevel D.E (D.NodeIndex (true, 0, 0)) :=
    ⟨U.block (D.gridDiagEquiv 0) (u.1, 1), h_block⟩
  have hu' : g (true, 0, 0) = (gridModulus ϑ).reductionGL u' := by
    refine hg_diag.trans (.trans ?_ h_red.symm)
    simp [← hu, Modulus.reductionGL]
  have hm : 0 ≠ D.m := by simp [m_eq_two_mul_varrho_add_two]
  let p : GridPath 0 D.m 0 0 := .column D.m.zero_le
  have h_char : edgeCharProd g (TwoGridPath.first D.m).edges =
      edgeCharProd g (p.edges false) * edgeCharProd g (p.edges true) :=
    prod_union (disjoint_edges_column _)
  have h_false : (D.gridSpace 0 false 0 0).formRep (D.gridKernel false 0 0 true) u.1
        (p.formMap (tupleAction g S) false y') =
      edgeCharProd g (p.edges false) • p.formMap S false y' :=
    formRep_formMap_column_tupleAction _ (hg_end false) S y' u hu.symm (absurd · hm)
  have h_true : (D.gridSpace 0 true 0 0).formRep (D.gridKernel true 0 0 true) u'.1
        (p.formMap (tupleAction g S) true φ) =
      edgeCharProd g (p.edges true) • p.formMap S true φ :=
    formRep_formMap_column_tupleAction _ (hg_end true) S φ u' hu' (absurd · hm)
  -- `erw`: the index set of the node `(z, 0, 0)` is `D.GridIndex z 0 0` only by definition.
  erw [← diagonalPeriodForm_formRep D ϑ u.1, h_false, h_true]
  rw [h_char, LinearMap.map_smul₂, map_smul, smul_smul, smul_eq_mul]

end GridStart

/-!
## Path data on the first path

The product `Ψ¹` of the point data of the edges is symmetrized to the path datum `Ψ⁰`, the sum of
its translates.
-/

section GridFirstColumns

open Function Matrix Fintype Finset Exchange Rows Subgroup MulAction Equiv

variable {P : Parameters} {D : Data P}

/-- For a set `w` of pairs of nodes, `tuplesOn ϑ w` is the set of tuples of matrices modulo
`gridModulus ϑ`, one for each pair of nodes, that are zero outside `w`. A tuple on the union of
disjoint sets `w` and `w'` is glued by `Finset.piecewise` from a tuple on `w` and one on `w'`, so a
sum over tuples on the union is a double sum. -/
lemma sum_tuplesOn_union {ϑ : D.MFoldTwist} {w w' : Finset (GridNode × GridNode)}
    (hw : Disjoint w w') (F : EdgeTuple ϑ → ℂ) :
    ∑ S ∈ tuplesOn ϑ (w ∪ w'), F S =
      ∑ S ∈ tuplesOn ϑ w, ∑ S' ∈ tuplesOn ϑ w', F (w.piecewise S S') := by
  rw [← sum_product']
  -- The inverse of gluing cuts a tuple into its parts on `w` and off `w`.
  refine sum_nbij' (fun S ↦ (w.piecewise S 0, w.piecewise 0 S)) (fun p ↦ w.piecewise p.1 p.2)
    (fun S hS ↦ by simp_all +contextual [mem_tuplesOn, Finset.piecewise])
    (fun p hp ↦ by simp_all +contextual [mem_tuplesOn, Finset.piecewise])
    (fun S _ ↦ by simp [piecewise_same]) (fun p hp ↦ ?_) fun S _ ↦ by simp [piecewise_same]
  simp only [mem_product, mem_tuplesOn] at hp
  ext e : 2 <;> by_cases he : e ∈ w <;> simp [he, hp, disjoint_left.1 hw]

/-- The edges of the column from `(0, m)` down to `(0, b)` in the grid `z` are those from `(0, i)`
to `(0, i + 1)` with `b ≤ i < m`. -/
lemma edges_column {z : Bool} {b : ℕ} (hb : b ≤ D.m) :
    (GridPath.column hb).edges z = (Ico b D.m).image (columnEdge z 0) := by
  induction hb using Nat.decreasingInduction with
  | self => simp [GridPath.column_self, GridPath.edges]
  | of_succ b hb ih =>
    simp [GridPath.column_of_lt hb, GridPath.edges, ih, ← insert_Ico_add_one_left_eq_Ico hb]

/-- An edge lies on the first path exactly when it is an edge of the first column of a grid. -/
lemma mem_edges_first {e : GridNode × GridNode} :
    e ∈ (TwoGridPath.first D.m).edges ↔ ∃ z : Bool, ∃ i < D.m, columnEdge z 0 i = e := by
  simp [TwoGridPath.edges, TwoGridPath.first, edges_column]

/-! ### The point data -/

/-- The point datum of the edge from `(0, b)` to `(0, b + 1)`, regarded modulo `𝔪`: the
indicator of the matrices that reduce to the standard inclusion modulo `𝔪₀` in the grid of the
`Y` and modulo `𝔟` in that of the `Ỹ`. -/
def edgePointDatum {ϑ : D.MFoldTwist} (z : Bool) (b : ℕ)
    (y : Matrix (D.NodeIndex (z, 0, b + 1)) (D.NodeIndex (z, 0, b)) (gridModulus ϑ).ResidueRing) :
    ℂ :=
  pointDatum (triangleModulus z ϑ).ResidueRing (y.map (reduceToTriangle ϑ z))

/-- The product of the point data `edgePointDatum` of the edges from `(0, b)` to `(0, m)` in the
grid `z`, at the matrices of `S`: the indicator that each of these matrices reduces to the standard
inclusion modulo `triangleModulus z ϑ`. -/
def columnPointDatum {ϑ : D.MFoldTwist} (z : Bool) (b : ℕ) (S : EdgeTuple ϑ) : ℂ :=
  ∏ i ∈ Ico b D.m, edgePointDatum z i (S (columnEdge z 0 i))

/-- The product `Ψ¹` of the point data of the edges of the first path. -/
def firstPointDatum {ϑ : D.MFoldTwist} (S : EdgeTuple ϑ) : ℂ :=
  columnPointDatum false 0 S * columnPointDatum true 0 S

/-- The product of the point data from `(0, b)` to `(0, m)` depends only on the matrices of the
edges between these two nodes. -/
lemma columnPointDatum_congr {ϑ : D.MFoldTwist} {z : Bool} {b : ℕ} {S S' : EdgeTuple ϑ}
    (hS : ∀ i ∈ Ico b D.m, S (columnEdge z 0 i) = S' (columnEdge z 0 i)) :
    columnPointDatum z b S = columnPointDatum z b S' :=
  prod_congr rfl fun i hi ↦ by rw [hS i hi]

/-- A value of `Ψ¹` is `0` or `1`, so it is a sum of at most one root of unity. -/
lemma isSumOfRootsOfUnity_firstPointDatum {ϑ : D.MFoldTwist} (S : EdgeTuple ϑ) :
    IsSumOfRootsOfUnity 1 (firstPointDatum S) := by
  by_cases hS : firstPointDatum S = 0
  · simpa only [hS] using IsSumOfRootsOfUnity.zero
  have h_one (z : Bool) (hz : columnPointDatum z 0 S ≠ 0) : columnPointDatum z 0 S = 1 :=
    prod_eq_one fun i hi ↦ by grind [edgePointDatum, prod_ne_zero_iff.1 hz i hi]
  rw [firstPointDatum, h_one _ (left_ne_zero_of_mul hS), h_one _ (right_ne_zero_of_mul hS), mul_one]
  exact .of_isOfFinOrder .one

/-- Let `y` be a matrix modulo `𝔪 = gridModulus ϑ` from the space `Y_b` at the node `(false, 0, b)`
to `Y_(b+1)`. If `edgePointDatum false b y` is nonzero, that is, `y` reduces to the standard
inclusion modulo `𝔪₀ = triangleModulus false ϑ`, then `y` has a left inverse modulo `𝔪`, because
`𝔪₀` and `𝔪` have the same primes. -/
lemma hasLeftInv_of_edgePointDatum_ne_zero {ϑ : D.MFoldTwist} {b : ℕ}
    {y : Matrix (D.NodeIndex (false, 0, b + 1)) (D.NodeIndex (false, 0, b))
      (gridModulus ϑ).ResidueRing} (hy : edgePointDatum false b y ≠ 0) : HasLeftInv y := by
  -- The transposed inclusion times `y` reduces to `1`, so it is invertible. (`erw`: the index
  -- set at `(0, b + 1)` is the sum of that at `(0, b)` and a finite set only by definition.)
  let J : Matrix (D.NodeIndex (false, 0, b + 1)) (D.NodeIndex (false, 0, b))
      (gridModulus ϑ).ResidueRing := inclMatrix _ .inl
  have h_red : y.map (reduceToTriangle ϑ false) = inclMatrix _ .inl := Pi.support_single_subset hy
  have h_unit : IsUnit (Jᵀ * y) := isUnit_of_mapMatrix (reduceToTriangle ϑ false) <| by
    simp only [J, RingHom.mapMatrix_apply, Matrix.map_mul, transpose_map]
    erw [h_red, map_inclMatrix, inclMatrix_transpose_mul_self .inl]
    exact isUnit_one
  exact ⟨_ * Jᵀ, (Matrix.mul_assoc ..).trans h_unit.val_inv_mul⟩

/-! ### The period -/

/-- Both `pointTransposedLift` and `transposedMove y` are transposed theta lifts from forms at
`(0, b + 1)` to forms at `(0, b)` of the grid `z`. The datum of the first is the indicator of the
inclusion matrix modulo `triangleModulus z ϑ`, scaled by the order `triangleGLCard z ϑ b`; that of
the second is the indicator of the single matrix `y` modulo `𝔪`. The first is `triangleGLCard z ϑ b`
times the sum of the second over `y`, weighted by the point datum `edgePointDatum` of the edge. -/
lemma pointTransposedLift_eq_sum {ϑ : D.MFoldTwist} {z : Bool} {b : ℕ} :
    pointTransposedLift ϑ z b = (triangleGLCard z ϑ b : ℂ) •
      ∑ y : Matrix (D.NodeIndex (z, 0, b + 1)) (D.NodeIndex (z, 0, b)) (gridModulus ϑ).ResidueRing,
        edgePointDatum z b y • transposedMove (ϑ := ϑ) y := by
  -- Pull the datum back along the reduction from `𝔪`, then expand it in indicator functions;
  -- `rfl` identifies the pullback with `edgePointDatum` and each summand with `transposedMove`.
  erw [pointTransposedLift, modTransposedLift, ← modDatum_factor, modDatum_eq_sum]
  simp only [map_sum, map_smul]
  rfl

/-- Let `b ≤ m = D.m` and take the first column of the grid `z` from `(0, m)` down to `(0, b)`. With
`π_M = D.piM`, `𝔟 = π_M ^ D.natB` and `Q` the product of the places of `ϑ`, the modulus
`triangleModulus z ϑ` is `π_M Q` for `false` and `𝔟` for `true`, and `triangleGLCard z ϑ i` is the
order of `GL` of the node `(0, i)` modulo it. The composite `transposedChain ϑ z b` of the
transposed theta lifts `pointTransposedLift` along the column is the product of these orders,
`b ≤ i < m`, times a sum over the tuples `S` of matrices modulo `𝔪 = 𝔟Q` on its edges: the composite
`formMap` of the transposed lifts whose data are the single matrices of `S`, weighted by the
indicator `columnPointDatum z b S` that each matrix reduces to the standard inclusion modulo
`triangleModulus z ϑ`. -/
lemma transposedChain_eq_sum {ϑ : D.MFoldTwist} {z : Bool} {b : ℕ} (hb : b ≤ D.m) :
    transposedChain ϑ z b = (∏ i ∈ Ico b D.m, (triangleGLCard z ϑ i : ℂ)) •
      ∑ S ∈ tuplesOn ϑ ((GridPath.column hb).edges z),
        columnPointDatum z b S • (GridPath.column hb).formMap S z := by
  induction hb using Nat.decreasingInduction with
  | self => simp [transposedChain_self, GridPath.column_self, GridPath.edges, GridPath.formMap,
      tuplesOn_empty, columnPointDatum]
  | of_succ b hb ih =>
    -- The factors and the maps of the later edges do not see the matrix `y` of the new edge.
    let M := Matrix (D.NodeIndex (z, 0, b + 1)) (D.NodeIndex (z, 0, b)) (gridModulus ϑ).ResidueRing
    have h_new : columnEdge z 0 b ∉ (GridPath.column hb).edges z := by simp [edges_column]
    have h_datum (S : EdgeTuple ϑ) (y : M) :
        columnPointDatum z b (update S (columnEdge z 0 b) y) =
          edgePointDatum z b y * columnPointDatum z (b + 1) S := by
      rw [columnPointDatum, prod_eq_prod_Ico_succ_bot hb, update_self]
      exact congrArg _ (columnPointDatum_congr (by grind))
    have h_map (S : EdgeTuple ϑ) (y : M) :
        (GridPath.column hb).formMap (update S (columnEdge z 0 b) y) z =
          (GridPath.column hb).formMap S z := GridPath.formMap_congr _ (by grind)
    rw [transposedChain_of_lt ϑ hb, ih, pointTransposedLift_eq_sum, GridPath.column_of_lt hb,
      GridPath.edges,
      sum_tuplesOn_insert h_new, sum_comm, prod_eq_prod_Ico_succ_bot hb]
    ext φ : 1
    simp [GridPath.formMap, h_datum, h_map, smul_sum, smul_smul, mul_assoc, mul_left_comm]

/-- In the grid of the `Ỹ` the iterated transposed lifts `transposedChain` along the first column do
not depend on the twist. -/
lemma transposedChain_one_true_eq_transposedChain {b : ℕ} (ϑ : D.MFoldTwist) (hb : b ≤ D.m) :
    D.transposedChain 1 true b = transposedChain ϑ true b := by
  induction hb using Nat.decreasingInduction with
  | self => rw [transposedChain_self, transposedChain_self]
  | of_succ b hb ih => rw [transposedChain_of_lt 1 hb, transposedChain_of_lt ϑ hb, ih,
      show D.pointTransposedLift 1 true b = pointTransposedLift ϑ true b from rfl]

/-- Let `ϑ` be an m-fold twist (`MFoldTwist`), `y'` a conjugate form on `Y_m` and `φ` a form on
`Ỹ^m_0`. Move them to `Y₀` and `Ỹ^0_0` by `transposedChain`, the composites of transposed theta
lifts down the first columns of the two grids `Y` (`false`) and `Ỹ` (`true`). The pairing of the
images by a bilinear form `B` equals a product times a sum. The product runs over `i < D.m` and both
grids `z` of `triangleGLCard z ϑ i`, the order of `GL` at the node `(z, 0, i)` modulo
`triangleModulus z ϑ`. The sum runs over the tuples `S ∈ tuplesOn ϑ` of matrices on the edges of the
first path `TwoGridPath.first D.m`, which goes down both first columns. Its term is
`firstPointDatum S`, the indicator that each matrix reduces to the standard inclusion modulo
`triangleModulus z ϑ`, times `B` of the two forms mapped down the columns by `S` (`formMap`). -/
lemma pairing_transposedChain_eq_sum {ϑ : D.MFoldTwist}
    (B : D.GridForm false 0 0 →ₗ[ℂ] D.GridForm true 0 0 →ₗ[ℂ] ℂ)
    (y' : D.GridForm false 0 D.m) (φ : D.GridForm true 0 D.m) :
    B (transposedChain ϑ false 0 y') (D.transposedChain 1 true 0 φ) =
      (∏ i ∈ range D.m, (triangleGLCard false ϑ i : ℂ) * triangleGLCard true ϑ i) *
        ∑ S ∈ tuplesOn ϑ (TwoGridPath.first D.m).edges, firstPointDatum S *
          B ((GridPath.column D.m.zero_le).formMap S false y')
            ((GridPath.column D.m.zero_le).formMap S true φ) := by
  set p : GridPath 0 D.m 0 0 := .column D.m.zero_le
  have h_disjoint : Disjoint (p.edges false) (p.edges true) := disjoint_edges_column _
  have h_glue_true (S S' : EdgeTuple ϑ) :
      ∀ e ∈ p.edges true, (p.edges false).piecewise S S' e = S' e :=
    fun e he ↦ piecewise_eq_of_notMem _ _ _ (disjoint_right.1 h_disjoint he)
  have h_mem (z : Bool) : ∀ i ∈ Ico 0 D.m, columnEdge z 0 i ∈ p.edges z := by
    simp +contextual [p, edges_column]
  -- Of a tuple glued from `S` and `S'` the column of the `Y` sees `S`, that of the `Ỹ` sees `S'`.
  have h_datum (S S' : EdgeTuple ϑ) : firstPointDatum ((p.edges false).piecewise S S') =
      columnPointDatum false 0 S * columnPointDatum true 0 S' := by
    rw [firstPointDatum, columnPointDatum_congr fun i hi ↦ h_glue_true S S' _ (h_mem true i hi),
      columnPointDatum_congr fun i hi ↦ piecewise_eq_of_mem _ _ _ (h_mem false i hi)]
  have h_formMap_false (S S' : EdgeTuple ϑ) :
      p.formMap ((p.edges false).piecewise S S') false = p.formMap S false :=
    p.formMap_congr fun e ↦ piecewise_eq_of_mem _ S S'
  have h_sum : ∑ S ∈ tuplesOn ϑ (p.edges false ∪ p.edges true),
        firstPointDatum S * B (p.formMap S false y') (p.formMap S true φ) =
      B ((∑ S ∈ tuplesOn ϑ (p.edges false), columnPointDatum false 0 S • p.formMap S false) y')
        ((∑ S ∈ tuplesOn ϑ (p.edges true), columnPointDatum true 0 S • p.formMap S true) φ) := by
    rw [sum_tuplesOn_union h_disjoint, sum_comm]
    simp [h_datum, h_formMap_false, p.formMap_congr (h_glue_true _ _), mul_sum, mul_assoc,
      mul_left_comm]
  rw [show (TwoGridPath.first D.m).edges = p.edges false ∪ p.edges true from rfl, h_sum,
    transposedChain_one_true_eq_transposedChain ϑ zero_le, transposedChain_eq_sum zero_le,
      transposedChain_eq_sum zero_le,
      range_eq_Ico]
  simp only [prod_mul_distrib, LinearMap.smul_apply, map_smul, smul_eq_mul, p, mul_assoc,
    mul_left_comm]

/-! ### Invariance -/

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.univ in
/-- Let `k` be an invertible matrix modulo `gridModulus ϑ = 𝔟Q` in the level `nodeLevel` at a node
`(z, 0, i)` of the first column: the trivial subgroup for `z = false`, the kernel of reduction
modulo `𝔟` for `z = true`. Then `k` reduces to `1` under `reduceToTriangle ϑ z`, the reduction
modulo `π_M Q` for `z = false` and modulo `𝔟` for `z = true`, and for any `b` the character
`edgeChar` of the edge from `(z, 0, b)` to `(z, 0, b + 1)` is `1` at the determinant of `k`. -/
lemma map_eq_one_and_edgeChar_eq_one_of_mem_nodeLevel {ϑ : D.MFoldTwist} {z : Bool} {b i : ℕ}
    {k : GL (D.NodeIndex (z, 0, i)) (gridModulus ϑ).ResidueRing}
    (hk : k ∈ nodeLevel ϑ (z, 0, i)) :
    k.map (reduceToTriangle ϑ z) = 1 ∧ edgeChar ϑ (columnEdge z 0 b) k.val.det = 1 := by
  cases z
  · -- For `z = false` the level is trivial.
    simp [show k = 1 by simpa [nodeLevel] using hk]
  -- For `z = true` the character is untwisted, so it may be read at the modulus of the trivial
  -- twist, where `k` is `1`.
  replace hk : k.map (reduceToTriangle ϑ true) = 1 := by simpa [nodeLevel] using hk
  obtain ⟨k₀, rfl⟩ := reductionGL_surjective k
  have hk₀ : (D.gridModulus 1).reductionGL k₀ = 1 :=
    (Units.ext Modulus.factor_reductionGL).symm.trans hk
  -- Both sides are the value at `k₀` of the adelic character `gridChar`, in which the twist
  -- does not enter.
  have h_char : edgeChar ϑ (columnEdge true 0 b) ((gridModulus ϑ).reductionGL k₀).1.det =
      (D.gridModulus 1).charOfTamePart (gridTamePart 1 false b)
        ((D.gridModulus 1).reductionGL k₀).1.det :=
    (gridChar_det (ϑ := ϑ) false b Unit 1 k₀).symm.trans (gridChar_det (ϑ := 1) false b Unit 1 k₀)
  exact ⟨hk, by simp [h_char, hk₀]⟩

/-- Let `g` be a family of invertible matrices modulo `gridModulus ϑ`, one at each node, whose
members on the first path (the nodes `(z, 0, i)`, `i ≤ D.m`) lie in `nodeLevel`: they are `1` for
`z = false` and `1` modulo `D.piM ^ D.natB` for `z = true`. Then `g` fixes `Ψ¹ = firstPointDatum`,
the indicator that each matrix of the path reduces to the standard inclusion, under the action on
functions of tuples: the matrix from `p` to `q` becomes `(g q)⁻¹ * S (p, q) * g p`, and the value
is multiplied by the product of the characters of the edges at `det (g q) / det (g p)`. -/
lemma firstPointDatum_invariant {ϑ : D.MFoldTwist} {g : NodeFamily ϑ}
    (hg : ∀ z : Bool, ∀ i ≤ D.m, g (z, 0, i) ∈ nodeLevel ϑ (z, 0, i)) (S : EdgeTuple ϑ) :
    edgeCharProd g (TwoGridPath.first D.m).edges * firstPointDatum (tupleAction g S) =
      firstPointDatum S := by
  have h_char : edgeCharProd g (TwoGridPath.first D.m).edges = 1 := prod_eq_one fun e he ↦ by
    obtain ⟨z, i, hi, rfl⟩ := mem_edges_first.1 he
    simp [(map_eq_one_and_edgeChar_eq_one_of_mem_nodeLevel (hg z i hi.le)).2,
      (map_eq_one_and_edgeChar_eq_one_of_mem_nodeLevel (hg z (i + 1) hi)).2]
  have h_red (z : Bool) (j : ℕ) (hj : j ≤ D.m) : (g (z, 0, j)).map (reduceToTriangle ϑ z) = 1 :=
    (map_eq_one_and_edgeChar_eq_one_of_mem_nodeLevel (b := 0) (hg z j hj)).1
  have h_column (z : Bool) : columnPointDatum z 0 (tupleAction g S) = columnPointDatum z 0 S := by
    refine prod_congr rfl fun i hi ↦ ?_
    replace hi : i < D.m := (mem_Ico.1 hi).2
    -- `-coe_units_inv` keeps the inverse a unit, so that the map passes through it.
    simp [edgePointDatum, tupleAction, Matrix.map_mul, -coe_units_inv,
      ← GeneralLinearGroup.val_map_apply, h_red z i hi.le, h_red z (i + 1) hi]
  simp [h_char, firstPointDatum, h_column]

/-- The cosets of the level `nodeLevel` at a node form a finite type. -/
instance fintypeQuotientNodeLevel {ϑ : D.MFoldTwist} (z : Bool) (a b : ℕ) :
    Fintype (GL (D.GridIndex z a b) (gridModulus ϑ).ResidueRing ⧸ nodeLevel ϑ (z, a, b)) :=
  .ofFinite _

/-- A coset of the level `nodeLevel` for each of the spaces `Y_i` and `Ỹ^i_0` with `i < m`: of the
level `𝔪` at `Y_i` and of the level `𝔟` at `Ỹ^i_0`. -/
abbrev LevelCosets (ϑ : D.MFoldTwist) : Type :=
  ∀ p : Bool × Fin D.m,
    GL (D.NodeIndex (p.1, 0, p.2)) (gridModulus ϑ).ResidueRing ⧸ nodeLevel ϑ (p.1, 0, p.2)

/-- Representatives of the cosets `x`, extended by `1` to the other spaces. -/
def LevelCosets.out {ϑ : D.MFoldTwist} (x : LevelCosets ϑ) : NodeFamily ϑ
  | (z, 0, i) => if h : i < D.m then (x (z, ⟨i, h⟩)).out else 1
  | _ => 1

/-- The family by which the cosets `x` translate: the representatives, except that `Ỹ^0_0`
moves with `Y^0_0`. -/
def LevelCosets.family {ϑ : D.MFoldTwist} (x : LevelCosets ϑ) : NodeFamily ϑ :=
  update x.out (true, 0, 0) (blockInlGL (D.gridDiagEquiv 0) (x.out (false, 0, 0)))

/-- The sum `Ψ⁰` of the translates of `Ψ¹` over the coset families, each weighted by the
characters of the edges. The coset at `Ỹ^0_0` does not act, so each translate is counted a constant
number of times. -/
def firstPathDatum (ϑ : D.MFoldTwist) (S : EdgeTuple ϑ) : ℂ :=
  ∑ x : LevelCosets ϑ, edgeCharProd x.family (TwoGridPath.first D.m).edges *
    firstPointDatum (tupleAction x.family S)

/-- Let `g` be an admissible family of invertible matrices modulo `gridModulus ϑ`: it is `1` at
`(false, 0, D.m)`, is `1` modulo `D.piM ^ D.natB` at `(true, 0, D.m)`, and at `(true, a, a)` is the
block sum of `g (false, a, a)` with `1`. Then `g` fixes `Ψ⁰ = firstPathDatum ϑ` under translation
of the matrices (`tupleAction`) followed by multiplication by the product `edgeCharProd` of the
characters of the edges, because `Ψ⁰` is the sum of the translates of the indicator
`firstPointDatum` over cosets of the levels `nodeLevel`, and `g` permutes these cosets. -/
lemma firstPathDatum_invariant {ϑ : D.MFoldTwist} {g : NodeFamily ϑ} (hg : IsAdmissibleFamily g)
    (S : EdgeTuple ϑ) :
    edgeCharProd g (TwoGridPath.first D.m).edges * firstPathDatum ϑ (tupleAction g S) =
      firstPathDatum ϑ S := by
  obtain ⟨hg_end, hg_diag⟩ : (∀ z : Bool, g (z, 0, D.m) ∈ nodeLevel ϑ (z, 0, D.m)) ∧
      ∀ a : ℕ, g (true, a, a) = blockInlGL (D.gridDiagEquiv a) (g (false, a, a)) := hg
  let σ : LevelCosets ϑ ≃ LevelCosets ϑ := piCongrRight fun p ↦ toPerm (g (p.1, 0, p.2))
  -- Reindex the translates by `σ`: the family of `σ x` and `g` times that of `x` differ by a
  -- family in the levels, which fixes `Ψ¹`.
  rw [firstPathDatum, firstPathDatum, mul_sum,
    ← σ.sum_comp fun y ↦ _ * firstPointDatum (tupleAction y.family S)]
  refine sum_congr rfl fun x _ ↦ ?_
  have h_coset (z : Bool) (i : ℕ) (hi : i ≤ D.m) :
      ((σ x).out (z, 0, i))⁻¹ * (g (z, 0, i) * x.out (z, 0, i)) ∈ nodeLevel ϑ (z, 0, i) := by
    obtain rfl | hi := hi.eq_or_lt
    · simp [LevelCosets.out, hg_end]
    · simp [LevelCosets.out, ← QuotientGroup.eq, σ, ← Quotient.mk_smul_out, hi]
  -- The level at `Y^0_0` is trivial, so the component at `Ỹ^0_0` is `1`.
  have h_zero : ((σ x).out (false, 0, 0))⁻¹ * (g (false, 0, 0) * x.out (false, 0, 0)) = 1 :=
    mem_bot.1 (h_coset false 0 D.m.zero_le)
  have h_level (z : Bool) (i : ℕ) (hi : i ≤ D.m) :
      ((σ x).family⁻¹ * (g * x.family)) (z, 0, i) ∈ nodeLevel ϑ (z, 0, i) := by
    by_cases h_corner : ((z, 0, i) : GridNode) = (true, 0, 0)
    · cases h_corner
      simp [LevelCosets.family, hg_diag, ← map_inv, ← map_mul, h_zero, Prod.mk_one_one]
    · simp [LevelCosets.family, h_coset z i hi, h_corner]
  rw [← firstPointDatum_invariant h_level (tupleAction (σ x).family S)]
  simp only [← mul_assoc, ← edgeCharProd_mul, ← tupleAction_mul, mul_inv_cancel, one_mul]

/-- The number of coset families `LevelCosets ϑ` is at most `edgeMatrixCountBound ϑ ^ (2 * D.m)`.
`edgeMatrixCountBound ϑ` bounds the number of matrices modulo `gridModulus ϑ` of an edge between
nodes of index at most `D.m`. -/
lemma card_levelCosets_le {ϑ : D.MFoldTwist} :
    card (LevelCosets ϑ) ≤ edgeMatrixCountBound ϑ ^ (2 * D.m) := by
  rw [Fintype.card_pi]
  refine (prod_le_pow_card univ _ (edgeMatrixCountBound ϑ) fun ⟨z, i⟩ _ ↦ ?_).trans_eq (by simp)
  calc _ ≤ card (GL (D.NodeIndex (z, 0, i)) (gridModulus ϑ).ResidueRing) :=
        card_le_of_surjective _ QuotientGroup.mk_surjective
    _ ≤ card (Matrix (D.NodeIndex (z, 0, i)) (D.NodeIndex (z, 0, i)) (gridModulus ϑ).ResidueRing) :=
        card_le_of_injective _ Units.val_injective
    _ ≤ edgeMatrixCountBound ϑ := card_matrix_le_edgeMatrixCountBound (by simp) (by simp)

/-- Put `m = D.m`. The function `Ψ⁰ = firstPathDatum ϑ`, the weighted sum of the translates of the
indicator `firstPointDatum`, is a path datum on the first path, the edges from `(z, 0, i)` to
`(z, 0, i + 1)` with `i < m`. Its values are sums of at most `N ^ (2 m)` roots of unity, where
`N = edgeMatrixCountBound ϑ` bounds the number of matrices modulo `gridModulus ϑ` between two nodes
with indices at most `m`. -/
lemma isPathDatum_firstPathDatum (ϑ : D.MFoldTwist) :
    IsPathDatum (edgeMatrixCountBound ϑ ^ (2 * D.m)) (TwoGridPath.first D.m).edges
      (firstPathDatum ϑ) where
  dependsOn S S' hS := by
    have h_column (x : LevelCosets ϑ) (z : Bool) : columnPointDatum z 0 (tupleAction x.family S) =
        columnPointDatum z 0 (tupleAction x.family S') :=
      columnPointDatum_congr fun i hi ↦ by
        rw [tupleAction, tupleAction, hS _ (mem_edges_first.2 ⟨z, i, (mem_Ico.1 hi).2, rfl⟩)]
    simp only [firstPathDatum, firstPointDatum, h_column]
  invariant _ := firstPathDatum_invariant
  hasLeftInv S hS e he h_vertical := by
    -- Some translate of `Ψ¹` is nonzero at `S`, and translation keeps split injectivity.
    obtain ⟨x, -, hx⟩ := exists_ne_zero_of_sum_ne_zero hS
    obtain ⟨z, i, hi, rfl⟩ := mem_edges_first.1 he
    obtain rfl : z = false := by simpa [IsVerticalEdge] using h_vertical
    have h_false : columnPointDatum false 0 (tupleAction x.family S) ≠ 0 :=
      left_ne_zero_of_mul (right_ne_zero_of_mul hx)
    obtain ⟨L, hL⟩ : HasLeftInv (tupleAction x.family S (columnEdge false 0 i)) :=
      hasLeftInv_of_edgePointDatum_ne_zero (prod_ne_zero_iff.1 h_false i (by simpa))
    refine ⟨(x.family (false, 0, i)).1 * L * (x.family (false, 0, i + 1))⁻¹.1, ?_⟩
    -- Conjugate the equation of the left inverse `L` by the matrix at `(0, i)`.
    simpa [tupleAction, Matrix.mul_assoc] using congrArg
      (fun M ↦ (x.family (false, 0, i)).1 * M * (x.family (false, 0, i))⁻¹.1) hL
  isSumOfRootsOfUnity S := by
    have h_sum : IsSumOfRootsOfUnity (card (LevelCosets ϑ) * 1) (firstPathDatum ϑ S) := .sum fun x ↦
      (isSumOfRootsOfUnity_firstPointDatum _).mul_left (isOfFinOrder_edgeCharProd _ _)
    exact h_sum.mono (by simpa using card_levelCosets_le)

/-- For a tuple `S` of matrices let `periodAt S` be the period, for the twist `ϑ` and at the real
point `gInf`, of the images under `formMap S` down the first columns of a conjugate form `y'` on
`Y_m` and a form `φ` on `Ỹ^m_0`. The sum of `periodAt` over the tuples on the first path weighted by
`Ψ⁰` is the cardinality of `LevelCosets ϑ` times the sum weighted by `Ψ¹`, because every translate
of `Ψ¹` gives the same sum. -/
lemma sum_firstPathDatum_mul {ϑ : D.MFoldTwist} (gInf : GInf D.E (D.gridSigns true 0 0 0))
    (y' : D.GridForm false 0 D.m) (φ : D.GridForm true 0 D.m) :
    let periodAt (S : EdgeTuple ϑ) : ℂ := diagonalPeriodForm ϑ zero_le gInf
      ((GridPath.column D.m.zero_le).formMap S false y')
      ((GridPath.column D.m.zero_le).formMap S true φ)
    ∑ S ∈ tuplesOn ϑ (TwoGridPath.first D.m).edges, firstPathDatum ϑ S * periodAt S =
      card (LevelCosets ϑ) * ∑ S ∈ tuplesOn ϑ (TwoGridPath.first D.m).edges,
        firstPointDatum S * periodAt S := by
  intro periodAt
  set pathEdges : Finset (GridNode × GridNode) := (TwoGridPath.first D.m).edges
  have h_end (x : LevelCosets ϑ) (z : Bool) : x.family (z, 0, D.m) = 1 := by
    simp [LevelCosets.family, LevelCosets.out, m_eq_two_mul_varrho_add_two]
  have h_diag (x : LevelCosets ϑ) :
      x.family (true, 0, 0) = blockInlGL (D.gridDiagEquiv 0) (x.family (false, 0, 0)) := by
    simp [LevelCosets.family]
  have h_period (x : LevelCosets ϑ) (S : EdgeTuple ϑ) :
      periodAt (tupleAction x.family S) = edgeCharProd x.family pathEdges * periodAt S :=
    diagonalPeriodForm_tupleAction (h_end x) (h_diag x) gInf y' φ S
  have h_translate (x : LevelCosets ϑ) : ∑ S ∈ tuplesOn ϑ pathEdges,
      edgeCharProd x.family pathEdges * firstPointDatum (tupleAction x.family S) * periodAt S =
        ∑ S ∈ tuplesOn ϑ pathEdges, firstPointDatum S * periodAt S := by
    rw [← sum_tuplesOn_tupleAction x.family fun S ↦ firstPointDatum S * periodAt S]
    simp only [h_period, mul_assoc, mul_left_comm]
  simp only [firstPathDatum, sum_mul]
  rw [sum_comm, sum_eq_card_nsmul fun x _ ↦ h_translate x, card_univ, nsmul_eq_mul]

/-- The number of coset families `LevelCosets` is the product of the indices `levelIndex` of the
levels of the nodes `(0, i)` in the grid of the `Y` and of the orders `triangleGLCard` in that of
the `Ỹ`, over `i < m`. -/
lemma card_levelCosets_eq (ϑ : D.MFoldTwist) : (card (LevelCosets ϑ) : ℂ) =
    ∏ i ∈ range D.m, levelIndex ϑ false 0 i * triangleGLCard true ϑ i := by
  have h_index (z : Bool) (i : ℕ) : (card (GL (D.NodeIndex (z, 0, i)) (gridModulus ϑ).ResidueRing ⧸
      nodeLevel ϑ (z, 0, i)) : ℂ) = levelIndex ϑ z 0 i := by
    rw [levelIndex, index_eq_card, Nat.card_eq_fintype_card]
  have h_true (i : ℕ) : levelIndex ϑ true 0 i = triangleGLCard true ϑ i :=
    levelIndex_eq_card_GL_untwisted (Or.inl rfl)
  rw [Fintype.card_pi, Nat.cast_prod, Fintype.prod_prod_type, Fintype.prod_bool, mul_comm]
  simp only [h_index, h_true, prod_range, prod_mul_distrib]

/-- Let `y'` be a conjugate form on `Y_m`, `φ` a form on `Ỹ^m_0`, and `g` a real point of the
unitary group of `Ỹ^0_0`. Move `y'` and `φ` down the first columns by the composites
`transposedChain` of transposed theta lifts, `y'` at the twist `ϑ` and `φ` at the trivial twist `1`.
The period at `g` of the images is a constant, independent of `ϑ`, times `gridPeriod` of
`Ψ⁰ = firstPathDatum` at `(ϑ, y', φ)`: the sum over the tuples `S` on the first path of `Ψ⁰ ϑ S`
times the period at `g` of the images of `y'` and `φ` under the matrices of `S`. -/
lemma exists_diagonalPeriodForm_transposedChain_eq :
    ∃ C : ℂ, ∀ (ϑ : D.MFoldTwist) (g : GInf D.E (D.gridSigns true 0 0 0))
      (y' : D.GridForm false 0 D.m) (φ : D.GridForm true 0 D.m),
      diagonalPeriodForm ϑ zero_le g (transposedChain ϑ false 0 y')
          (D.transposedChain 1 true 0 φ) =
        C * gridPeriod (.first D.m) firstPathDatum g (ϑ, y', φ) := by
  choose κ hκ using (D.exists_triangleGLCard_eq_mul_levelIndex :
    ∀ j : ℕ, ∃ C : ℂ, ∀ ϑ : D.MFoldTwist, D.triangleGLCard false ϑ j = C * levelIndex ϑ false 0 j)
  refine ⟨∏ i ∈ range D.m, κ i, fun ϑ g y' φ ↦ ?_⟩
  have h_period : gridPeriod (.first D.m) firstPathDatum g (ϑ, y', φ) =
      card (LevelCosets ϑ) * ∑ S ∈ tuplesOn ϑ (TwoGridPath.first D.m).edges, firstPointDatum S *
        diagonalPeriodForm ϑ zero_le g ((GridPath.column D.m.zero_le).formMap S false y')
          ((GridPath.column D.m.zero_le).formMap S true φ) :=
    sum_firstPathDatum_mul g y' φ
  -- The period of `Ψ⁰` is the number of coset families times that of `Ψ¹`. This number is the
  -- product of the indices of the levels, and the orders for the `Y` are `κ i` times the indices.
  rw [h_period, card_levelCosets_eq, pairing_transposedChain_eq_sum]
  simp only [hκ, prod_mul_distrib, mul_assoc]

/-- Put `m = D.m`; the first path `TwoGridPath.first m` consists of the edges from `(z, 0, i)` to
`(z, 0, i + 1)` with `i < m`. There are a constant `C` and, for each `m`-fold twist `ϑ`, a path
datum `Ψ ϑ` on the first path. They satisfy the following for a conjugate form `y'` on `Y^0_m`, a
form `φ` on `Ỹ^m_0` (`GridForm true 0 m`) and a point `g` of the archimedean unitary group `GInf` of
`Ỹ^0_0`. Move `y'` and `φ` down the first columns by the composites `transposedChain` of transposed
theta lifts, `y'` at `ϑ` and `φ` at the trivial twist `1`. The period `diagonalPeriodForm` at `g` of
the images is `C` times `gridPeriod`: the sum over the tuples `S` on the first path of `Ψ ϑ S` times
the period at `g` of the images of `y'` and `φ` under the matrices of `S`. -/
lemma exists_isPathDatum_diagonalPeriodForm_eq :
    ∃ (C : ℂ) (Ψ : ∀ ϑ : D.MFoldTwist, EdgeTuple ϑ → ℂ), ∀ ϑ : D.MFoldTwist,
      IsPathDatum (edgeMatrixCountBound ϑ ^ (2 * D.m)) (TwoGridPath.first D.m).edges (Ψ ϑ) ∧
      ∀ (g : GInf D.E (D.gridSigns true 0 0 0)) (y' : D.GridForm false 0 D.m)
        (φ : D.GridForm true 0 D.m),
        diagonalPeriodForm ϑ zero_le g (transposedChain ϑ false 0 y')
            (D.transposedChain 1 true 0 φ) =
          C * gridPeriod (.first D.m) Ψ g (ϑ, y', φ) := by
  obtain ⟨C, hC⟩ := exists_diagonalPeriodForm_transposedChain_eq (D := D)
  exact ⟨C, firstPathDatum, fun ϑ ↦ ⟨isPathDatum_firstPathDatum ϑ, hC ϑ⟩⟩

end GridFirstColumns

end New.Data

end
