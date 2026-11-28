import Lib.Adelic.TraceFormula.CuspidalComparison
import Lib.Adelic.TraceFormula.CuspidalType
import New.Determinant.Norms.AdjointThetaLift

/-!
# Equality of multiplicities

The spaces `Y_0, W_1, …, W_m` share the group `G_fin`, the level and the parameter, and differ only
in their signs at the real places. Let `V`, `V'` be two hermitian spaces for whose signs the
parameter `New.Data.paramW` has gap `D.gap`. Then a spherical Hecke operator away from the level `M`
has the same trace on their good forms. The equality of traces is deduced from the comparison of
traces for a test function that is cuspidal at one split place (`New.trace_eq_of_isCuspidalAt`).

## Main definitions and results

* `New.Data.exists_heckeAlgebra_eq_mul_inner_of_hasSum_rallisTerm`: the sums of scalar multiples of
  the Rallis series on two spaces are the same multiples of matrix coefficients of one element of
  the Hecke algebra.
* `New.Data.trace_heckeOnGood_eq`, `New.Data.charpoly_heckeOnGood_eq`,
  `New.Data.det_heckeOnGood_eq`: equal traces, characteristic polynomials and determinants.
* `New.Data.rallisOnGood`, `New.Data.det_rallisOnGood_eq`: the Rallis series preserves the good
  forms and has the same determinant on the good forms of both spaces.
* `New.Data.finrank_goodForms_inf_eigenPart_eq`: each eigensystem has the same multiplicity.
* `New.Data.targetDim_eq_finrank_goodForms_spaceW`: the good forms on `Y_0` and on `W_j` have the
  same dimension.

Notions from other files:
* `New.Data.principalForms`: the forms fixed by the principal level `D.chosenLevel` at the chosen
  places above `M`.
* `New.Data.principalRep`: the action on them of `D.chosenGL = ∏ GL_r(𝔽_w)`, over the chosen places
  w.
* `New.Data.goodForms`: the image of the idempotent `D.e₀` on these forms.
* `New.Data.heckeAlgebra`, `New.Data.eigenPart`: the spherical Hecke operators away from `M`, and
  the part with a given eigensystem.
* `New.HCParam.HasGap`: entries of the parameter with different signs are at least `h` apart.

## Relation to the literature

The equality of traces is the analogue of the Jacquet–Langlands correspondence for a quaternion
algebra that is ramified exactly at the real places. Related work: Harris–Labesse, Conditional base
change for unitary groups, 2004; Labesse, Changement de base CM et séries discrètes, 2011.
-/

namespace New

namespace Data

open Module Submodule LinearMap Gf MonoidAlgebra Representation

variable {P : Parameters} (D : Data P) {s s' : D.RowIndex → ℤˣ}

/-- A family `c` in `D.goodTupleFamilies` consists of a polynomial `c x` over the residue field of
each chosen place `x`. Above each of the primes `p₀`, `p₁` these polynomials are monic of degree
`r = card D.RowIndex`, all allowed (`New.IsAllowedPolynomial`), and one of them is primitive. In
particular, some `c x` is primitive: irreducible, with a root that generates the units of the
extension of degree `r` of the residue field. -/
lemma exists_isPrimitivePolynomial
    {c : ∀ x : (i : Fin 2) × D.ChosenPlace i, Polynomial (ResField (D.chosenPlace x))}
    (hc : c ∈ D.goodTupleFamilies) :
    ∃ x : (i : Fin 2) × D.ChosenPlace i, IsPrimitivePolynomial (Fintype.card D.RowIndex) (c x) := by
  classical
  rw [goodTupleFamilies, Finset.mem_map_equiv, Fintype.mem_piFinset] at hc
  obtain ⟨-, -, w, h_prim⟩ := Finset.mem_filter.1 (hc 0)
  exact ⟨⟨0, w⟩, h_prim⟩

/-- Let `γ` be a finite point of the unitary group whose component is `1` at each place
`D.chosenPlace x`. There is a spherical Hecke operator `p` away from these places with
`⟪z, p y⟫ = ⟪z, γ y⟫` for every space `W` and all forms `z`, `y` on `W` of principal level. -/
lemma exists_heckeAlgebra_inner_eq_inner_translate {γ : Gf D.E D.RowIndex}
    (hγ : γ ∈ D.offLevelGroup) :
    ∃ p : D.heckeAlgebra, ∀ {s : D.RowIndex → ℤˣ} (W : Space D.E D.RowIndex s)
      (z y : D.principalForms W),
      inner ℂ z (p.val W y) = inner ℂ z.val (W.formRep (typeKernel D.paramW s) γ y) := by
  -- The operator is the mean of the translations by `k γ` over the cosets `k H` in
  -- `K = K₀ ∩ G^M`. The group `H = K ∩ γ K γ⁻¹` is open in the compact group `K`.
  let g : D.offLevelGroup := ⟨γ, hγ⟩
  let K : Subgroup D.offLevelGroup := (stdLevel D.E D.RowIndex).subgroupOf D.offLevelGroup
  let H : Subgroup K := (K.comap (MulAut.conj g⁻¹).toMonoidHom).subgroupOf K
  have h_closed : IsClosed (D.offLevelGroup : Set (Gf D.E D.RowIndex)) := by
    have h_eq : (D.offLevelGroup : Set (Gf D.E D.RowIndex)) =
        ⋂ w ∈ Set.range D.chosenPlace, {k | k.atPlace w = 1} := Set.ext fun k ↦ by
          simp [mem_trivialOn]
    rw [h_eq]
    exact isClosed_biInter fun w _ ↦ isClosed_eq (continuous_atPlace w) continuous_const
  have h_compact : IsCompact (K : Set D.offLevelGroup) :=
    h_closed.isClosedEmbedding_subtypeVal.isCompact_preimage isCompact_stdLevel
  have h_open : IsOpen (K.comap (MulAut.conj g⁻¹).toMonoidHom : Set D.offLevelGroup) :=
    (IsTopologicalGroup.continuous_conj g⁻¹).isOpen_preimage _
      (isOpen_stdLevel.preimage continuous_subtype_val)
  have h_fin := H.fintypeOfIndexNeZero (h_compact.relIndex_ne_zero h_open)
  let a : ℂ[D.offLevelGroup] := ∑ q : K ⧸ H, .single (q.out * g) 1
  have h_act {M : Type} [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ D.offLevelGroup M)
      (y : M) : ρ.asAlgebraHom a y = ∑ q : K ⧸ H, ρ (q.out * g) y := by
    simp [a]
  -- As `k γ y` depends only on the coset `k H`, left translation by `K` permutes the terms.
  have ha : a ∈ D.sphericalAlgebra := by
    refine D.mem_sphericalAlgebra_of_mem_universalLevelAlgebra (mem_universalLevelAlgebra.2
      fun M _ _ ρ ↦ mem_levelAlgebra.2 fun y hy ↦ ?_)
    have h_inv (k h : K) (hh : h ∈ H) : ρ ((k * h).val * g) y = ρ (k.val * g) y := by
      have h_mem : g⁻¹ * h * g ∈ K := by simpa [H, Subgroup.mem_subgroupOf] using hh
      have h_fix : ρ (g⁻¹ * h * g) y = y := by simpa using mem_levelSpace.1 hy ⟨g⁻¹ * h * g, h_mem⟩
      have h_mul : (k * h).val * g = k.val * g * (g⁻¹ * h * g) := by simp [mul_assoc]
      rw [h_mul, map_mul, End.mul_apply, h_fix]
    rw [h_act]
    simpa using sum_mul_out H (fun k : K ↦ ρ (k * g) y) h_inv
  -- The operator `p` acts as `a` on the forms of every space.
  obtain ⟨p, hp⟩ := D.exists_heckeAlgebra_eq_asAlgebraHom ha
  refine ⟨(h_fin.card : ℂ)⁻¹ • p, fun {s} W z y ↦ ?_⟩
  -- All terms have the same inner product with `z`, as `K` acts unitarily and fixes `z`.
  set π := W.formRep (typeKernel D.paramW s)
  have h_term (k : K) (u : W.Form (typeKernel D.paramW s)) :
      inner ℂ z.val (π k.val u) = inner ℂ z.val u := by
    have h_fix : π k.val z.val = z.val := mem_levelSpace_iff_forall_apply_eq.1 z.prop _
      (inf_trivialOn_le_levelOf ⟨k.prop, k.val.prop⟩)
    rw [← W.inner_formRep k.val z.val u, h_fix]
  have h_sum : inner ℂ z (p.val W y) = h_fin.card * inner ℂ z.val (π γ y) := by
    rw [coe_inner, hp, asAlgebraHom_mapDomain, h_act, inner_sum]
    simp [π, g, h_term]
  exact (inner_smul_right z (p.val W y) _).trans <| by simp [h_sum, Fintype.card_ne_zero]

/-- A term `D.rallisTerm ϑ j W z y i` of Rallis' inner product formula is a vacuum coefficient of
the Weil representation times `⟪z, γ y⟫`, for a representative `γ` of `i`, over the number of
matrices modulo the modulus of the twist. It is a matrix coefficient `⟪z, p y⟫` of a spherical Hecke
operator `p` away from the level `D.M`, the same for all spaces `W`. -/
lemma exists_rallisTerm_eq_inner (ϑ : D.TameChar) (j : ℕ)
    (i : Gf D.E D.RowIndex ⧸ localLevel D.RowIndex (D.twistModulus ϑ 1).places.conjClosureᶜ) :
    ∃ p : D.heckeAlgebra, ∀ {s : D.RowIndex → ℤˣ} (W : Space D.E D.RowIndex s)
      (z y : D.principalForms W), D.rallisTerm ϑ j W z y i = inner ℂ z (p.val W y) := by
  -- The term is a scalar times a matrix coefficient of a representative `γ`, which is supported
  -- away from the places of the modulus, so trivial above `M`.
  let γ : Gf D.E D.RowIndex := SiegelWeil.cosetRep i
  have h_off : γ ∈ D.offLevelGroup := mem_trivialOn.2 fun w ⟨x, hx⟩ ↦ by
    have hw : w ∈ (D.twistModulus ϑ 1).places := (Rows.places_levelModulus ..).ge ⟨.inl x, hx⟩
    simp [γ, mem_supportedOn.1 (SiegelWeil.cosetRep i).prop, hw]
  obtain ⟨p, hp⟩ := D.exists_heckeAlgebra_inner_eq_inner_translate h_off
  let coeff : ℂ := SiegelWeil.vacuumCoeff (Fintype.card (D.Y 1)) (D.descentPair ϑ j).charV γ /
    Fintype.card (D.Y 1 × D.RowIndex → (D.twistModulus ϑ 1).ResidueRing)
  refine ⟨coeff • p, fun {s} W z y ↦ ?_⟩
  calc D.rallisTerm ϑ j W z y i
      = coeff * inner ℂ z.val (W.formRep (typeKernel D.paramW s) γ y) := by
        rw [rallisTerm, SiegelWeil.cosetTerm, mul_div_right_comm]
    _ = inner ℂ z (coeff • p.val W y) := by rw [← hp, inner_smul_right]

variable (V : Space D.E D.RowIndex s) (V' : Space D.E D.RowIndex s')

/-- Let the doubled parameter `D.paramW` have gap `D.gap` for the signs of `V` and of `V'`: at each
infinite place its entries are distinct and have the parity of `card D.RowIndex - 1`, and entries
with different signs are at least `2 * D.gap` apart. Let `D.rallisTerm ϑ j` be the terms of Rallis'
inner product formula for the tame character `ϑ` and the descent pair `D.descentPair ϑ j`. Suppose
that for all forms `z`, `y` of principal level the series of these terms times `a` sums to `B z y`
on `V`, and times `a'` sums to `B' z y` on `V'`. Then one spherical Hecke operator `p` gives
`B z y = a ⟪z, p y⟫` on `V` and `B' z y = a' ⟪z, p y⟫` on `V'`. -/
lemma exists_heckeAlgebra_eq_mul_inner_of_hasSum_rallisTerm
    [hs : ∀ v : D.Φ, (toHCParam s (D.paramW v)).HasGap D.gap]
    [hs' : ∀ v : D.Φ, (toHCParam s' (D.paramW v)).HasGap D.gap]
    (ϑ : D.TameChar) (j : ℕ) {a a' : ℂ}
    {B : D.principalForms V → D.principalForms V → ℂ}
    {B' : D.principalForms V' → D.principalForms V' → ℂ}
    (hB : ∀ z y : D.principalForms V, HasSum
      (fun i : Gf D.E D.RowIndex ⧸ localLevel D.RowIndex (D.twistModulus ϑ 1).places.conjClosureᶜ ↦
        a * D.rallisTerm ϑ j V z y i) (B z y))
    (hB' : ∀ z y : D.principalForms V', HasSum
      (fun i : Gf D.E D.RowIndex ⧸ localLevel D.RowIndex (D.twistModulus ϑ 1).places.conjClosureᶜ ↦
        a' * D.rallisTerm ϑ j V' z y i) (B' z y)) :
    ∃ p : D.heckeAlgebra,
      (∀ z y : D.principalForms V, B z y = a * inner ℂ z (p.val V y)) ∧
      ∀ z y : D.principalForms V', B' z y = a' * inner ℂ z (p.val V' y) := by
  -- The pairs `(a ⟪z, p y⟫, a' ⟪z, p y⟫)` of functions of `z`, `y` with one `p` in `D.heckeAlgebra`
  -- make a finite-dimensional, hence closed, subspace `N`; it contains every pair of terms of the
  -- two series, so it contains the pair of sums.
  -- `matrixCoeff W` sends an operator `T` to its matrix coefficients `(z, y) ↦ ⟪z, T y⟫`.
  let matrixCoeff {s : D.RowIndex → ℤˣ} (W : Space D.E D.RowIndex s) :
      End ℂ (D.principalForms W) →ₗ[ℂ] D.principalForms W → D.principalForms W → ℂ :=
    .pi fun z ↦ .pi fun y ↦ innerₛₗ ℂ z ∘ₗ applyₗ y
  let ev {s : D.RowIndex → ℤˣ} (W : Space D.E D.RowIndex s) :
      D.heckeAlgebra →ₗ[ℂ] End ℂ (D.principalForms W) :=
    { toFun p := p.val W, map_add' _ _ := rfl, map_smul' _ _ := rfl }
  let pairs := range ((ev V).prod (ev V'))
  let N := pairs.map ((a • matrixCoeff V).prodMap (a' • matrixCoeff V'))
  -- Finiteness is given explicitly, as instance search for it is too slow on these types.
  have : Module.Finite ℂ (End ℂ (D.principalForms V)) := Module.Finite.linearMap ℂ ℂ _ _
  have : Module.Finite ℂ (End ℂ (D.principalForms V')) := Module.Finite.linearMap ℂ ℂ _ _
  have : Module.Finite ℂ pairs := FiniteDimensional.finiteDimensional_submodule pairs
  have : Module.Finite ℂ N := Module.Finite.map pairs _
  have h_term (i : Gf D.E D.RowIndex ⧸ localLevel D.RowIndex
    (D.twistModulus ϑ 1).places.conjClosureᶜ) :
      (fun z y ↦ a * D.rallisTerm ϑ j V z y i, fun z y ↦ a' * D.rallisTerm ϑ j V' z y i) ∈ N := by
    obtain ⟨p, hp⟩ := D.exists_rallisTerm_eq_inner ϑ j i
    refine mem_map.2 ⟨(p.val V, p.val V'), mem_range.2 ⟨p, by simp [ev]⟩, ?_⟩
    ext <;> simp [matrixCoeff, hp]
  have h_sum : HasSum (fun i ↦ (fun z y ↦ a * D.rallisTerm ϑ j V z y i,
      fun z y ↦ a' * D.rallisTerm ϑ j V' z y i)) (B, B') :=
    (Pi.hasSum.2 fun z ↦ Pi.hasSum.2 (hB z)).prodMk (Pi.hasSum.2 fun z ↦ Pi.hasSum.2 (hB' z))
  have h_mem : (B, B') ∈ N := N.closed_of_finiteDimensional.mem_of_tendsto h_sum
    (.of_forall fun t ↦ sum_mem fun i _ ↦ h_term i)
  obtain ⟨T, h_hecke, h_image⟩ := h_mem
  obtain ⟨p, hp⟩ : ∃ p : D.heckeAlgebra, (ev V).prod (ev V') p = T := mem_range.1 h_hecke
  obtain ⟨hB_eq, hB'_eq⟩ :
      a • matrixCoeff V (p.val V) = B ∧ a' • matrixCoeff V' (p.val V') = B' := by
    rw [← hp] at h_image
    simpa [ev] using h_image
  refine ⟨p, fun z y ↦ ?_, fun z y ↦ ?_⟩
  · simp [← hB_eq, matrixCoeff]
  · simp [← hB'_eq, matrixCoeff]

open scoped Classical in
/-- Let the parameter `D.paramW` have gap `D.gap` for the signs of `V`. As `e₀` projects onto the
good forms and is the sum of the idempotents `e_c = tupleIdem D.RowIndex c` of the good families `c`
of labels, the trace of a spherical Hecke operator `T` on good forms is the sum of the traces of
`T e_c` on all forms of principal level. -/
lemma trace_heckeOnGood_eq_sum [hs : ∀ v : D.Φ, (toHCParam s (D.paramW v)).HasGap D.gap]
    (T : D.heckeAlgebra) :
    trace ℂ (D.goodForms V) (D.heckeOnGood V T) = ∑ c ∈ D.goodTupleFamilies,
      trace ℂ (D.principalForms V)
        (T.val V * (D.principalRep V).asAlgebraHom (tupleIdem D.RowIndex c)) := by
  set e : End ℂ (D.principalForms V) := (D.principalRep V).asAlgebraHom D.e₀ with he
  have he_idem : IsIdempotentElem e := D.isCentralProj_e₀.1.map (D.principalRep V).asAlgebraHom
  -- The good forms are the range of `e`, so `T e` agrees with `T` on them.
  have h_maps (y : D.principalForms V) : (T.val V * e) y ∈ D.goodForms V :=
    (D.heckeOnGood V T ⟨e y, mem_range_self e y⟩).prop
  have h_restrict : D.heckeOnGood V T = (T.val V * e).restrict fun y _ ↦ h_maps y := by
    ext y : 2
    simp [coe_heckeOnGood_apply, he_idem.mem_range_iff.mp y.prop]
  rw [h_restrict, trace_restrict_eq_of_forall_mem _ _ h_maps]
  simp [he, e₀, Finset.mul_sum]

open scoped Classical in
/-- Let the doubled parameter `D.paramW` have gap `D.gap` for the signs of `V` and of `V'`: at each
infinite place its entries are distinct and have the parity of `card D.RowIndex - 1`, and entries
with different signs are at least `2 * D.gap` apart. Let `c` be a good family of
labels: a polynomial `c x` of degree `r = card D.RowIndex` over the residue field of each chosen
place `x`, subject to the conditions of `D.goodTupleFamilies`. The product of the label idempotents
of the `c x` is an idempotent `e_c = tupleIdem D.RowIndex c` in the group algebra of the product of
the finite groups `GL_r`. For a spherical Hecke operator `T`, the operator `T e_c` has the same
trace on the forms of principal level of `V` and of `V'`: its test function is cuspidal at a place
`x` where the polynomial `c x` is primitive. -/
lemma trace_mul_tupleIdem_eq [hs : ∀ v : D.Φ, (toHCParam s (D.paramW v)).HasGap D.gap]
    [hs' : ∀ v : D.Φ, (toHCParam s' (D.paramW v)).HasGap D.gap] (T : D.heckeAlgebra)
    {c : ∀ x : (i : Fin 2) × D.ChosenPlace i, Polynomial (ResField (D.chosenPlace x))}
    (hc : c ∈ D.goodTupleFamilies) :
    trace ℂ (D.principalForms V)
        (T.val V * (D.principalRep V).asAlgebraHom (tupleIdem D.RowIndex c)) =
      trace ℂ (D.principalForms V')
        (T.val V' * (D.principalRep V').asAlgebraHom (tupleIdem D.RowIndex c)) := by
  obtain ⟨a, ha, hT⟩ : ∃ a ∈ D.sphericalAlgebra,
      ∀ {s : D.RowIndex → ℤˣ} (W : Space D.E D.RowIndex s) (y : D.principalForms W),
        (T.val W y).val = (W.formRep (typeKernel D.paramW s)).asAlgebraHom
          (mapDomain D.offLevelGroup.subtype a) y := T.prop
  obtain ⟨x, h_label, h_irr, -⟩ := D.exists_isPrimitivePolynomial hc
  -- The element `f` of the group algebra of the finite points acts as `T e_c` on every space.
  let f : ℂ[Gf D.E D.RowIndex] :=
    mapDomain D.offLevelGroup.subtype a * D.liftGroupAlgebra (tupleIdem D.RowIndex c)
  have hf_mem : f ∈ universalLevelAlgebra D.chosenLevel :=
    mul_mem (D.mem_sphericalAlgebra.1 ha) (D.liftGroupAlgebra_mem_universalLevelAlgebra _)
  have hf_acts {s : D.RowIndex → ℤˣ} (W : Space D.E D.RowIndex s) (y : D.principalForms W) :
      ((T.val W * (D.principalRep W).asAlgebraHom (tupleIdem D.RowIndex c)) y).val =
        (W.formRep (typeKernel D.paramW s)).asAlgebraHom f y := by
    rw [End.mul_apply, hT, coe_principalRep_asAlgebraHom_apply, map_mul, End.mul_apply]
  have h_rank : 2 ≤ Fintype.card D.RowIndex := D.nat_le_of_hasLogBound
  have h_gap : gapThreshold D.RowIndex (10 * Fintype.card D.RowIndex ^ 5) ≤ D.gap :=
    D.nat_le_of_hasLogBound
  have h_cusp : IsCuspidalAt (D.isConjApart_chosenPlace.star_ne x x)
      (convIndicator isOpen_levelOf (IsLevel.isCompact (K := D.chosenLevel)) f) :=
    isCuspidalAt_convIndicator_tupleIdem h_label h_irr _
  exact trace_eq_of_isCuspidalAt D.f_even h_rank V V' (fun v ↦ (hs v).mono h_gap)
    (fun v ↦ (hs' v).mono h_gap) hf_mem _ h_cusp (hf_acts V) (hf_acts V')

/-- Let the parameter `D.paramW` have gap `D.gap` for the signs of `V` and of `V'`. Then a spherical
Hecke operator away from `M` has the same trace on the good forms of `V` and of `V'`. -/
theorem trace_heckeOnGood_eq [hs : ∀ v : D.Φ, (toHCParam s (D.paramW v)).HasGap D.gap]
    [hs' : ∀ v : D.Φ, (toHCParam s' (D.paramW v)).HasGap D.gap] (T : D.heckeAlgebra) :
    trace ℂ (D.goodForms V) (D.heckeOnGood V T) =
      trace ℂ (D.goodForms V') (D.heckeOnGood V' T) := by
  simp only [trace_heckeOnGood_eq_sum]
  exact Finset.sum_congr rfl fun c hc ↦ D.trace_mul_tupleIdem_eq V V' T hc

/-- Let the parameter `D.paramW` have gap `D.gap` for the signs of `V` and of `V'`. Then a spherical
Hecke operator away from `M` has the same characteristic polynomial on the good forms of `V` and of
`V'`, as the traces of all its powers agree. -/
theorem charpoly_heckeOnGood_eq [hs : ∀ v : D.Φ, (toHCParam s (D.paramW v)).HasGap D.gap]
    [hs' : ∀ v : D.Φ, (toHCParam s' (D.paramW v)).HasGap D.gap] (T : D.heckeAlgebra) :
    (D.heckeOnGood V T).charpoly = (D.heckeOnGood V' T).charpoly := by
  exact charpoly_eq_of_trace_pow_eq fun l ↦ by
    rw [← map_pow, ← map_pow, D.trace_heckeOnGood_eq V V']

/-- Let the parameter `D.paramW` have gap `D.gap` for the signs of `V` and of `V'`. Then a spherical
Hecke operator away from `M` has the same determinant on the good forms of `V` and of `V'`. -/
theorem det_heckeOnGood_eq [hs : ∀ v : D.Φ, (toHCParam s (D.paramW v)).HasGap D.gap]
    [hs' : ∀ v : D.Φ, (toHCParam s' (D.paramW v)).HasGap D.gap] (T : D.heckeAlgebra) :
    (D.heckeOnGood V T).det = (D.heckeOnGood V' T).det := by
  rw [det_eq_sign_charpoly_coeff, det_eq_sign_charpoly_coeff, ← charpoly_natDegree,
    ← charpoly_natDegree, D.charpoly_heckeOnGood_eq V V']

/-- Let the parameter `D.paramW` have gap `D.gap` for the signs of `V` and of `V'`. One spherical
Hecke operator acts on the forms of principal level of both spaces as `D.rallisOperator ϑ j`, the
operator whose matrix coefficient `⟪z, R y⟫` is the series of Rallis' formula for the tame
character `ϑ` and the descent pair `D.descentPair ϑ j` without its normalisation: the sum over the
cosets `i` of `N` times `D.rallisTerm ϑ j V z y i`, where `N` is the number of matrices over the
residue ring of `D.twistModulus ϑ 1` with rows `D.Y 1` and columns `D.RowIndex`. -/
theorem exists_hecke_eq_rallisOperator [hs : ∀ v : D.Φ, (toHCParam s (D.paramW v)).HasGap D.gap]
    [hs' : ∀ v : D.Φ, (toHCParam s' (D.paramW v)).HasGap D.gap] (ϑ : D.TameChar) (j : ℕ) :
    ∃ p : D.heckeAlgebra,
      p.val V = D.rallisOperator ϑ j V ∧ p.val V' = D.rallisOperator ϑ j V' := by
  let N : ℂ := Fintype.card (D.Y 1 × D.RowIndex → (D.twistModulus ϑ 1).ResidueRing)
  -- The terms `rallisTerm` are those of the series divided by `N`.
  have h_sum {s : D.RowIndex → ℤˣ} (W : Space D.E D.RowIndex s) (z y : D.principalForms W) :
      HasSum (fun i ↦ N * D.rallisTerm ϑ j W z y i) (inner ℂ z (D.rallisOperator ϑ j W y)) :=
    (D.hasSum_inner_rallisOperator ϑ j W z y).congr_fun fun i ↦ mul_div_cancel₀ _ NeZero.out
  obtain ⟨p, hp, hp'⟩ := D.exists_heckeAlgebra_eq_mul_inner_of_hasSum_rallisTerm V V' ϑ j (h_sum V)
    (h_sum V')
  refine ⟨N • p, LinearMap.ext fun y ↦ ext_inner_left ℂ fun z ↦ ?_,
    LinearMap.ext fun y ↦ ext_inner_left ℂ fun z ↦ ?_⟩
  · exact (inner_smul_right z (p.val V y) N).trans (hp z y).symm
  · exact (inner_smul_right z (p.val V' y) N).trans (hp' z y).symm

/-- Let the parameter `D.paramW` have gap `D.gap` for the signs of `V`. The series of Rallis'
formula (`New.Data.rallisOperator`) preserves the good forms of `V`, as it acts as a spherical Hecke
operator. This is its restriction to the good forms. -/
noncomputable def rallisOnGood [hs : ∀ v : D.Φ, (toHCParam s (D.paramW v)).HasGap D.gap]
    (ϑ : D.TameChar) (j : ℕ) : End ℂ (D.goodForms V) :=
  (D.rallisOperator ϑ j V).restrict fun y hy ↦ by
    obtain ⟨p, hp, -⟩ := D.exists_hecke_eq_rallisOperator V V ϑ j
    rw [← hp]
    exact (D.heckeOnGood V p ⟨y, hy⟩).prop

lemma coe_rallisOnGood_apply [hs : ∀ v : D.Φ, (toHCParam s (D.paramW v)).HasGap D.gap]
    (ϑ : D.TameChar) (j : ℕ) (y : D.goodForms V) :
    (D.rallisOnGood V ϑ j y : D.principalForms V) = D.rallisOperator ϑ j V y :=
  rfl

/-- Let `V`, `V'` be hermitian spaces with signs `s`, `s'`, and let the parameter `D.paramW` have
gap `D.gap` for both. Let `D.rallisOnGood V ϑ j` be the series of Rallis' formula for the tame
character `ϑ` and the descent pair `D.descentPair ϑ j`, restricted to the good forms of `V`. It has
the same determinant as the corresponding operator on the good forms of `V'`. -/
theorem det_rallisOnGood_eq [hs : ∀ v : D.Φ, (toHCParam s (D.paramW v)).HasGap D.gap]
    [hs' : ∀ v : D.Φ, (toHCParam s' (D.paramW v)).HasGap D.gap] (ϑ : D.TameChar) (j : ℕ) :
    (D.rallisOnGood V ϑ j).det = (D.rallisOnGood V' ϑ j).det := by
  obtain ⟨p, hp, hp'⟩ := D.exists_hecke_eq_rallisOperator V V' ϑ j
  have h_good {t : D.RowIndex → ℤˣ} (W : Space D.E D.RowIndex t)
      [ht : ∀ v : D.Φ, (toHCParam t (D.paramW v)).HasGap D.gap]
      (hW : p.val W = D.rallisOperator ϑ j W) : D.rallisOnGood W ϑ j = D.heckeOnGood W p := by
    ext y : 2
    rw [coe_rallisOnGood_apply, coe_heckeOnGood_apply, hW]
  rw [h_good V hp, h_good V' hp', D.det_heckeOnGood_eq V V']

open scoped Classical in
/-- Let `V` be a hermitian space with signs `s`, such that for each `v : D.Φ` the doubled parameter
`toHCParam s (D.paramW v)` has gap `D.gap` (`HasGap`). If `T` in `D.heckeAlgebra`, a spherical Hecke
operator away from the level, is `1` on `D.eigenPart V q` and `0` on `D.eigenPart V d` for `d ≠ q`,
then its trace on the good forms is the dimension of the good forms in `D.eigenPart V q`. -/
lemma trace_heckeOnGood_eq_finrank [hs : ∀ v : D.Φ, (toHCParam s (D.paramW v)).HasGap D.gap]
    {T : D.heckeAlgebra} {q : FinPlace D.E × ℕ → ℂ}
    (hT : ∀ d : FinPlace D.E × ℕ → ℂ, ∀ y ∈ D.eigenPart V d, T.val V y = if d = q then y else 0) :
    trace ℂ (D.goodForms V) (D.heckeOnGood V T) =
      finrank ℂ (D.goodForms V ⊓ D.eigenPart V q : Submodule ℂ (D.principalForms V)) := by
  -- `T` maps each eigenpart into the `q`-part, and the eigenparts span.
  have h_le : ⨆ d, D.eigenPart V d ≤ (D.eigenPart V q).comap (T.val V) := by
    refine iSup_le fun d y hy ↦ ?_
    rw [mem_comap, hT d y hy]
    aesop
  have h_proj : IsProj ((D.goodForms V ⊓ D.eigenPart V q).comap (D.goodForms V).subtype)
      (D.heckeOnGood V T) := by
    refine ⟨fun y ↦ mem_inf.2 ⟨(D.heckeOnGood V T y).prop,
      h_le ((D.iSup_eigenPart_eq_top V).ge mem_top)⟩,
      fun y ⟨_, hy_eigen⟩ ↦ Subtype.ext ?_⟩
    rw [coe_heckeOnGood_apply, hT q y hy_eigen, ite_eq_left rfl]
  rw [h_proj.trace, (comapSubtypeEquivOfLe inf_le_left).finrank_eq]

/-- Let `V`, `V'` be hermitian spaces with signs `s`, `s'`, which may differ, and let the parameter
`D.paramW` have gap `D.gap` for both. For each eigensystem `q`, the good forms with eigensystem `q`
on `V` and on `V'` make up spaces of the same dimension. -/
theorem finrank_goodForms_inf_eigenPart_eq
    [hs : ∀ v : D.Φ, (toHCParam s (D.paramW v)).HasGap D.gap]
    [hs' : ∀ v : D.Φ, (toHCParam s' (D.paramW v)).HasGap D.gap] (q : FinPlace D.E × ℕ → ℂ) :
    finrank ℂ (D.goodForms V ⊓ D.eigenPart V q : Submodule ℂ (D.principalForms V)) =
      finrank ℂ (D.goodForms V' ⊓ D.eigenPart V' q : Submodule ℂ (D.principalForms V')) := by
  classical
  -- Finitely many eigensystems occur for `V` or `V'`, and one Hecke operator projects both spaces
  -- of forms onto their `q`-parts.
  let F : Finset (FinPlace D.E × ℕ → ℂ) :=
    ((D.finite_setOf_inf_eigenPart_ne_bot V ⊤).union
      (D.finite_setOf_inf_eigenPart_ne_bot V' ⊤)).toFinset
  obtain ⟨T, hT⟩ := D.exists_hecke_proj_eigenPart q F
  -- `T` acts as the projection also on the eigenparts outside `F`, as these are zero.
  have h_proj {s : D.RowIndex → ℤˣ} (W : Space D.E D.RowIndex s)
      (hF : ∀ d ∉ F, D.eigenPart W d = ⊥) (d : FinPlace D.E × ℕ → ℂ) :
      ∀ y ∈ D.eigenPart W d, T.val W y = if d = q then y else 0 := fun y hy ↦ by
    by_cases hd : d ∈ F
    · exact hT d (Finset.mem_insert_of_mem hd) y hy
    · simp [(Submodule.mem_bot ℂ).1 ((hF d hd).le hy)]
  have h_trace := D.trace_heckeOnGood_eq V V' T
  rw [D.trace_heckeOnGood_eq_finrank V (h_proj V (by simp +contextual [F, top_inf_eq])),
    D.trace_heckeOnGood_eq_finrank V' (h_proj V' (by simp +contextual [F, top_inf_eq]))] at h_trace
  exact_mod_cast h_trace

/-- Let the parameter `D.paramW` have gap `D.gap` for the signs of `V` and of `V'`. An eigensystem
`q` that does not occur in the good forms of `V'` does not occur in those of `V`. -/
lemma goodForms_inf_eigenPart_eq_bot_of_eq_bot
    [hs : ∀ v : D.Φ, (toHCParam s (D.paramW v)).HasGap D.gap]
    [hs' : ∀ v : D.Φ, (toHCParam s' (D.paramW v)).HasGap D.gap] {q : FinPlace D.E × ℕ → ℂ}
    (h_bot : D.goodForms V' ⊓ D.eigenPart V' q = ⊥) : D.goodForms V ⊓ D.eigenPart V q = ⊥ := by
  rw [← finrank_eq_zero, D.finrank_goodForms_inf_eigenPart_eq V V', h_bot, finrank_bot]

/-- For `1 ≤ j ≤ m` the good forms on `W_j = D.spaceW j` have dimension `D.targetDim`, which is the
dimension of the good forms on `Y_0 = D.spaceY 0`: the identity has the same trace on both. -/
theorem targetDim_eq_finrank_goodForms_spaceW (j : D.LiftIndex) :
    D.targetDim = finrank ℂ (D.goodForms (D.spaceW j)) := by
  simpa [trace_one] using D.trace_heckeOnGood_eq (D.spaceY 0) (D.spaceW j) 1

end Data

end New
