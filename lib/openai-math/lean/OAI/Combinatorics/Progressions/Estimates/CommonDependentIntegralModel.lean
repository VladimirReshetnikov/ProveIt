import OAI.Combinatorics.Progressions.Fourier.CommonDependentWordFrequency
import OAI.Combinatorics.Progressions.Linear.BoundedRankIntegralModel

namespace OAI

section

namespace Erdos3

open Module

variable {I L : Type*} [Fintype I] [LieRing L] [LieAlgebra ℚ L]

noncomputable def finiteMarkedLieValues (v : I → L) (w : I → ℕ) (marked : I → Bool)
    (s d k l : ℕ) : Finset L := by
  classical
  exact ((finiteLieTrees I s).filter (fun a => d ≤ lieTreeWeight w a ∧
    k ≤ lieTreeMarkedCount marked a ∧ l ≤ a.length)).image (lieTreeEval v)

theorem finiteMarkedLieValues_mem (v : I → L) (w : I → ℕ) (marked : I → Bool)
    (s d k l : ℕ) {x : L} (hx : x ∈ finiteMarkedLieValues v w marked s d k l) :
    x ∈ markedLieSpan v w marked d k l := by
  classical
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨_, hd, hk, hl⟩ := Finset.mem_filter.mp ha
  exact Submodule.subset_span ⟨a, hd, hk, hl, rfl⟩

theorem markedLieSpan_eq_finite_span {s r : ℕ} (F : DegreeRankLieFiltration L s r)
    (v : I → L) (w : I → ℕ) (marked : I → Bool) (hw : ∀ i, 0 < w i)
    (hv : ∀ i, v i ∈ F.layer (w i) 1) (d k l : ℕ) :
    markedLieSpan v w marked d k l =
      Submodule.span ℚ (finiteMarkedLieValues v w marked s d k l : Set L) := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨a, hd, hk, hl, rfl⟩
    by_cases ha : a.length ≤ s
    · exact Submodule.subset_span (Finset.mem_image.mpr ⟨a,
        Finset.mem_filter.mpr ⟨mem_finiteLieTrees_of_length_le I a ha, hd, hk, hl⟩, rfl⟩)
    · have hweight := lieTree_length_le_weight w hw a
      have hzero := F.lieTreeEval_mem_length v w hv a
      rw [F.layer_eq_bot_of_past_top (Or.inl (by omega)), Submodule.mem_bot] at hzero
      rw [hzero]
      exact Submodule.zero_mem _
  · exact Submodule.span_le.mpr (fun _ hx => finiteMarkedLieValues_mem v w marked s d k l hx)

omit [LieAlgebra ℚ L] in
theorem finiteMarkedLieValues_card_le (v : I → L) (w : I → ℕ) (marked : I → Bool)
    (s d k l : ℕ) :
    (finiteMarkedLieValues v w marked s d k l).card ≤ (Fintype.card I + 2) ^ (3 ^ s) := by
  classical
  exact (Finset.card_image_le.trans (Finset.card_filter_le _ _)).trans (finiteLieTrees_card_le I s)

theorem finiteMarkedLieValues_coordinate_height {ι : Type*} [Fintype ι]
    (b : Basis ι ℚ L) (v : I → L) (w : I → ℕ) (marked : I → Bool) {H : ℕ}
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants b i j k) H)
    (hv : ∀ i j, RationalHeightLE (b.repr (v i) j) H) (s d k l : ℕ)
    {x : L} (hx : x ∈ finiteMarkedLieValues v w marked s d k l) (j : ι) :
    RationalHeightLE (b.repr x j) (lieTreeHeight (Fintype.card ι) H s) := by
  classical
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
  exact finiteLieTrees_coordinate_height b v hc hv s a (Finset.mem_filter.mp ha).1 j

theorem exists_markedLieSpan_bounded_basis {ι : Type*} [Fintype ι] {s r : ℕ}
    (F : DegreeRankLieFiltration L s r) (b : Basis ι ℚ L)
    (v : I → L) (w : I → ℕ) (marked : I → Bool) (hw : ∀ i, 0 < w i)
    (hv : ∀ i, v i ∈ F.layer (w i) 1) {H : ℕ}
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants b i j k) H)
    (hgen : ∀ i j, RationalHeightLE (b.repr (v i) j) H) (d k l : ℕ) :
    ∃ e : Basis (Fin (finrank ℚ (markedLieSpan v w marked d k l))) ℚ
      (markedLieSpan v w marked d k l),
      ∀ i j, RationalHeightLE (b.repr (e i : L) j) (lieTreeHeight (Fintype.card ι) H s) := by
  let S := finiteMarkedLieValues v w marked s d k l
  have hspan : Submodule.span ℚ (Set.range (Subtype.val : S → L)) =
      markedLieSpan v w marked d k l := by
    rw [markedLieSpan_eq_finite_span F v w marked hw hv]
    congr 1
    ext x
    exact ⟨fun ⟨y, hy⟩ => hy ▸ y.property, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
  exact exists_bounded_submodule_basis_from_spanning b _ (Subtype.val : S → L) hspan
    (fun x j => finiteMarkedLieValues_coordinate_height b v w marked hc hgen s d k l x.property j)

end Erdos3

end

section

namespace Erdos3.NativeRankRelation.CommonData

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

theorem dependentWordLayer_inf (d k l e m n : ℕ) :
    D.dependentWordLayer d k l ⊓ D.dependentWordLayer e m n =
      D.dependentWordLayer (max d e) (max k m) (max l n) :=
  FreeDegreeRankLieAlgebra.markedLayer_inf D.CoefficientAlphabet s r D.coefficientWeight
    D.coefficientWeight_pos D.coefficientIsDependent W.rank.filtration.rank_le_degree d k l e m n

theorem top_inter_dependentWordIdeal (k : ℕ) :
    D.coefficientFreeFiltration.layer s r ⊓ (D.dependentWordIdeal 0 k 0).toSubmodule =
      D.dependentWordLayer s k r :=
  FreeDegreeRankLieAlgebra.topLayer_inter_markedIdeal D.CoefficientAlphabet s r D.coefficientWeight
    D.coefficientWeight_pos D.coefficientIsDependent W.rank.filtration.rank_le_degree k

variable {Q : ℝ} (B : D.CoefficientBases Q)

theorem CoefficientBases.top_inter_dependentWordIdeal_le_ker :
    D.coefficientFreeFiltration.layer s r ⊓ (D.dependentWordIdeal 0 2 0).toSubmodule ≤
      (B.freeFrequency D).ker := by
  rw [D.top_inter_dependentWordIdeal]
  exact B.dependentWordLayer_top_le_ker D

theorem CoefficientBases.exists_dependent_word_quotient_frequency :
    ∃ ξ : (D.CoefficientFreeLieAlgebra ⧸ (D.dependentWordIdeal 0 2 0).toSubmodule) →ₗ[ℚ] ℚ,
      ∀ x ∈ D.coefficientFreeFiltration.layer s r,
        ξ ((D.dependentWordIdeal 0 2 0).toSubmodule.mkQ x) = B.freeFrequency D x :=
  exists_quotient_functional_preserving_subspace (D.coefficientFreeFiltration.layer s r)
    (D.dependentWordIdeal 0 2 0).toSubmodule (B.freeFrequency D)
    (B.top_inter_dependentWordIdeal_le_ker D)

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3

theorem lieQuotient_mapIdeal_abelian {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    (J K : LieIdeal ℚ L) (hK : ∀ a ∈ K, ∀ b ∈ K, ⁅a, b⁆ ∈ J)
    {x y : L ⧸ J} (hx : x ∈ K.map (lieQuotientMap J)) (hy : y ∈ K.map (lieQuotientMap J)) :
    ⁅x, y⁆ = 0 := by
  obtain ⟨a, rfl⟩ := LieIdeal.mem_map_of_surjective
    (f := lieQuotientMap J) (I := K) (lieQuotientMap_surjective J) hx
  obtain ⟨b, rfl⟩ := LieIdeal.mem_map_of_surjective
    (f := lieQuotientMap J) (I := K) (lieQuotientMap_surjective J) hy
  exact ((lieQuotientMap J).map_lie a.val b.val).symm.trans
    ((lieQuotientMap_eq_zero J ⁅a.val, b.val⁆).mpr (hK a.val a.property b.val b.property))

end Erdos3

namespace Erdos3.NativeRankRelation.CommonData

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

abbrev DependentQuotient := D.CoefficientFreeLieAlgebra ⧸ D.dependentWordIdeal 0 2 0

noncomputable def dependentQuotientMap : D.CoefficientFreeLieAlgebra →ₗ⁅ℚ⁆ D.DependentQuotient :=
  lieQuotientMap (D.dependentWordIdeal 0 2 0)

noncomputable def dependentQuotientFiltration : DegreeRankLieFiltration D.DependentQuotient s r :=
  D.coefficientFreeFiltration.quotientLie (D.dependentWordIdeal 0 2 0)
    D.coefficientFreeFiltration.rank_le_degree (by
      rw [D.coefficientFreeFiltration.terminal]
      exact bot_le)

theorem dependentQuotientMap_mem_layer {d i : ℕ} {x : D.CoefficientFreeLieAlgebra}
    (hx : x ∈ D.coefficientFreeFiltration.layer d i) :
    D.dependentQuotientMap x ∈ D.dependentQuotientFiltration.layer d i := ⟨x, hx, rfl⟩

noncomputable def dependentQuotientLinearIdeal : LieIdeal ℚ D.DependentQuotient :=
  (D.dependentWordIdeal 0 1 0).map D.dependentQuotientMap

theorem dependentQuotientLinearIdeal_abelian {x y : D.DependentQuotient}
    (hx : x ∈ D.dependentQuotientLinearIdeal) (hy : y ∈ D.dependentQuotientLinearIdeal) :
    ⁅x, y⁆ = 0 := by
  exact lieQuotient_mapIdeal_abelian (D.dependentWordIdeal 0 2 0) (D.dependentWordIdeal 0 1 0)
    (fun _ ha _ hb => D.dependentWordLayer_lie_mem
      (d := 0) (e := 0) (k := 1) (m := 1) (l := 0) (n := 0) ha hb) hx hy

theorem CoefficientBases.exists_dependentQuotient_top_frequency {Q : ℝ} (B : D.CoefficientBases Q) :
    ∃ ξ : D.DependentQuotient →ₗ[ℚ] ℚ,
      ∀ x ∈ D.coefficientFreeFiltration.layer s r, ξ (D.dependentQuotientMap x) = B.freeFrequency D x :=
  B.exists_dependent_word_quotient_frequency D

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module NilpotentLieBCHGroup RationalFilteredNilmanifold
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_uniform_dependentQuotient_comparison (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {b p q P M Q : ℝ}
      {W : NativeDegreeRankFamily s (r + 1) (ZMod N) b} {out : Fin W.outputDim}
      {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q}
      (D : R.CommonData P) (B : D.CoefficientBases M)
      {d e : ℕ} (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s d)
      (F : RationalFilteredNilmanifold D.DependentQuotient s e)
      (T : E.DegreeRankStructure (r + 1)) (S : F.DegreeRankStructure (r + 1))
      [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
      [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
      [TopologicalSpace (ℝ ⊗[ℚ] D.DependentQuotient)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.DependentQuotient)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.DependentQuotient)]
      [T2Space (ℝ ⊗[ℚ] D.DependentQuotient)]
      (I J σ : Type) [Fintype I] [Fintype J]
      (V : E.UnitVerticalObservable (T.realSubgroup s (r + 1)) I Q)
      (U : F.UnitVerticalObservable (S.realSubgroup s (r + 1)) J Q)
      (hmap : E.lattice ≤ F.lattice.comap (mapOfSteps
        (hL := E.filtration.lowerCentralSeries_eq_bot)
        (hM := F.filtration.lowerCentralSeries_eq_bot) D.dependentQuotientMap)),
      T.filtration = D.coefficientFreeFiltration →
      S.filtration = D.dependentQuotientFiltration →
      0 ≤ Q → T.ComplexityLE Q → S.ComplexityLE Q →
      (∀ i j, rationalLogHeight (F.basis.repr (D.dependentQuotientMap (E.basis j)) i) ≤ Q) →
      V.frequency = B.freeFrequency D →
      (∀ x ∈ D.coefficientFreeFiltration.layer s (r + 1),
        U.frequency (D.dependentQuotientMap x) = B.freeFrequency D x) →
      ∀ w : σ → ℕ,
        E.HasUniformLowerRankUnitFamily T
          (mapDifferenceObservable V U D.dependentQuotientMap hmap) w ((Q + C) ^ C) := by
  obtain ⟨C, hC, hcomparison⟩ := exists_uniform_lower_rank_map_difference s
  refine ⟨C, hC, ?_⟩
  intro r N _ b p q P M Q W out H R D B d e E F T S _ _ _ _ _ _ _ _
    I J σ _ _ V U hmap hT hS hQ hTc hSc hentries hV hU w
  apply hcomparison E F T S D.dependentQuotientMap hmap V U hQ hTc hSc hentries
  · intro x hx
    rw [hS]
    apply D.dependentQuotientMap_mem_layer
    rwa [hT] at hx
  · intro x hx
    rw [hT] at hx
    rw [hV]
    exact (hU x hx).symm

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P Q : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H₀ : Finset (ZMod N)} {R : NativeRankRelation W out H₀ p q} (D : R.CommonData P)
  (B : D.CoefficientBases Q) {n : ℕ}
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s n)
  (T : E.DegreeRankStructure r) (hT : T.filtration = D.coefficientFreeFiltration)
  {H : ℕ} (hH : 1 ≤ H)
  (hbracket : ∀ i j k, RationalHeightLE (lieStructureConstants E.basis i j k) H)
  (hdegree : ∀ i a j, RationalHeightLE (E.basis.repr (E.layerBasis i a).val j) H)
  (hrank : ∀ i j a k, RationalHeightLE (E.basis.repr (T.basis i j a).val k) H)
  (hgen : ∀ i j, RationalHeightLE (E.basis.repr (D.coefficientFreeGenerator i) j) H)
  (hfreq : ∀ i, RationalHeightLE (B.freeFrequency D (E.basis i)) H)

include T hT hH hbracket hdegree hrank hgen hfreq in
theorem CoefficientBases.exists_dependentQuotient_integral_model (l : ℕ) (hl : 0 < l) :
    ∃ m : ℕ, m ≤ n ∧ ∃ d : ℕ, d ≤ n ∧ ∃ u : ℕ, u ≤ d ∧
      let K := rankQuotientHeight n m d u (lieTreeHeight n H s)
      ∃ G : RationalFilteredNilmanifold D.DependentQuotient s d,
        ∃ S : G.DegreeRankStructure r,
          S.filtration = D.dependentQuotientFiltration ∧
          l ∣ G.grid ∧
          G.grid ≤ bchIntegralDenominatorBound s * K ^ (d ^ 3) * (l * K ^ d) ∧
          bchSubgroupCoordinates G.basis G.lattice = scaledIntegerGrid G.grid ∧
          (∀ i j, RationalHeightLE (G.basis.repr (D.dependentQuotientMap (E.basis j)) i) K) ∧
          ∃ ξ : D.DependentQuotient →ₗ[ℚ] ℚ,
            (∀ x ∈ D.coefficientFreeFiltration.layer s r,
              ξ (D.dependentQuotientMap x) = B.freeFrequency D x) ∧
            (∀ i, RationalHeightLE (ξ (G.basis i)) K) ∧
            (∀ z : G.filtration.Group, z ∈ G.lattice → ∃ a : ℤ, ξ z.coord = a) ∧
            ∀ v : ℝ, (d : ℝ) ≤ v → (G.grid : ℝ) ≤ Real.exp v →
              (K : ℝ) ≤ Real.exp v → S.ComplexityLE v := by
  classical
  let I := D.dependentWordIdeal 0 2 0
  let H' := lieTreeHeight n H s
  have hHH' : H ≤ H' := lieTreeHeight_ge_input n H s
  have hb : ∃ b' : ∀ i : Fin (s + 1),
      Basis (Fin (finrank ℚ (T.filtration.associatedDegree.layer (i.val + 1)))) ℚ
        (T.filtration.associatedDegree.layer (i.val + 1)),
      ∀ i a j, RationalHeightLE (E.basis.repr (b' i a).val j) H' := by
    rw [T.associated]
    exact ⟨E.layerBasis, fun i a j => (hdegree i a j).mono hHH'⟩
  obtain ⟨b', hb'⟩ := hb
  obtain ⟨a, ha⟩ := exists_markedLieSpan_bounded_basis D.coefficientFreeFiltration E.basis
    D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent
    D.coefficientWeight_pos D.coefficientFreeGenerator_mem_layer hbracket hgen 0 2 0
  change Basis (Fin (finrank ℚ I.toSubmodule)) ℚ I at a
  have ha' : ∀ i j, RationalHeightLE (E.basis.repr (a i).val j) H' := by
    intro i j
    have h := ha i j
    change RationalHeightLE (E.basis.repr (a i).val j)
      (lieTreeHeight (Fintype.card (Fin n)) H s) at h
    simpa only [Fintype.card_fin, H'] using h
  have hann : T.filtration.layer s r ⊓ I.toSubmodule ≤ (B.freeFrequency D).ker := by
    rw [hT]
    exact B.top_inter_dependentWordIdeal_le_ker D
  obtain ⟨m, hm, d, hd, u, hu, f, hproj, hc, hbq, hrq, ξ, hξ, hξH⟩ :=
    exists_bounded_rank_quotient_data T.filtration E.basis b' T.basis I a
      (B.freeFrequency D) hann (hH.trans hHH') hb'
      (fun i j a k => (hrank i j a k).mono hHH') ha'
      (fun i j k => (hbracket i j k).mono hHH') (fun i => (hfreq i).mono hHH')
  let K := rankQuotientHeight n m d u H'
  have hm' : m ≤ n := by
    let _ : FiniteDimensional ℚ D.CoefficientFreeLieAlgebra := E.basis.finiteDimensional_of_finite
    have hn : finrank ℚ D.CoefficientFreeLieAlgebra = n := by
      simpa only [Fintype.card_fin] using finrank_eq_card_basis E.basis
    exact hm.trans ((Submodule.finrank_le I.toSubmodule).trans_eq hn)
  have hbq' : ∀ i : Fin (s + 1), ∃ bq : Basis
      (Fin (finrank ℚ (D.dependentQuotientFiltration.associatedDegree.layer (i.val + 1)))) ℚ
        (D.dependentQuotientFiltration.associatedDegree.layer (i.val + 1)),
      ∀ a j, RationalHeightLE (f.repr (bq a).val j) K := by
    intro i
    have h := hbq i
    rw [hT] at h
    exact h
  have hrq' : ∀ i j : Fin (s + 1), ∃ cq : Basis
      (Fin (finrank ℚ (D.dependentQuotientFiltration.layer i.val j.val))) ℚ
        (D.dependentQuotientFiltration.layer i.val j.val),
      ∀ a k, RationalHeightLE (f.repr (cq a).val k) K := by
    intro i j
    have h := hrq i j
    rw [hT] at h
    exact h
  choose bq hbqH using hbq'
  choose cq hcqH using hrq'
  obtain ⟨grid, hgrid, hdiv, hbound, G, S, hSF, hGf, hGgrid, hcoords, hint, hcomplex⟩ :=
    D.dependentQuotientFiltration.exists_bounded_rank_integral_model_with_frequency
      f bq cq hbqH hcqH hc ξ hξH l hl
  refine ⟨m, hm', d, hd, u, hu, G, S, hSF, hGgrid.symm ▸ hdiv,
    hGgrid.symm ▸ hbound, ?_, ?_, ξ, ?_, ?_, hint, ?_⟩
  · rwa [hGgrid]
  · intro i j
    rw [hGf]
    exact hproj i j
  · intro x hx
    apply hξ x
    rwa [hT]
  · intro i
    rw [hGf]
    exact hξH i
  · intro v hdv hgv hKv
    apply hcomplex v hdv
    · rwa [← hGgrid]
    · exact hKv

end Erdos3.NativeRankRelation.CommonData

end

end OAI
