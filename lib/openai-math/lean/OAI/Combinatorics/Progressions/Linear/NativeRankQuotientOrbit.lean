import OAI.Combinatorics.Progressions.Estimates.UniformFrozenDescent

namespace OAI

section

namespace Erdos3

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}

noncomputable def basisOfTail (b : Basis (Fin d) ℚ L) (P : Submodule ℚ L) (c : ℕ)
    (hP : P = basisTail b c) : Basis (Fin (finrank ℚ P)) ℚ P := by
  classical
  let a := supportedSubmoduleBasis b P {j | c ≤ j.val} (hP.trans (basisTail_eq_span b c))
  exact a.reindex (Fintype.equivFinOfCardEq (finrank_eq_card_basis a).symm)

theorem basisOfTail_height (b : Basis (Fin d) ℚ L) (P : Submodule ℚ L) (c : ℕ)
    (hP : P = basisTail b c) (i : Fin (finrank ℚ P)) (j : Fin d) :
    RationalHeightLE (b.repr (basisOfTail b P c hP i : L) j) 1 := by
  classical
  unfold basisOfTail
  rw [Basis.reindex_apply, supportedSubmoduleBasis_coe]
  exact basis_repr_height_one b _ j

theorem tail_span_basis_members (b : Basis (Fin d) ℚ L) (P : Submodule ℚ L) (c : ℕ)
    (hP : P = basisTail b c) : P = Submodule.span ℚ (b '' {j | b j ∈ P}) := by
  apply le_antisymm
  · conv_lhs => rw [hP, basisTail_eq_span]
    apply Submodule.span_mono
    rintro x ⟨j, hj, rfl⟩
    exact ⟨j, hP.symm ▸ basis_mem_tail b j hj, rfl⟩
  · exact Submodule.span_le.mpr (by rintro _ ⟨j, hj, rfl⟩; exact hj)

theorem NilpotentLieFiltration.exists_weights_of_tails {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis (Fin d) ℚ L)
    (htail : ∀ i, ∃ c, F.layer i = basisTail b c) :
    ∃ w : Fin d → ℕ, ∀ i, F.layer i = Submodule.span ℚ (b '' {j | i ≤ w j}) := by
  let S : Fin (s + 1) → Set (Fin d) := fun i => {j | b j ∈ F.layer (i.val + 1)}
  have hS : Antitone S := fun _ _ h _ hx => F.antitone (Nat.add_le_add_right h 1) hx
  let w := nestedSupportWeight S
  refine ⟨w, F.layer_eq_span_of_weighted_flag b w (fun j => nestedSupportWeight_le S j) ?_⟩
  intro i
  obtain ⟨c, hc⟩ := htail (i.val + 1)
  rw [tail_span_basis_members b _ c hc]
  apply congrArg (Submodule.span ℚ)
  apply congrArg (fun A : Set (Fin d) => b '' A)
  ext j
  exact mem_nestedSupport_iff S hS i j

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieFiltration

theorem exists_coordinate_quotient_layer_basis
    {L ι : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype ι]
    (b : Basis ι ℚ L) (I : LieIdeal ℚ L) (S : Set ι) [DecidablePred (· ∈ S)]
    (hI : I.toSubmodule = Submodule.span ℚ (b '' S))
    (P : Submodule ℚ L) (T : Set ι) (hP : P = Submodule.span ℚ (b '' T)) :
    ∃ a : Basis (Fin (finrank ℚ (P.map (lieQuotientMap I).toLinearMap))) ℚ
        (P.map (lieQuotientMap I).toLinearMap),
      ∀ i j, rationalLogHeight ((quotientFinBasis b I S hI).repr (a i : L ⧸ I) j) ≤ 0 := by
  classical
  let q := supportedQuotientBasis b I.toSubmodule S hI
  have hspan : P.map (lieQuotientMap I).toLinearMap =
      Submodule.span ℚ (q '' {i : {i // i ∉ S} | i.val ∈ T}) := by
    rw [hP]
    exact supportedQuotientBasis_map_span b I.toSubmodule S hI T
  let a := supportedSubmoduleBasis q (P.map (lieQuotientMap I).toLinearMap)
    {i : {i // i ∉ S} | i.val ∈ T} hspan
  let e := Fintype.equivFinOfCardEq (finrank_eq_card_basis a).symm
  refine ⟨a.reindex e, ?_⟩
  intro i j
  rw [Basis.reindex_apply, supportedSubmoduleBasis_coe,
    quotientFinBasis, Basis.repr_reindex_apply]
  change rationalLogHeight (q.repr (q (e.symm i).val)
    ((Fintype.equivFin {i // i ∉ S}).symm j)) ≤ 0
  rw [Basis.repr_self, Finsupp.single_apply]
  split_ifs <;> norm_num [rationalLogHeight]

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {L ι κ : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem adaptedSquareBasis_projection_height (e : Basis ι ℚ L) (b : Basis κ ℚ L) (w : κ → ℕ)
    (h : F.layer 2 = Submodule.span ℚ (b '' {i | 2 ≤ w i}))
    {H : ℕ} (hH : 1 ≤ H) (hb : ∀ i j, RationalHeightLE (e.repr (b j) i) H)
    (i : κ ⊕ {i // 2 ≤ w i}) (k : ι) :
    RationalHeightLE (e.repr (F.squareFst (F.adaptedSquareBasis b w h i)) k) H ∧
      RationalHeightLE (e.repr (F.squareSnd (F.adaptedSquareBasis b w h i)) k) H := by
  cases i with
  | inl i =>
    simpa only [squareFst_apply, squareSnd_apply, adaptedSquareBasis_inl] using
      And.intro (hb k i) (hb k i)
  | inr i =>
    constructor
    · simpa only [squareFst_apply, adaptedSquareBasis_inr] using hb k i
    · simp only [squareSnd_apply, adaptedSquareBasis_inr, map_zero, Finsupp.zero_apply]
      exact rationalHeightLE_zero hH

variable [Fintype κ]

theorem squareFinBasis_projection_height (e : Basis ι ℚ L) (b : Basis κ ℚ L) (w : κ → ℕ)
    (h : F.layer 2 = Submodule.span ℚ (b '' {i | 2 ≤ w i}))
    {H : ℕ} (hH : 1 ≤ H) (hb : ∀ i j, RationalHeightLE (e.repr (b j) i) H)
    (i : Fin (Fintype.card (κ ⊕ {i // 2 ≤ w i}))) (k : ι) :
    RationalHeightLE (e.repr (F.squareFst (F.squareFinBasis b w h i)) k) H ∧
      RationalHeightLE (e.repr (F.squareSnd (F.squareFinBasis b w h i)) k) H := by
  simp only [squareFinBasis, Basis.reindex_apply]
  exact F.adaptedSquareBasis_projection_height e b w h hH hb _ k

theorem quotientFinBasis_projection_height (b : Basis κ ℚ L) (I : LieIdeal ℚ L)
    (S : Set κ) [DecidablePred (· ∈ S)]
    (hspan : I.toSubmodule = Submodule.span ℚ (b '' S))
    (i : κ) (j : Fin (Fintype.card {i // i ∉ S})) :
    RationalHeightLE ((quotientFinBasis b I S hspan).repr (lieQuotientMap I (b i)) j) 1 := by
  rw [quotientFinBasis, Basis.repr_reindex_apply]
  exact supportedQuotientBasis_projection_height b I S hspan i _

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d r : ℕ}
  {D : RationalFilteredNilmanifold L s d} (R : D.DegreeRankStructure r)

theorem rankFlag_span_height {H : ℕ}
    (hR : ∀ i j a k, RationalHeightLE (D.basis.repr (R.basis i j a : L) k) H)
    (n : Fin ((s + 1) * (s + 1) + 1)) :
    Submodule.span ℚ ({x : L | ∀ k, RationalHeightLE (D.basis.repr x k) H} ∩
      (R.filtration.rankFlag n.val : Set L)) = R.filtration.rankFlag n.val := by
  by_cases hn : n.val < (s + 1) * (s + 1)
  · obtain ⟨hi, hj⟩ := DegreeRankLieFiltration.rankFlag_decode_lt hn
    let i : Fin (s + 1) := ⟨n.val / (s + 1), by omega⟩
    let j : Fin (s + 1) := ⟨n.val % (s + 1), by omega⟩
    exact span_inter_eq_of_spanning_family _ (R.basis i j) (R.basis i j).span_eq _
      (fun a => hR i j a)
  · have heq : n.val = (s + 1) * (s + 1) := by omega
    rw [heq, R.filtration.rankFlag_terminal]
    exact le_antisymm (Submodule.span_le.mpr (fun _ hx => hx.2)) bot_le

theorem exists_bounded_rank_adapted_basis {H : ℕ}
    (hR : ∀ i j a k, RationalHeightLE (D.basis.repr (R.basis i j a : L) k) H) :
    ∃ b : Basis (Fin (finrank ℚ L)) ℚ L,
      IsCentralLieBasis b ∧ (∀ a k, RationalHeightLE (D.basis.repr (b a) k) H) ∧
      ∀ i j, ∃ c ≤ finrank ℚ L, R.filtration.layer i j = basisTail b c := by
  let := D.basis.finiteDimensional_of_finite
  let N := (s + 1) * (s + 1)
  let S : Set L := {x | ∀ k, RationalHeightLE (D.basis.repr x k) H}
  let P : Fin (N + 1) → Submodule ℚ L := fun n => R.filtration.rankFlag n.val
  have hP : Antitone P := fun _ _ h => R.filtration.rankFlag_antitone h
  have hspan : ∀ n, Submodule.span ℚ (S ∩ (P n : Set L)) = P n := R.rankFlag_span_height hR
  have hS : Submodule.span ℚ S = ⊤ := by
    apply top_unique
    calc
      ⊤ = P 0 := R.filtration.rankFlag_zero.symm
      _ = Submodule.span ℚ (S ∩ (P 0 : Set L)) := (hspan 0).symm
      _ ≤ Submodule.span ℚ S := Submodule.span_mono Set.inter_subset_left
  obtain ⟨b, w, hw, _, hb, hflag⟩ := exists_sorted_flag_basis_from_spanning_set P hP S hS hspan
  have hcentral : IsCentralLieBasis b := centralLieBasis_of_finite_flag R.filtration.rankFlag b w
    R.filtration.rankFlag_zero R.filtration.rankFlag_terminal
    (fun _ {_ _} hy => R.filtration.rankFlag_lie_mem hy) hw hflag
  refine ⟨b, hcentral, hb, ?_⟩
  intro i j
  obtain ⟨k, hk⟩ := R.filtration.layer_eq_rankFlag i j
  exact ⟨weightCut w k.val, weightCut_le w k.val,
    hk.trans ((hflag k).trans (span_weight_gt_eq_basisTail b w hw k.val))⟩

end Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d r : ℕ}
  {D : RationalFilteredNilmanifold L s d} (R : D.DegreeRankStructure r)

theorem exists_controlled_rank_adapted_basis {p : ℝ} (hp : 0 ≤ p) (hR : R.ComplexityLE p) :
    ∃ (b : Basis (Fin (finrank ℚ L)) ℚ L) (N : ℕ),
      IsCentralLieBasis b ∧
      (∀ i j, ∃ c ≤ finrank ℚ L, R.filtration.layer i j = basisTail b c) ∧
      (∀ j i, rationalLogHeight (D.basis.repr (b j) i) ≤ p + 1) ∧
      (∀ i j, rationalLogHeight (b.repr (D.basis i) j) ≤ (p + 3) ^ 5) ∧
      (∀ i j k, rationalLogHeight (lieStructureConstants b i j k) ≤ (p + 3) ^ 11) ∧
      0 < N ∧ (N : ℝ) ≤ Real.exp ((p + 3) ^ 9) ∧
      scaledIntegerGrid N ⊆ bchSubgroupCoordinates b D.lattice ∧
      bchSubgroupCoordinates b D.lattice ⊆ denominatorGrid N := by
  let := D.basis.finiteDimensional_of_finite
  let H := ⌈Real.exp p⌉₊
  have hH : 1 ≤ H := one_le_ceil_exp p
  have hHp : (H : ℝ) ≤ Real.exp (p + 1) := ceil_exp_le_exp_add_one hp
  have hp1 : 0 ≤ p + 1 := by linarith
  have hd : (d : ℝ) ≤ p + 1 := hR.1.1.trans (by linarith)
  have hr : (finrank ℚ L : ℝ) ≤ p + 1 := by
    simpa only [finrank_eq_card_basis D.basis, Fintype.card_fin] using hd
  have hgrid : (D.grid : ℝ) ≤ Real.exp (p + 1) :=
    hR.1.2.1.trans (Real.exp_le_exp.mpr (by linarith))
  obtain ⟨b, hcentral, hb, htail⟩ := R.exists_bounded_rank_adapted_basis
    (fun i j a k => rationalHeightLE_ceil_exp (hR.2 i j a k))
  obtain ⟨N, hN, hNb, hin, hout⟩ := exists_basis_change_grid_exp_bound D.basis b D.lattice
    hH D.grid_pos hb D.inner_grid D.outer_grid hp1
    (by simpa only [Fintype.card_fin] using hd)
    (by simpa only [Fintype.card_fin] using hr) hHp hgrid
  have hInv := inverse_basis_entries_height D.basis b hH hb
  have hStructure := basis_change_structure_height D.basis b hH hb
    (fun i j k => rationalHeightLE_ceil_exp (hR.1.2.2.1 i j k))
  have hSolveBudget := rationalSolveHeight_le_budget (finrank ℚ L) H hp1 hr hHp
  have hStructureBudget := rationalLieStructureHeight_inverse_budget d (finrank ℚ L) H hp1 hd hr hHp
  have hshift : p + 1 + 2 = p + 3 := by ring
  refine ⟨b, N, hcentral, htail, ?_, ?_, ?_, hN, ?_, hin, hout⟩
  · exact fun j i => rationalLogHeight_le_of_height (hb j i) hHp
  · intro i j
    apply rationalLogHeight_le_of_height (hInv i j)
    simpa only [Fintype.card_fin, hshift] using hSolveBudget
  · intro i j k
    apply rationalLogHeight_le_of_height (hStructure i j k)
    simpa only [Fintype.card_fin, hshift] using hStructureBudget
  · simpa only [hshift] using hNb

end Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d r : ℕ}
  {D : RationalFilteredNilmanifold L s d}

structure AdaptedData (R : D.DegreeRankStructure r) extends D.AdaptedModelData where
  central : IsCentralLieBasis basis
  rank_layers : ∀ i j, ∃ c ≤ finrank ℚ L, R.filtration.layer i j = basisTail basis c

namespace AdaptedData

variable {R : D.DegreeRankStructure r} (F : R.AdaptedData)

noncomputable def model : RationalFilteredNilmanifold L s (finrank ℚ L) := F.toAdaptedModelData.model

noncomputable def rank : F.model.DegreeRankStructure r where
  filtration := R.filtration
  associated := R.associated
  basis i j := basisOfTail F.basis _ (Classical.choose (F.rank_layers i.val j.val))
    (Classical.choose_spec (F.rank_layers i.val j.val)).2

theorem rank_filtration : F.rank.filtration = R.filtration := rfl

theorem rank_realSubgroup (i j : ℕ) : F.rank.realSubgroup i j = R.realSubgroup i j := rfl

theorem model_geometry_of_bounds {p : ℝ} (hp : 0 ≤ p) (hd : (finrank ℚ L : ℝ) ≤ p)
    (hgrid : (F.grid : ℝ) ≤ Real.exp p)
    (hc : ∀ i j k, rationalLogHeight (lieStructureConstants F.basis i j k) ≤ p) :
    F.model.GeometryComplexityLE p :=
  D.filtration.ofAdaptedBasis_geometry F.basis F.weight F.layers D.lattice F.grid F.grid_pos
    F.inner F.outer hp hd hgrid hc

theorem rank_complexity {p : ℝ} (hp : 0 ≤ p) (hF : F.model.GeometryComplexityLE p) :
    F.rank.ComplexityLE p := by
  refine ⟨hF, ?_⟩
  intro i j a k
  apply rationalLogHeight_le_of_height
    (basisOfTail_height F.basis _ (Classical.choose (F.rank_layers i.val j.val))
      (Classical.choose_spec (F.rank_layers i.val j.val)).2 a k)
  simpa only [Nat.cast_one] using Real.one_le_exp hp

end AdaptedData

theorem exists_rank_adapted_data (R : D.DegreeRankStructure r) {p : ℝ}
    (hp : 0 ≤ p) (hR : R.ComplexityLE p) :
    ∃ F : R.AdaptedData, F.rank.ComplexityLE ((p + 3) ^ 11) ∧
      (∀ i j, rationalLogHeight (D.basis.repr (F.basis i) j) ≤ p + 1) ∧
      ∀ j i, rationalLogHeight (F.basis.repr (D.basis j) i) ≤ (p + 3) ^ 5 := by
  obtain ⟨b, N, hcentral, htail, hb, hinv, hc, hN, hNb, hin, hout⟩ :=
    R.exists_controlled_rank_adapted_basis hp hR
  have hOrd : ∀ i, ∃ c, D.filtration.layer i = basisTail b c := by
    intro i
    obtain ⟨c, _, h⟩ := htail i 0
    refine ⟨c, ?_⟩
    rw [← R.associated]
    exact h
  obtain ⟨w, hw⟩ := D.filtration.exists_weights_of_tails b hOrd
  let F : R.AdaptedData := {
    basis := b
    weight := w
    layers := hw
    grid := N
    grid_pos := hN
    inner := hin
    outer := hout
    central := hcentral
    rank_layers := htail
  }
  have hp1 : 1 ≤ p + 3 := by linarith
  have hpow : p ≤ (p + 3) ^ 11 := by
    calc
      p ≤ p + 3 := by linarith
      _ = (p + 3) ^ 1 := (pow_one _).symm
      _ ≤ (p + 3) ^ 11 := pow_le_pow_right₀ hp1 (by decide)
  have hdim : (finrank ℚ L : ℝ) ≤ (p + 3) ^ 11 := by
    simpa only [finrank_eq_card_basis D.basis, Fintype.card_fin] using hR.1.1.trans hpow
  have hgeom : F.model.GeometryComplexityLE ((p + 3) ^ 11) :=
    F.model_geometry_of_bounds (by positivity) hdim
      (hNb.trans (Real.exp_le_exp.mpr (pow_le_pow_right₀ hp1 (by decide : 9 ≤ 11)))) hc
  exact ⟨F, F.rank_complexity (by positivity) hgeom, hb, hinv⟩

end Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

end

section

namespace Erdos3

namespace RationalFilteredNilmanifold.DegreeRankStructure.AdaptedData

open Module NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r d : ℕ}
  {D : RationalFilteredNilmanifold L s d} {R : D.DegreeRankStructure (r + 1)}
  (F : R.AdaptedData)

theorem exists_lower_rank_quotient {p : ℝ} (hp : 0 ≤ p) (hF : F.model.GeometryComplexityLE p) :
    let I := R.filtration.layerIdeal s (r + 1)
    let hI : D.filtration.layer (s + 1) ≤ I.toSubmodule := by rw [D.filtration.terminal]; exact bot_le
    ∃ n : ℕ, n ≤ finrank ℚ L ∧
      ∃ Q : RationalFilteredNilmanifold (L ⧸ I) s n,
        ∃ U : Q.DegreeRankStructure r,
          U.filtration = R.filtration.quotientRank r (Nat.le_of_succ_le R.filtration.rank_le_degree) ∧
          Q.filtration = D.filtration.quotientLie I hI ∧
          Q.lattice = D.lattice.map (D.filtration.quotientStepHom I hI) ∧
          U.ComplexityLE p ∧
          (∀ i j, rationalLogHeight (Q.basis.repr (lieQuotientMap I (F.basis i)) j) ≤ 0) ∧
          ∀ j, ∃ k, ∀ x : L, Q.basis.repr (lieQuotientMap I x) j = F.basis.repr x k := by
  intro I hI
  classical
  let S : Set (Fin (finrank ℚ L)) := {i | F.basis i ∈ I}
  have hspan : I.toSubmodule = Submodule.span ℚ (F.basis '' S) := by
    obtain ⟨c, _, hc⟩ := F.rank_layers s (r + 1)
    exact tail_span_basis_members F.basis _ c hc
  let Q := D.filtration.coordinateQuotientModel F.basis F.weight F.layers I hI S hspan
    D.lattice F.grid F.grid_pos F.inner F.outer
  let G := R.filtration.quotientRank r (Nat.le_of_succ_le R.filtration.rank_le_degree)
  have hG : G.associatedDegree = Q.filtration := by
    apply NilpotentLieFiltration.eq_of_layer_eq
    funext j
    change (R.filtration.layer j 0).map (lieQuotientMap I).toLinearMap =
      (D.filtration.layer j).map (lieQuotientMap I).toLinearMap
    exact congrArg (fun P : Submodule ℚ L => P.map (lieQuotientMap I).toLinearMap)
      (congrArg (fun H : NilpotentLieFiltration L s => H.layer j) R.associated)
  have hbase (i j : Fin (s + 1)) :
      ∃ b : Basis (Fin (finrank ℚ (G.layer i.val j.val))) ℚ (G.layer i.val j.val),
        ∀ a k, rationalLogHeight (Q.basis.repr (b a : L ⧸ I) k) ≤ 0 := by
    obtain ⟨c, _, hc⟩ := F.rank_layers i.val j.val
    exact exists_coordinate_quotient_layer_basis F.basis I S hspan (R.filtration.layer i.val j.val)
      {k | c ≤ k.val} (hc.trans (basisTail_eq_span F.basis c))
  choose b hb using hbase
  let U : Q.DegreeRankStructure r := ⟨G, hG, b⟩
  have hQ : Q.GeometryComplexityLE p :=
    D.filtration.coordinateQuotientModel_geometry F.basis F.weight F.layers I hI S hspan
      D.lattice F.grid F.grid_pos F.inner F.outer hp
      (by simpa only [Fintype.card_fin] using hF.1) hF.2.1 hF.2.2.1
  refine ⟨_, ?_, Q, U, rfl, rfl, rfl, ⟨hQ, ?_⟩, ?_, ?_⟩
  · simpa only [Fintype.card_fin] using Fintype.card_subtype_le (fun i : Fin (finrank ℚ L) => i ∉ S)
  · intro i j a k
    exact (hb i j a k).trans hp
  · intro i j
    exact rationalLogHeight_le_of_height
      (quotientFinBasis_projection_height F.basis I S hspan i j) (by norm_num)

  · intro j
    exact ⟨((Fintype.equivFin {i // i ∉ S}).symm j).val,
      fun x => quotientFinBasis_repr_mk F.basis I S hspan x j⟩

end RationalFilteredNilmanifold.DegreeRankStructure.AdaptedData
end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

open Module NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r d : ℕ}
  {D : RationalFilteredNilmanifold L s d} (R : D.DegreeRankStructure (r + 1))

theorem terminal_le_topRankIdeal :
    D.filtration.layer (s + 1) ≤ (R.filtration.layerIdeal s (r + 1)).toSubmodule := by
  rw [D.filtration.terminal]
  exact bot_le

theorem exists_controlled_lower_rank_quotient {p : ℝ} (hp : 0 ≤ p) (hR : R.ComplexityLE p) :
    let I := R.filtration.layerIdeal s (r + 1)
    ∃ n : ℕ, n ≤ d ∧
      ∃ Q : RationalFilteredNilmanifold (L ⧸ I) s n,
        ∃ U : Q.DegreeRankStructure r,
          U.filtration = R.filtration.quotientRank r (Nat.le_of_succ_le R.filtration.rank_le_degree) ∧
          Q.filtration = D.filtration.quotientLie I R.terminal_le_topRankIdeal ∧
          Q.lattice = D.lattice.map (D.filtration.quotientStepHom I R.terminal_le_topRankIdeal) ∧
          U.ComplexityLE ((p + 3) ^ 11) ∧
          ∀ i j, rationalLogHeight (Q.basis.repr (lieQuotientMap I (D.basis i)) j) ≤ (p + 3) ^ 5 := by
  intro I
  obtain ⟨F, hF, _, hinv⟩ := R.exists_rank_adapted_data hp hR
  obtain ⟨n, hn, Q, U, hU, hQF, hQL, hUc, _, hcoord⟩ :=
    F.exists_lower_rank_quotient (by positivity : 0 ≤ (p + 3) ^ 11) hF.1
  have hdim : finrank ℚ L = d := by
    simpa only [Fintype.card_fin] using finrank_eq_card_basis D.basis
  refine ⟨n, hdim ▸ hn, Q, U, hU, hQF, hQL, hUc, ?_⟩
  intro i j
  obtain ⟨k, hk⟩ := hcoord j
  rw [hk]
  exact hinv i k

end Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {L σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s r d n : ℕ}
  {D : RationalFilteredNilmanifold L s d} (R : D.DegreeRankStructure (r + 1))
  (Q : RationalFilteredNilmanifold (L ⧸ R.filtration.layerIdeal s (r + 1)) s n)
  (hQ : Q.filtration = D.filtration.quotientLie
    (R.filtration.layerIdeal s (r + 1)) R.terminal_le_topRankIdeal) {w : σ → ℕ}

noncomputable def rankQuotientOrbit (g : D.filtration.realification.PolynomialOrbit w) :
    Q.filtration.realification.PolynomialOrbit w :=
  let q := D.filtration.realQuotientPolynomialOrbit
    (R.filtration.layerIdeal s (r + 1)) R.terminal_le_topRankIdeal g
  NilpotentLieFiltration.polynomialOrbitOfLog q.log (by rw [hQ]; exact q.adapted)

theorem rankQuotientOrbit_eval (g : D.filtration.realification.PolynomialOrbit w) (x : σ → ℤ) :
    Q.filtration.realification.polynomialOrbitEval w x (R.rankQuotientOrbit Q hQ g) =
      realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := Q.filtration.lowerCentralSeries_eq_bot)
        (lieQuotientMap (R.filtration.layerIdeal s (r + 1)))
        (D.filtration.realification.polynomialOrbitEval w x g) :=
  D.filtration.realQuotientPolynomialOrbit_eval
    (R.filtration.layerIdeal s (r + 1)) R.terminal_le_topRankIdeal g x

end Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

end

end OAI
