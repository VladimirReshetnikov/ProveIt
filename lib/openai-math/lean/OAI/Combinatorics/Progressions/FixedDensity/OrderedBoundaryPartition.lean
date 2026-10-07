-- Modified for ProveIt: added `import OAI.Compat.*` lines (backported names); see lib/openai-math/README.md.
-- Modified for ProveIt: in the deletionCylinder computation, `all_goals rfl` after `simp` (simp leaves a reflexive iff in Mathlib v4.32.0).
import Mathlib.Data.Fin.Tuple.Finset
import OAI.Combinatorics.Progressions.FixedDensity.OrderedRegularizedCells
import OAI.Combinatorics.Progressions.FixedDensity.StructuredCleaning
import OAI.Compat.BigOperators

namespace OAI

section

namespace Erdos3.FixedDensity

def eraseOrderedFace
    {k r : ℕ} (e : OrderedFace k r) (i : Fin r) :
    OrderedFace k (r - 1) := by
  cases r with
  | zero => exact Fin.elim0 i
  | succ n =>
      exact (Fin.succAboveOrderEmb i).trans e

@[simp]
theorem orderedFaceTuple_eraseOrderedFace
    {G : Type*} {k r : ℕ}
    (e : OrderedFace k r) (i : Fin r)
    (x : Fin k → G) :
    orderedFaceTuple (eraseOrderedFace e i) x =
      eraseCoordinate i (orderedFaceTuple e x) := by
  cases r with
  | zero => exact Fin.elim0 i
  | succ n =>
      rfl

theorem exists_orderedCoface
    {k r : ℕ} (hr : 0 < r) (hrk : r ≤ k)
    (g : OrderedFace k (r - 1)) :
    ∃ e : OrderedFace k r, ∃ i : Fin r,
      eraseOrderedFace e i = g := by
  classical
  cases r with
  | zero => omega
  | succ n =>
      let s : Finset (Fin k) :=
        Finset.univ.map g.toEmbedding
      have hs : s.card = n := by
        rw [show s.card =
            (Finset.univ :
              Finset (Fin (n + 1 - 1))).card by
          exact Finset.card_map g.toEmbedding]
        exact Fintype.card_fin n
      have hnk : n < k := by
        omega
      have hs_ne_univ : s ≠ Finset.univ := by
        intro h
        have : n = k := by
          calc
            n = s.card := hs.symm
            _ = Finset.univ.card := congrArg Finset.card h
            _ = k := by simp
        omega
      obtain ⟨v, hv⟩ :
          ∃ v : Fin k, v ∉ s := by
        by_contra h
        push Not at h
        exact hs_ne_univ (Finset.eq_univ_of_forall h)
      let t : Finset (Fin k) := insert v s
      have ht : t.card = n + 1 := by
        simp [t, hv, hs]
      let e : OrderedFace k (n + 1) :=
        t.orderEmbOfFin ht
      have hv_t : v ∈ t := by
        simp [t]
      let vInT : t := ⟨v, hv_t⟩
      let i : Fin (n + 1) :=
        (t.orderIsoOfFin ht).symm vInT
      have hei : e i = v := by
        change
          t.orderEmbOfFin ht
              ((t.orderIsoOfFin ht).symm vInT) =
            v
        rw [← Finset.coe_orderIsoOfFin_apply]
        simp [vInT]
      have herase_mem :
          ∀ q, eraseOrderedFace e i q ∈ s := by
        intro q
        have htmem :
            e (i.succAbove q) ∈ t := by
          exact t.orderEmbOfFin_mem ht (i.succAbove q)
        have hne :
            e (i.succAbove q) ≠ v := by
          intro h
          have heq :
              e (i.succAbove q) = e i :=
            h.trans hei.symm
          exact
            (i.succAbove_ne q)
              (e.injective heq)
        change e (i.succAbove q) ∈ s
        have hor : e (i.succAbove q) = v ∨
            e (i.succAbove q) ∈ s := by
          simpa [t] using htmem
        exact hor.resolve_left hne
      have herase :
          eraseOrderedFace e i =
            s.orderEmbOfFin hs :=
        Finset.orderEmbOfFin_unique' hs herase_mem
      have hg :
          g = s.orderEmbOfFin hs := by
        apply Finset.orderEmbOfFin_unique' hs
        intro q
        exact Finset.mem_map.mpr
          ⟨q, Finset.mem_univ _, rfl⟩
      exact ⟨e, i, herase.trans hg.symm⟩

namespace OrderedPattern

noncomputable def deletionCylinder
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (D : DeletionFamily (G := G) k (r - 1))
    (e : OrderedFace k r) (i : Fin r) :
    Finset (Fin r → G) := by
  classical
  exact Finset.univ.filter fun y =>
    eraseCoordinate i y ∈ D (eraseOrderedFace e i)

@[simp]
theorem mem_deletionCylinder
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (D : DeletionFamily (G := G) k (r - 1))
    (e : OrderedFace k r) (i : Fin r)
    (y : Fin r → G) :
    y ∈ deletionCylinder D e i ↔
      eraseCoordinate i y ∈
        D (eraseOrderedFace e i) := by
  simp [deletionCylinder]

theorem card_deletionCylinder
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (D : DeletionFamily (G := G) k (r - 1))
    (e : OrderedFace k r) (i : Fin r) :
    (deletionCylinder D e i).card =
      Fintype.card G *
        (D (eraseOrderedFace e i)).card := by
  classical
  cases r with
  | zero => exact Fin.elim0 i
  | succ n =>
      change DeletionFamily (G := G) k n at D
      let S : (j : Fin (n + 1)) → Finset G :=
        fun _ => Finset.univ
      have h :=
        Finset.card_insertNthEquiv_filter_piFinset
          (S := S) (p := i)
          (P := fun z =>
            z ∈ D (eraseOrderedFace e i))
      simp only [S, Fin.removeNth_fun_const,
        Fintype.piFinset_univ] at h
      simp only [Finset.filter_univ_mem] at h
      have hcylinder :
          deletionCylinder D e i =
            Finset.univ.filter fun x :
                Fin (n + 1) → G =>
              Fin.removeNth i x ∈
                D (eraseOrderedFace e i) := by
        ext x
        simp [eraseCoordinate_eq_removeNth]
        all_goals rfl
      rw [hcylinder]
      exact h

noncomputable def liftLowerDeletion
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (D : DeletionFamily (G := G) k (r - 1)) :
    DeletionFamily (G := G) k r := by
  classical
  exact fun e =>
    Finset.univ.biUnion fun i =>
      deletionCylinder D e i

@[simp]
theorem mem_liftLowerDeletion
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (D : DeletionFamily (G := G) k (r - 1))
    (e : OrderedFace k r) (y : Fin r → G) :
    y ∈ liftLowerDeletion D e ↔
      ∃ i : Fin r,
        eraseCoordinate i y ∈
          D (eraseOrderedFace e i) := by
  classical
  simp [liftLowerDeletion]

theorem card_liftLowerDeletion_le
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (D : DeletionFamily (G := G) k (r - 1))
    (e : OrderedFace k r) :
    (liftLowerDeletion D e).card ≤
      ∑ i : Fin r,
        (deletionCylinder D e i).card := by
  classical
  exact Finset.card_biUnion_le

theorem deletionCylinder_density_eq
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (D : DeletionFamily (G := G) k (r - 1))
    (e : OrderedFace k r) (i : Fin r) :
    ((deletionCylinder D e i).card : ℝ) /
        Fintype.card (Fin r → G) =
      faceDeletionDensity D
        (eraseOrderedFace e i) := by
  cases r with
  | zero => exact Fin.elim0 i
  | succ n =>
      change DeletionFamily (G := G) k n at D
      rw [card_deletionCylinder]
      unfold faceDeletionDensity
      simp only [Fintype.card_fun, Fintype.card_fin,
        Nat.cast_mul, Nat.cast_pow]
      have hG : (0 : ℝ) <
          Fintype.card G := by
        positivity
      rw [pow_succ]
      field_simp [ne_of_gt hG]
      simp

theorem faceDeletionDensity_liftLowerDeletion_le
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (D : DeletionFamily (G := G) k (r - 1))
    {δ : ℝ}
    (hD : ∀ g, faceDeletionDensity D g ≤ δ)
    (e : OrderedFace k r) :
    faceDeletionDensity (liftLowerDeletion D) e ≤
      (r : ℝ) * δ := by
  unfold faceDeletionDensity
  have hdenom :
      (0 : ℝ) <
        Fintype.card (Fin r → G) := by
    positivity
  calc
    ((liftLowerDeletion D e).card : ℝ) /
          Fintype.card (Fin r → G) ≤
        (∑ i : Fin r,
          (deletionCylinder D e i).card : ℕ) /
            Fintype.card (Fin r → G) := by
      apply div_le_div_of_nonneg_right
      · exact_mod_cast card_liftLowerDeletion_le D e
      · exact hdenom.le
    _ =
        ∑ i : Fin r,
          ((deletionCylinder D e i).card : ℝ) /
            Fintype.card (Fin r → G) := by
      rw [Nat.cast_sum, Finset.sum_div]
    _ =
        ∑ i : Fin r,
          faceDeletionDensity D
            (eraseOrderedFace e i) := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact deletionCylinder_density_eq D e i
    _ ≤ ∑ _i : Fin r, δ := by
      apply Finset.sum_le_sum
      intro i _hi
      exact hD (eraseOrderedFace e i)
    _ = (r : ℝ) * δ := by
      simp

noncomputable def unionDeletion
    {ι G : Type*} [Fintype ι]
    [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (D : ι → DeletionFamily (G := G) k r) :
    DeletionFamily (G := G) k r := by
  classical
  exact fun e =>
    Finset.univ.biUnion fun t => D t e

@[simp]
theorem mem_unionDeletion
    {ι G : Type*} [Fintype ι]
    [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (D : ι → DeletionFamily (G := G) k r)
    (e : OrderedFace k r) (y : Fin r → G) :
    y ∈ unionDeletion D e ↔
      ∃ t : ι, y ∈ D t e := by
  classical
  simp [unionDeletion]

theorem faceDeletionDensity_unionDeletion_le
    {ι G : Type*} [Fintype ι]
    [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (D : ι → DeletionFamily (G := G) k r)
    (e : OrderedFace k r) :
    faceDeletionDensity (unionDeletion D) e ≤
      ∑ t : ι, faceDeletionDensity (D t) e := by
  unfold faceDeletionDensity unionDeletion
  have hdenom :
      (0 : ℝ) <
        Fintype.card (Fin r → G) := by
    positivity
  calc
    (((Finset.univ.biUnion fun t => D t e).card : ℕ) : ℝ) /
          Fintype.card (Fin r → G) ≤
        (∑ t : ι, (D t e).card : ℕ) /
          Fintype.card (Fin r → G) := by
      apply div_le_div_of_nonneg_right
      · exact_mod_cast (Finset.card_biUnion_le :
          (Finset.univ.biUnion fun t => D t e).card ≤
            ∑ t : ι, (D t e).card)
      · exact hdenom.le
    _ =
        ∑ t : ι,
          ((D t e).card : ℝ) /
            Fintype.card (Fin r → G) := by
      rw [Nat.cast_sum, Finset.sum_div]

theorem toWeighted_edgeWeight_zeroOne
    {G : Type*} {k r : ℕ}
    (H : OrderedPattern G k r)
    (e : OrderedFace k r) :
    IsZeroOneValued (H.toWeighted.edgeWeight e) := by
  intro y
  classical
  by_cases hy : H.edge e y
  · right
    simp [OrderedPattern.toWeighted, hy]
  · left
    simp [OrderedPattern.toWeighted, hy]

noncomputable def lowStructuredDeletion
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (H : OrderedPattern G k r)
    (S : OrderedRegularitySystem G k r)
    (τ : ℝ) :
    DeletionFamily (G := G) k r :=
  fun e =>
    (S e).lowStructuredOneFinset
      (H.toWeighted.edgeWeight e) τ

@[simp]
theorem mem_lowStructuredDeletion
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (H : OrderedPattern G k r)
    (S : OrderedRegularitySystem G k r)
    (τ : ℝ) (e : OrderedFace k r)
    (y : Fin r → G) :
    y ∈ lowStructuredDeletion H S τ e ↔
      H.toWeighted.edgeWeight e y = 1 ∧
        (S e).structured
          (H.toWeighted.edgeWeight e) y < τ := by
  exact
    (S e).mem_lowStructuredOneFinset
      (H.toWeighted.edgeWeight e) τ y

theorem faceDeletionDensity_lowStructuredDeletion_le
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (H : OrderedPattern G k r)
    (S : OrderedRegularitySystem G k r)
    {τ : ℝ} (hτ : 0 ≤ τ)
    (e : OrderedFace k r) :
    faceDeletionDensity
        (lowStructuredDeletion H S τ) e ≤ τ := by
  have hmean :=
    (S e).mean_indicator_lowStructuredOneFinset_le
      (H.toWeighted_edgeWeight_zeroOne e) hτ
  rw [mean_finsetIndicator] at hmean
  exact hmean

theorem regularized_edgeWeight_ge_of_not_mem_lowDeletion
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (H : OrderedPattern G k r)
    (S : OrderedRegularitySystem G k r)
    (τ : ℝ) (e : OrderedFace k r)
    (y : Fin r → G)
    (hy : H.edge e y)
    (hnot : y ∉ lowStructuredDeletion H S τ e) :
    τ ≤
      (regularizedOrderedPattern H.toWeighted S).edgeWeight e y := by
  have hone :
      H.toWeighted.edgeWeight e y = 1 := by
    classical
    simp [OrderedPattern.toWeighted, hy]
  have hnotlt :
      ¬(S e).structured
          (H.toWeighted.edgeWeight e) y < τ := by
    intro hlt
    exact hnot
      ((mem_lowStructuredDeletion H S τ e y).2
        ⟨hone, hlt⟩)
  exact not_lt.mp hnotlt

theorem lowerCover_lifts
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (hr : 0 < r) (hrk : r ≤ k)
    (L : OrderedPattern G k (r - 1))
    (D : DeletionFamily (G := G) k (r - 1))
    (hcover : L.IsCover D)
    {x : Fin k → G}
    (hx : L.IsOccurrence x) :
    ∃ e : OrderedFace k r,
      orderedFaceTuple e x ∈
        liftLowerDeletion D e := by
  classical
  have hxfinset : x ∈ L.occurrenceFinset := by
    exact (L.mem_occurrenceFinset x).2 hx
  obtain ⟨g, hg⟩ := hcover x hxfinset
  obtain ⟨e, i, hei⟩ :=
    exists_orderedCoface hr hrk g
  refine ⟨e, (mem_liftLowerDeletion D e _).2
    ⟨i, ?_⟩⟩
  rw [← hei] at hg
  simpa using hg

end OrderedPattern

namespace GeneratedOrderedPatternRegularization

def IsInAtomBranch
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} {H : WeightedOrderedPattern G k r}
    {ε : ℝ}
    (R : GeneratedOrderedPatternRegularization
      G k r H ε)
    (a : R.TopAtomChoice)
    (w : R.BranchSystem)
    (x : Fin k → G) : Prop :=
  ∀ e i,
    eraseCoordinate i (orderedFaceTuple e x) ∈
      lowerGeneratorCell (R.generators e)
        ((R.state e).partition.representative (a e))
        (w e) i

noncomputable def lowerCellPattern
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} {H : WeightedOrderedPattern G k r}
    {ε : ℝ}
    (R : GeneratedOrderedPatternRegularization
      G k r H ε)
    (a : R.TopAtomChoice)
    (w : R.BranchSystem) :
    OrderedPattern G k (r - 1) where
  edge g z :=
    ∀ (e : OrderedFace k r) (i : Fin r),
      eraseOrderedFace e i = g →
        z ∈ lowerGeneratorCell (R.generators e)
          ((R.state e).partition.representative (a e))
          (w e) i

theorem lowerCellPattern_isOccurrence_iff
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} {H : WeightedOrderedPattern G k r}
    {ε : ℝ}
    (R : GeneratedOrderedPatternRegularization
      G k r H ε)
    (a : R.TopAtomChoice)
    (w : R.BranchSystem)
    (x : Fin k → G) :
    (R.lowerCellPattern a w).IsOccurrence x ↔
      R.IsInAtomBranch a w x := by
  constructor
  · intro hocc e i
    have h :=
      hocc (eraseOrderedFace e i) e i rfl
    simpa using h
  · intro hcell g e i hsubface
    rw [← hsubface]
    simpa using hcell e i

theorem mem_all_topAtoms_iff_exists_branchSystem
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} {H : WeightedOrderedPattern G k r}
    {ε : ℝ}
    (R : GeneratedOrderedPatternRegularization
      G k r H ε)
    (hr : 0 < r)
    (a : R.TopAtomChoice)
    (x : Fin k → G) :
    (∀ e, orderedFaceTuple e x ∈ (a e).1) ↔
      ∃ w : R.BranchSystem,
        R.IsInAtomBranch a w x := by
  classical
  constructor
  · intro hmem
    have he (e : OrderedFace k r) :
        ∃ w : GeneratorBranch (R.generators e),
          ∀ i,
            eraseCoordinate i
                (orderedFaceTuple e x) ∈
              lowerGeneratorCell (R.generators e)
                ((R.state e).partition.representative
                  (a e)) w i := by
      apply
        (R.mem_state_part_iff_exists_lowerGeneratorCells
          hr e _ _).1
      rw [(R.state e).partition.part_representative]
      exact hmem e
    choose w hw using he
    exact ⟨w, fun e i => hw e i⟩
  · rintro ⟨w, hcell⟩
    intro e
    have h :=
      (R.mem_state_part_iff_exists_lowerGeneratorCells
        hr e _ _).2 ⟨w e, hcell e⟩
    rw [(R.state e).partition.part_representative] at h
    exact h

noncomputable def atomEdgeWeight
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} {H : WeightedOrderedPattern G k r}
    {ε : ℝ}
    (R : GeneratedOrderedPatternRegularization
      G k r H ε)
    (a : R.TopAtomChoice)
    (e : OrderedFace k r) : ℝ :=
  (regularizedOrderedPattern H R.state).edgeWeight e
    ((R.state e).partition.representative (a e))

theorem regularized_edgeWeight_eq_atomEdgeWeight
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} {H : WeightedOrderedPattern G k r}
    {ε : ℝ}
    (R : GeneratedOrderedPatternRegularization
      G k r H ε)
    (a : R.TopAtomChoice)
    (e : OrderedFace k r)
    (x : Fin k → G)
    (hmem : orderedFaceTuple e x ∈ (a e).1) :
    (regularizedOrderedPattern H R.state).edgeWeight e
        (orderedFaceTuple e x) =
      R.atomEdgeWeight a e := by
  unfold atomEdgeWeight
  apply conditionalMean_eq_of_mem_part
  rw [(R.state e).partition.part_representative]
  exact hmem

theorem regularized_patternWeight_eq_prod_atomEdgeWeight
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} {H : WeightedOrderedPattern G k r}
    {ε : ℝ}
    (R : GeneratedOrderedPatternRegularization
      G k r H ε)
    (a : R.TopAtomChoice)
    (x : Fin k → G)
    (hmem : ∀ e, orderedFaceTuple e x ∈ (a e).1) :
    (regularizedOrderedPattern H R.state).patternWeight x =
      ∏ e : OrderedFace k r,
        R.atomEdgeWeight a e := by
  apply Finset.prod_congr rfl
  intro e _he
  exact R.regularized_edgeWeight_eq_atomEdgeWeight
    a e x (hmem e)

def IsHeavy
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} {H : WeightedOrderedPattern G k r}
    {ε : ℝ}
    (R : GeneratedOrderedPatternRegularization
      G k r H ε)
    (τ : ℝ) (a : R.TopAtomChoice) : Prop :=
  ∀ e, τ ≤ R.atomEdgeWeight a e

abbrev CellIndex
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} {H : WeightedOrderedPattern G k r}
    {ε : ℝ}
    (R : GeneratedOrderedPatternRegularization
      G k r H ε) :=
  R.TopAtomChoice × R.BranchSystem

@[simp]
theorem card_cellIndex
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} {H : WeightedOrderedPattern G k r}
    {ε : ℝ}
    (R : GeneratedOrderedPatternRegularization
      G k r H ε) :
    Fintype.card R.CellIndex =
      Fintype.card R.TopAtomChoice *
        Fintype.card R.BranchSystem := by
  simp [CellIndex]

theorem card_cellIndex_le
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} {H : WeightedOrderedPattern G k r}
    {ε : ℝ}
    (R : GeneratedOrderedPatternRegularization
      G k r H ε)
    (hr : 0 < r) :
    Fintype.card R.CellIndex ≤
      (∏ e : OrderedFace k r,
        2 ^ R.stepIndex e) *
      ∏ e : OrderedFace k r,
        r ^ R.stepIndex e := by
  rw [R.card_cellIndex]
  exact Nat.mul_le_mul
    R.card_topAtomChoice_le
    (R.card_branchSystem_le hr)

theorem pow_le_regularized_patternWeight_of_lowerCellOccurrence
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} {H : WeightedOrderedPattern G k r}
    {ε τ : ℝ}
    (R : GeneratedOrderedPatternRegularization
      G k r H ε)
    (hr : 0 < r) (hτ : 0 ≤ τ)
    (a : R.TopAtomChoice) (ha : R.IsHeavy τ a)
    (w : R.BranchSystem)
    {x : Fin k → G}
    (hx : (R.lowerCellPattern a w).IsOccurrence x) :
    τ ^ Fintype.card (OrderedFace k r) ≤
      (regularizedOrderedPattern H R.state).patternWeight x := by
  have hcell :
      R.IsInAtomBranch a w x :=
    (R.lowerCellPattern_isOccurrence_iff a w x).1 hx
  have hmem :
      ∀ e, orderedFaceTuple e x ∈ (a e).1 :=
    (R.mem_all_topAtoms_iff_exists_branchSystem
      hr a x).2 ⟨w, hcell⟩
  rw [R.regularized_patternWeight_eq_prod_atomEdgeWeight
    a x hmem]
  have hprod :
      (∏ _e : OrderedFace k r, τ) ≤
        ∏ e : OrderedFace k r,
          R.atomEdgeWeight a e := by
    apply Finset.prod_le_prod₀
    · intro e _he
      exact hτ
    · intro e _he
      exact ha e
  simpa using hprod

theorem pow_mul_lowerCellPattern_weight_le
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} {H : WeightedOrderedPattern G k r}
    {ε τ : ℝ}
    (R : GeneratedOrderedPatternRegularization
      G k r H ε)
    (hH : H.EdgeWeightsInUnitInterval)
    (hr : 0 < r) (hτ : 0 ≤ τ)
    (a : R.TopAtomChoice) (ha : R.IsHeavy τ a)
    (w : R.BranchSystem)
    (x : Fin k → G) :
    τ ^ Fintype.card (OrderedFace k r) *
        (R.lowerCellPattern a w).toWeighted.patternWeight x ≤
      (regularizedOrderedPattern H R.state).patternWeight x := by
  classical
  by_cases hx : (R.lowerCellPattern a w).IsOccurrence x
  · rw [(R.lowerCellPattern a w).toWeighted_patternWeight_of_occurrence
      hx, mul_one]
    exact
      R.pow_le_regularized_patternWeight_of_lowerCellOccurrence
        hr hτ a ha w hx
  · rw [(R.lowerCellPattern a w).toWeighted_patternWeight_of_not_occurrence
      hx, mul_zero]
    exact
      (regularizedOrderedPattern H R.state).patternWeight_nonneg
        (fun e y =>
          ((regularizedOrderedPattern_unitInterval hH R.state)
            e y).1) x

theorem pow_mul_lowerCellPattern_count_le
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ} {H : WeightedOrderedPattern G k r}
    {ε τ : ℝ}
    (R : GeneratedOrderedPatternRegularization
      G k r H ε)
    (hH : H.EdgeWeightsInUnitInterval)
    (hr : 0 < r) (hτ : 0 ≤ τ)
    (a : R.TopAtomChoice) (ha : R.IsHeavy τ a)
    (w : R.BranchSystem) :
    τ ^ Fintype.card (OrderedFace k r) *
        (R.lowerCellPattern a w).toWeighted.patternCount ≤
      (regularizedOrderedPattern H R.state).patternCount := by
  rw [WeightedOrderedPattern.patternCount,
    WeightedOrderedPattern.patternCount,
    ← mean_smul]
  exact mean_mono fun x =>
    R.pow_mul_lowerCellPattern_weight_le
      hH hr hτ a ha w x

theorem lowerCellPattern_count_lt_of_regularized_count_lt
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ} {H : WeightedOrderedPattern G k r}
    {ε τ c : ℝ}
    (R : GeneratedOrderedPatternRegularization
      G k r H ε)
    (hH : H.EdgeWeightsInUnitInterval)
    (hr : 0 < r) (hτ : 0 < τ)
    (a : R.TopAtomChoice) (ha : R.IsHeavy τ a)
    (w : R.BranchSystem)
    (hsmall :
      (regularizedOrderedPattern H R.state).patternCount <
        τ ^ Fintype.card (OrderedFace k r) * c) :
    (R.lowerCellPattern a w).toWeighted.patternCount < c := by
  have hscaled :
      τ ^ Fintype.card (OrderedFace k r) *
          (R.lowerCellPattern a w).toWeighted.patternCount <
        τ ^ Fintype.card (OrderedFace k r) * c :=
    lt_of_le_of_lt
      (R.pow_mul_lowerCellPattern_count_le
        hH hr hτ.le a ha w)
      hsmall
  exact
    lt_of_mul_lt_mul_left hscaled
      (pow_pos hτ
        (Fintype.card (OrderedFace k r))).le

theorem exists_generatedCellCover_of_activeLowerCellCounts
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (H : OrderedPattern G k r)
    {η τ δ ξ cLower : ℝ}
    (R : GeneratedOrderedPatternRegularization
      G k r H.toWeighted η)
    (hr : 0 < r) (hrk : r ≤ k)
    (hτ : 0 < τ) (hδ : 0 ≤ δ)
    (active : R.CellIndex → Prop)
    (exceptionalDeletion :
      OrderedPattern.DeletionFamily (G := G) k r)
    (hexceptionalDensity :
      ∀ e,
        OrderedPattern.faceDeletionDensity
          exceptionalDeletion e ≤ ξ)
    (hexceptionalCover :
      ∀ (a : R.TopAtomChoice) (w : R.BranchSystem)
          (x : Fin k → G),
        R.IsHeavy τ a →
        (R.lowerCellPattern a w).IsOccurrence x →
        ¬ active (a, w) →
          ∃ e,
            orderedFaceTuple e x ∈
              exceptionalDeletion e)
    (hcellSmall :
      ∀ a : R.TopAtomChoice,
        R.IsHeavy τ a →
          ∀ w : R.BranchSystem,
            active (a, w) →
            (R.lowerCellPattern a w).toWeighted.patternCount <
              cLower)
    (hremove :
      ∀ L : OrderedPattern G k (r - 1),
        L.toWeighted.patternCount < cLower →
          ∃ D : OrderedPattern.DeletionFamily
              (G := G) k (r - 1),
            L.IsCover D ∧
              ∀ g,
                OrderedPattern.faceDeletionDensity D g ≤ δ) :
    ∃ D : OrderedPattern.DeletionFamily
        (G := G) k r,
      H.IsCover D ∧
        ∀ e,
          OrderedPattern.faceDeletionDensity D e ≤
            τ +
              (Fintype.card R.CellIndex : ℝ) *
                (r : ℝ) * δ +
              ξ := by
  classical
  have hchoice (p : R.CellIndex) :
      ∃ D : OrderedPattern.DeletionFamily
          (G := G) k (r - 1),
        (R.IsHeavy τ p.1 →
          active p →
          (R.lowerCellPattern p.1 p.2).IsCover D) ∧
        ∀ g,
          OrderedPattern.faceDeletionDensity D g ≤ δ := by
    by_cases hp : R.IsHeavy τ p.1
    · by_cases hactive : active p
      · have hcount :
            (R.lowerCellPattern p.1 p.2).toWeighted.patternCount <
              cLower :=
          hcellSmall p.1 hp p.2 hactive
        obtain ⟨D, hcover, hdensity⟩ :=
          hremove (R.lowerCellPattern p.1 p.2) hcount
        exact ⟨D, fun _ _ => hcover, hdensity⟩
      · refine
          ⟨OrderedPattern.emptyDeletion k (r - 1),
            fun _ h => (hactive h).elim, fun g => ?_⟩
        rw [OrderedPattern.faceDeletionDensity_empty]
        exact hδ
    · refine
        ⟨OrderedPattern.emptyDeletion k (r - 1),
          fun hheavy _ => (hp hheavy).elim, fun g => ?_⟩
      rw [OrderedPattern.faceDeletionDensity_empty]
      exact hδ
  choose lowerDeletion hlower using hchoice
  let liftedCellDeletion :
      R.CellIndex →
        OrderedPattern.DeletionFamily (G := G) k r :=
    fun p =>
      OrderedPattern.liftLowerDeletion
        (lowerDeletion p)
  let cellDeletion :
      OrderedPattern.DeletionFamily (G := G) k r :=
    OrderedPattern.unionDeletion liftedCellDeletion
  let lowDeletion :
      OrderedPattern.DeletionFamily (G := G) k r :=
    OrderedPattern.lowStructuredDeletion
      H R.state τ
  let baseComponents :
      Bool →
        OrderedPattern.DeletionFamily (G := G) k r :=
    fun b => if b then cellDeletion else lowDeletion
  let baseDeletion :
      OrderedPattern.DeletionFamily (G := G) k r :=
    OrderedPattern.unionDeletion baseComponents
  let components :
      Bool →
        OrderedPattern.DeletionFamily (G := G) k r :=
    fun b =>
      if b then exceptionalDeletion else baseDeletion
  let totalDeletion :
      OrderedPattern.DeletionFamily (G := G) k r :=
    OrderedPattern.unionDeletion components
  have hcellDensity (e : OrderedFace k r) :
      OrderedPattern.faceDeletionDensity
          cellDeletion e ≤
        (Fintype.card R.CellIndex : ℝ) *
          (r : ℝ) * δ := by
    calc
      OrderedPattern.faceDeletionDensity
          cellDeletion e ≤
          ∑ p : R.CellIndex,
            OrderedPattern.faceDeletionDensity
              (liftedCellDeletion p) e := by
        exact
          OrderedPattern.faceDeletionDensity_unionDeletion_le
            liftedCellDeletion e
      _ ≤ ∑ _p : R.CellIndex, (r : ℝ) * δ := by
        apply Finset.sum_le_sum
        intro p _hp
        exact
          OrderedPattern.faceDeletionDensity_liftLowerDeletion_le
            (lowerDeletion p) (hlower p).2 e
      _ =
          (Fintype.card R.CellIndex : ℝ) *
            (r : ℝ) * δ := by
        simp
        ring
  have hbaseDensity (e : OrderedFace k r) :
      OrderedPattern.faceDeletionDensity
          baseDeletion e ≤
        τ +
          (Fintype.card R.CellIndex : ℝ) *
            (r : ℝ) * δ := by
    calc
      OrderedPattern.faceDeletionDensity
          baseDeletion e ≤
          ∑ b : Bool,
            OrderedPattern.faceDeletionDensity
              (baseComponents b) e := by
        exact
          OrderedPattern.faceDeletionDensity_unionDeletion_le
            baseComponents e
      _ =
          OrderedPattern.faceDeletionDensity lowDeletion e +
            OrderedPattern.faceDeletionDensity cellDeletion e := by
        simp [baseComponents]
        ring
      _ ≤
          τ +
            (Fintype.card R.CellIndex : ℝ) *
              (r : ℝ) * δ :=
        add_le_add
          (OrderedPattern.faceDeletionDensity_lowStructuredDeletion_le
            H R.state hτ.le e)
          (hcellDensity e)
  have htotalDensity (e : OrderedFace k r) :
      OrderedPattern.faceDeletionDensity
          totalDeletion e ≤
        τ +
          (Fintype.card R.CellIndex : ℝ) *
            (r : ℝ) * δ +
          ξ := by
    calc
      OrderedPattern.faceDeletionDensity
          totalDeletion e ≤
          ∑ b : Bool,
            OrderedPattern.faceDeletionDensity
              (components b) e := by
        exact
          OrderedPattern.faceDeletionDensity_unionDeletion_le
            components e
      _ =
          OrderedPattern.faceDeletionDensity baseDeletion e +
            OrderedPattern.faceDeletionDensity
              exceptionalDeletion e := by
        simp [components]
        ring
      _ ≤
          (τ +
            (Fintype.card R.CellIndex : ℝ) *
              (r : ℝ) * δ) +
            ξ :=
        add_le_add (hbaseDensity e)
          (hexceptionalDensity e)
  refine ⟨totalDeletion, ?_, htotalDensity⟩
  intro x hx
  have hxocc : H.IsOccurrence x :=
    (H.mem_occurrenceFinset x).1 hx
  by_cases hlow :
      ∃ e : OrderedFace k r,
        orderedFaceTuple e x ∈ lowDeletion e
  · obtain ⟨e, he⟩ := hlow
    have hbase :
        orderedFaceTuple e x ∈ baseDeletion e := by
      apply
        (OrderedPattern.mem_unionDeletion
          baseComponents e _).2
      refine ⟨false, ?_⟩
      simpa [baseComponents] using he
    refine ⟨e,
      (OrderedPattern.mem_unionDeletion
        components e _).2 ⟨false, ?_⟩⟩
    simpa [components] using hbase
  · push Not at hlow
    let a : R.TopAtomChoice :=
      R.topAtomChoiceOf x
    have ha : R.IsHeavy τ a := by
      intro e
      have hmem :
          orderedFaceTuple e x ∈ (a e).1 :=
        R.mem_topAtomChoiceOf x e
      rw [← R.regularized_edgeWeight_eq_atomEdgeWeight
        a e x hmem]
      exact
        OrderedPattern.regularized_edgeWeight_ge_of_not_mem_lowDeletion
          H R.state τ e (orderedFaceTuple e x)
          (hxocc e) (hlow e)
    have hbranch :
        ∃ w : R.BranchSystem,
          R.IsInAtomBranch a w x :=
      (R.mem_all_topAtoms_iff_exists_branchSystem
        hr a x).1
        (fun e => R.mem_topAtomChoiceOf x e)
    obtain ⟨w, hw⟩ := hbranch
    have hlowerOccurrence :
        (R.lowerCellPattern a w).IsOccurrence x :=
      (R.lowerCellPattern_isOccurrence_iff
        a w x).2 hw
    by_cases hactive : active (a, w)
    · have hlowerCover :
          (R.lowerCellPattern a w).IsCover
            (lowerDeletion (a, w)) :=
        (hlower (a, w)).1 ha hactive
      obtain ⟨e, he⟩ :=
        OrderedPattern.lowerCover_lifts
          hr hrk (R.lowerCellPattern a w)
          (lowerDeletion (a, w))
          hlowerCover hlowerOccurrence
      have hcell :
          orderedFaceTuple e x ∈ cellDeletion e := by
        apply
          (OrderedPattern.mem_unionDeletion
            liftedCellDeletion e _).2
        exact ⟨(a, w), he⟩
      have hbase :
          orderedFaceTuple e x ∈ baseDeletion e := by
        apply
          (OrderedPattern.mem_unionDeletion
            baseComponents e _).2
        refine ⟨true, ?_⟩
        simpa [baseComponents] using hcell
      refine ⟨e,
        (OrderedPattern.mem_unionDeletion
          components e _).2 ⟨false, ?_⟩⟩
      simpa [components] using hbase
    · obtain ⟨e, he⟩ :=
        hexceptionalCover a w x ha
          hlowerOccurrence hactive
      refine ⟨e,
        (OrderedPattern.mem_unionDeletion
          components e _).2 ⟨true, ?_⟩⟩
      simpa [components] using he

theorem exists_generatedCellCover_of_lowerCellCounts
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (H : OrderedPattern G k r)
    {η τ δ cLower : ℝ}
    (R : GeneratedOrderedPatternRegularization
      G k r H.toWeighted η)
    (hr : 0 < r) (hrk : r ≤ k)
    (hτ : 0 < τ) (hδ : 0 ≤ δ)
    (hcellSmall :
      ∀ a : R.TopAtomChoice,
        R.IsHeavy τ a →
          ∀ w : R.BranchSystem,
            (R.lowerCellPattern a w).toWeighted.patternCount <
              cLower)
    (hremove :
      ∀ L : OrderedPattern G k (r - 1),
        L.toWeighted.patternCount < cLower →
          ∃ D : OrderedPattern.DeletionFamily
              (G := G) k (r - 1),
            L.IsCover D ∧
              ∀ g,
                OrderedPattern.faceDeletionDensity D g ≤ δ) :
    ∃ D : OrderedPattern.DeletionFamily
        (G := G) k r,
      H.IsCover D ∧
        ∀ e,
          OrderedPattern.faceDeletionDensity D e ≤
            τ +
              (Fintype.card R.CellIndex : ℝ) *
                (r : ℝ) * δ := by
  simpa using
    R.exists_generatedCellCover_of_activeLowerCellCounts
      (ξ := 0) H hr hrk hτ hδ
      (fun _ => True)
      (OrderedPattern.emptyDeletion k r)
      (fun e => by
        rw [OrderedPattern.faceDeletionDensity_empty])
      (by
        intro a w x ha hx hnot
        exact (hnot trivial).elim)
      (by
        intro a ha w _hactive
        exact hcellSmall a ha w)
      hremove

theorem exists_generatedCellCover
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (H : OrderedPattern G k r)
    {η τ δ cLower : ℝ}
    (R : GeneratedOrderedPatternRegularization
      G k r H.toWeighted η)
    (hr : 0 < r) (hrk : r ≤ k)
    (hτ : 0 < τ) (hδ : 0 ≤ δ)
    (hsmall :
      (regularizedOrderedPattern
          H.toWeighted R.state).patternCount <
        τ ^ Fintype.card (OrderedFace k r) *
          cLower)
    (hremove :
      ∀ L : OrderedPattern G k (r - 1),
        L.toWeighted.patternCount < cLower →
          ∃ D : OrderedPattern.DeletionFamily
              (G := G) k (r - 1),
            L.IsCover D ∧
              ∀ g,
                OrderedPattern.faceDeletionDensity D g ≤ δ) :
    ∃ D : OrderedPattern.DeletionFamily
        (G := G) k r,
      H.IsCover D ∧
        ∀ e,
          OrderedPattern.faceDeletionDensity D e ≤
            τ +
              (Fintype.card R.CellIndex : ℝ) *
                (r : ℝ) * δ := by
  apply R.exists_generatedCellCover_of_lowerCellCounts
    H hr hrk hτ hδ
  · intro a ha w
    exact
      R.lowerCellPattern_count_lt_of_regularized_count_lt
        H.toWeighted_unitInterval hr hτ
        a ha w hsmall
  · exact hremove

end GeneratedOrderedPatternRegularization

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

def eraseBoundaryCoordinate
    {G : Type*} {j : ℕ}
    (i : Fin (j + 1)) (x : Fin (j + 1) → G) :
    Fin j → G :=
  fun q => x (i.succAbove q)

def eraseBoundaryFace
    {k j : ℕ}
    (e : OrderedFace k (j + 1)) (i : Fin (j + 1)) :
    OrderedFace k j :=
  (Fin.succAboveOrderEmb i).trans e

@[simp]
theorem orderedFaceTuple_eraseBoundaryFace
    {G : Type*} {k j : ℕ}
    (e : OrderedFace k (j + 1)) (i : Fin (j + 1))
    (x : Fin k → G) :
    orderedFaceTuple (eraseBoundaryFace e i) x =
      eraseBoundaryCoordinate i (orderedFaceTuple e x) :=
  rfl

abbrev OrderedFacePartitionSystem
    (G : Type*) [Fintype G] [DecidableEq G]
    (k j : ℕ) :=
  (e : OrderedFace k j) → FacePartition (Fin j → G)

def OrderedFacePartitionRefines
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (fine coarse : OrderedFacePartitionSystem G k j) : Prop :=
  ∀ e, fine e ≤ coarse e

namespace OrderedFacePartitionRefines

theorem refl
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : OrderedFacePartitionSystem G k j) :
    OrderedFacePartitionRefines P P :=
  fun _ => le_rfl

theorem trans
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    {P Q R : OrderedFacePartitionSystem G k j}
    (hPQ : OrderedFacePartitionRefines P Q)
    (hQR : OrderedFacePartitionRefines Q R) :
    OrderedFacePartitionRefines P R :=
  fun e => le_trans (hPQ e) (hQR e)

end OrderedFacePartitionRefines

def indiscreteOrderedFacePartitionSystem
    (G : Type*) [Fintype G] [DecidableEq G]
    (k j : ℕ) :
    OrderedFacePartitionSystem G k j :=
  fun _ => FacePartition.indiscrete

def orderedImmediateBoundaryPartition
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1)) (i : Fin (j + 1)) :
    FacePartition (Fin (j + 1) → G) :=
  FacePartition.pullback (eraseBoundaryCoordinate i)
    (P (eraseBoundaryFace e i))

def orderedBoundaryPartition
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1)) :
    FacePartition (Fin (j + 1) → G) :=
  FacePartition.joinFinset
    (Finset.univ : Finset (Fin (j + 1)))
    (orderedImmediateBoundaryPartition P e)

theorem orderedBoundaryPartition_le_immediate
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1)) (i : Fin (j + 1)) :
    orderedBoundaryPartition P e ≤
      orderedImmediateBoundaryPartition P e i := by
  exact FacePartition.joinFinset_le_of_mem
    (orderedImmediateBoundaryPartition P e)
    (Finset.mem_univ i)

theorem orderedBoundaryPartition_mono
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    {fine coarse : OrderedFacePartitionSystem G k j}
    (hfc : OrderedFacePartitionRefines fine coarse)
    (e : OrderedFace k (j + 1)) :
    orderedBoundaryPartition fine e ≤
      orderedBoundaryPartition coarse e := by
  unfold orderedBoundaryPartition
  apply FacePartition.le_joinFinset_iff.mpr
  intro i _
  exact le_trans
    (orderedBoundaryPartition_le_immediate fine e i)
    (FacePartition.pullback_mono (eraseBoundaryCoordinate i)
      (hfc (eraseBoundaryFace e i)))

theorem mem_orderedBoundaryPartition_part_iff
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (x y : Fin (j + 1) → G) :
    y ∈ (orderedBoundaryPartition P e).part x ↔
      ∀ i : Fin (j + 1),
        eraseBoundaryCoordinate i y ∈
          (P (eraseBoundaryFace e i)).part
            (eraseBoundaryCoordinate i x) := by
  rw [orderedBoundaryPartition,
    FacePartition.mem_part_joinFinset_iff]
  simp only [Finset.mem_univ, forall_const,
    orderedImmediateBoundaryPartition,
    FacePartition.mem_part_pullback_iff_image_mem]

theorem mem_orderedBoundaryPartition_part_iff_part_eq
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (x y : Fin (j + 1) → G) :
    y ∈ (orderedBoundaryPartition P e).part x ↔
      ∀ i : Fin (j + 1),
        (P (eraseBoundaryFace e i)).part
            (eraseBoundaryCoordinate i y) =
          (P (eraseBoundaryFace e i)).part
            (eraseBoundaryCoordinate i x) := by
  rw [mem_orderedBoundaryPartition_part_iff]
  constructor
  · intro h i
    exact
      ((P (eraseBoundaryFace e i)).mem_part_iff_part_eq_part
        (Finset.mem_univ (eraseBoundaryCoordinate i y))
        (Finset.mem_univ (eraseBoundaryCoordinate i x))).1
        (h i)
  · intro h i
    exact
      ((P (eraseBoundaryFace e i)).mem_part_iff_part_eq_part
        (Finset.mem_univ (eraseBoundaryCoordinate i y))
        (Finset.mem_univ (eraseBoundaryCoordinate i x))).2
        (h i)

theorem orderedFaceTuple_mem_boundary_part_iff
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (x y : Fin k → G) :
    orderedFaceTuple e y ∈
        (orderedBoundaryPartition P e).part
          (orderedFaceTuple e x) ↔
      ∀ i : Fin (j + 1),
        orderedFaceTuple (eraseBoundaryFace e i) y ∈
          (P (eraseBoundaryFace e i)).part
            (orderedFaceTuple (eraseBoundaryFace e i) x) := by
  rw [mem_orderedBoundaryPartition_part_iff]
  constructor
  · intro h i
    rw [orderedFaceTuple_eraseBoundaryFace e i y,
      orderedFaceTuple_eraseBoundaryFace e i x]
    exact h i
  · intro h i
    rw [← orderedFaceTuple_eraseBoundaryFace e i y,
      ← orderedFaceTuple_eraseBoundaryFace e i x]
    exact h i

theorem complexity_orderedBoundaryPartition_le
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (P : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1)) :
    FacePartition.complexity
        (orderedBoundaryPartition P e) ≤
      ∏ i : Fin (j + 1),
        FacePartition.complexity
          (P (eraseBoundaryFace e i)) := by
  calc
    FacePartition.complexity
        (orderedBoundaryPartition P e) ≤
        ∏ i : Fin (j + 1),
          FacePartition.complexity
            (orderedImmediateBoundaryPartition P e i) := by
      exact FacePartition.complexity_joinFinset_le
        (Finset.univ : Finset (Fin (j + 1)))
        (orderedImmediateBoundaryPartition P e)
    _ ≤
        ∏ i : Fin (j + 1),
          FacePartition.complexity
            (P (eraseBoundaryFace e i)) := by
      apply Finset.prod_le_prod₀
      · intro i _
        exact Nat.zero_le _
      intro i _
      exact FacePartition.complexity_pullback_le
        (eraseBoundaryCoordinate i) (P (eraseBoundaryFace e i))

theorem complexity_orderedBoundaryPartition_le_pow
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j M : ℕ}
    (P : OrderedFacePartitionSystem G k j)
    (hP : ∀ g, FacePartition.complexity (P g) ≤ M)
    (e : OrderedFace k (j + 1)) :
    FacePartition.complexity
        (orderedBoundaryPartition P e) ≤
      M ^ (j + 1) := by
  calc
    FacePartition.complexity
        (orderedBoundaryPartition P e) ≤
        ∏ i : Fin (j + 1),
          FacePartition.complexity
            (P (eraseBoundaryFace e i)) :=
      complexity_orderedBoundaryPartition_le P e
    _ ≤ ∏ _i : Fin (j + 1), M := by
      apply Finset.prod_le_prod₀
      · intro i _
        exact Nat.zero_le _
      intro i _
      exact hP (eraseBoundaryFace e i)
    _ = M ^ (j + 1) := by simp

noncomputable def orderedBoundaryAtomAt
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (x : Fin (j + 1) → G) :
    (orderedBoundaryPartition P e).parts :=
  ⟨(orderedBoundaryPartition P e).part x,
    (orderedBoundaryPartition P e).part_mem.2
      (Finset.mem_univ x)⟩

@[simp]
theorem orderedBoundaryAtomAt_val
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (x : Fin (j + 1) → G) :
    (orderedBoundaryAtomAt P e x).1 =
      (orderedBoundaryPartition P e).part x :=
  rfl

theorem mem_orderedBoundaryAtomAt_iff
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (x y : Fin (j + 1) → G) :
    y ∈ (orderedBoundaryAtomAt P e x).1 ↔
      ∀ i : Fin (j + 1),
        eraseBoundaryCoordinate i y ∈
          (P (eraseBoundaryFace e i)).part
            (eraseBoundaryCoordinate i x) :=
  mem_orderedBoundaryPartition_part_iff P e x y

noncomputable def orderedBoundaryStructured
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (f : (Fin (j + 1) → G) → ℝ) :
    (Fin (j + 1) → G) → ℝ :=
  conditionalMean (orderedBoundaryPartition P e) f

noncomputable def orderedBoundaryEnergy
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (f : (Fin (j + 1) → G) → ℝ) : ℝ :=
  partitionEnergy (orderedBoundaryPartition P e) f

theorem orderedBoundaryEnergy_mono
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    {fine coarse : OrderedFacePartitionSystem G k j}
    (hfc : OrderedFacePartitionRefines fine coarse)
    (e : OrderedFace k (j + 1))
    (f : (Fin (j + 1) → G) → ℝ) :
    orderedBoundaryEnergy coarse e f ≤
      orderedBoundaryEnergy fine e f :=
  partitionEnergy_mono
    (orderedBoundaryPartition fine e)
    (orderedBoundaryPartition coarse e)
    (orderedBoundaryPartition_mono hfc e) f

theorem orderedBoundaryEnergy_sub_eq_mean_sq
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    {fine coarse : OrderedFacePartitionSystem G k j}
    (hfc : OrderedFacePartitionRefines fine coarse)
    (e : OrderedFace k (j + 1))
    (f : (Fin (j + 1) → G) → ℝ) :
    orderedBoundaryEnergy fine e f -
        orderedBoundaryEnergy coarse e f =
      mean (fun x =>
        (orderedBoundaryStructured fine e f x -
          orderedBoundaryStructured coarse e f x) ^ 2) := by
  exact partitionEnergy_sub_eq_mean_sq
    (orderedBoundaryPartition fine e)
    (orderedBoundaryPartition coarse e)
    (orderedBoundaryPartition_mono hfc e) f

structure OrderedPartitionComplex
    (G : Type*) [Fintype G] [DecidableEq G]
    (k r : ℕ) where
  partition :
    (j : Fin (r + 1)) →
      (e : OrderedFace k j.1) →
        FacePartition (Fin j.1 → G)

namespace OrderedPartitionComplex

def layer
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (j : ℕ) (hj : j ≤ r) :
    OrderedFacePartitionSystem G k j :=
  C.partition ⟨j, Nat.lt_succ_iff.mpr hj⟩

def boundary
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r j : ℕ}
    (C : OrderedPartitionComplex G k r)
    (hj : j < r)
    (e : OrderedFace k (j + 1)) :
    FacePartition (Fin (j + 1) → G) :=
  orderedBoundaryPartition (C.layer j (Nat.le_of_lt hj)) e

def Refines
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (fine coarse : OrderedPartitionComplex G k r) : Prop :=
  ∀ j e, fine.partition j e ≤ coarse.partition j e

theorem Refines.refl
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r) :
    C.Refines C :=
  fun _ _ => le_rfl

theorem Refines.trans
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C D E : OrderedPartitionComplex G k r}
    (hCD : C.Refines D) (hDE : D.Refines E) :
    C.Refines E :=
  fun j e => le_trans (hCD j e) (hDE j e)

theorem boundary_mono
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r j : ℕ}
    {fine coarse : OrderedPartitionComplex G k r}
    (hfc : fine.Refines coarse)
    (hj : j < r)
    (e : OrderedFace k (j + 1)) :
    fine.boundary hj e ≤ coarse.boundary hj e := by
  apply orderedBoundaryPartition_mono
  intro g
  exact hfc
    ⟨j, Nat.lt_succ_iff.mpr (Nat.le_of_lt hj)⟩ g

end OrderedPartitionComplex

end Erdos3.FixedDensity

end

end OAI
