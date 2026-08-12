import KlarnerConstant.Polyomino
import Mathlib.Data.Finset.Union

/-!
# Connected partitions grown from prescribed seeds

This module proves a finite square-grid partition lemma used by polyomino
decompositions.  Inside a finite set of cells, suppose that finitely many
pairwise-disjoint, nonempty, edge-connected seed sets are prescribed.  Assume
that every cell can reach some seed by an edge path staying in the ambient
cell set.  Then the ambient set can be partitioned into edge-connected
territories, one for each seed, such that a territory contains its own seed
and no cell of any other seed.

The proof grows a partial partition one frontier cell at a time.  If a cell is
not yet covered, a path from it to a seed crosses from uncovered to covered
cells.  Adding the uncovered endpoint of that frontier edge to the territory
on the covered side preserves connectedness and disjointness, and strictly
decreases the finite number of uncovered cells.

The reachability hypothesis is a component-free formulation of "every
connected component meets a seed".  It avoids introducing a quotient or a
separate connected-component API and is exactly what the frontier proof uses.
-/

namespace LeanProofs.KlarnerConstant

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The union of a finite indexed family of cell sets. -/
def coveredCells (territories : ι → Finset Cell) : Finset Cell :=
  Finset.univ.biUnion territories

@[simp]
theorem mem_coveredCells {territories : ι → Finset Cell} {c : Cell} :
    c ∈ coveredCells territories ↔ ∃ i, c ∈ territories i := by
  simp [coveredCells]

/-- The union of all designated seed cells. -/
def allSeedCells (seeds : ι → Finset Cell) : Finset Cell :=
  coveredCells seeds

/-- Explicit hypotheses for growing connected territories from seeds.

`reaches_seed` says that each ambient cell is connected, inside `cells`, to
at least one seed.  Equivalently, every edge-connected component of `cells`
contains a seed. -/
structure SeedSystem (ι : Type*) [Fintype ι] where
  cells : Finset Cell
  seeds : ι → Finset Cell
  seed_subset : ∀ i, seeds i ⊆ cells
  seed_nonempty : ∀ i, (seeds i).Nonempty
  seed_connected : ∀ i, EdgeConnected (seeds i)
  seed_pairwise_disjoint :
    ∀ i j, i ≠ j → Disjoint (seeds i) (seeds j)
  reaches_seed :
    ∀ c, c ∈ cells →
      ∃ i s, s ∈ seeds i ∧
        Relation.ReflTransGen (EdgeAdjacentIn cells) c s

/-- A partial assignment of cells to connected seed territories. -/
structure PartialSeededPartition (D : SeedSystem ι) where
  territories : ι → Finset Cell
  territory_subset : ∀ i, territories i ⊆ D.cells
  seed_subset : ∀ i, D.seeds i ⊆ territories i
  territory_connected : ∀ i, EdgeConnected (territories i)
  territory_pairwise_disjoint :
    ∀ i j, i ≠ j → Disjoint (territories i) (territories j)

namespace PartialSeededPartition

theorem covered_subset {D : SeedSystem ι}
    (P : PartialSeededPartition D) :
    coveredCells P.territories ⊆ D.cells := by
  intro c hc
  rcases mem_coveredCells.mp hc with ⟨i, hci⟩
  exact P.territory_subset i hci

theorem territory_subset_covered {D : SeedSystem ι}
    (P : PartialSeededPartition D) (i : ι) :
    P.territories i ⊆ coveredCells P.territories := by
  intro c hc
  exact mem_coveredCells.mpr ⟨i, hc⟩

end PartialSeededPartition

/-- A complete connected partition subordinate to a seed system. -/
structure SeededPartition (D : SeedSystem ι) where
  territories : ι → Finset Cell
  territory_subset : ∀ i, territories i ⊆ D.cells
  seed_subset : ∀ i, D.seeds i ⊆ territories i
  territory_connected : ∀ i, EdgeConnected (territories i)
  territory_pairwise_disjoint :
    ∀ i j, i ≠ j → Disjoint (territories i) (territories j)
  cover : coveredCells territories = D.cells

namespace SeededPartition

/-- Each territory is nonempty because it contains its nonempty seed. -/
theorem territory_nonempty {D : SeedSystem ι}
    (P : SeededPartition D) (i : ι) :
    (P.territories i).Nonempty :=
  (D.seed_nonempty i).mono (P.seed_subset i)

/-- A territory, equipped with its proved nonemptiness and connectedness, is
a polyomino. -/
def territoryPolyomino {D : SeedSystem ι}
    (P : SeededPartition D) (i : ι) : Polyomino where
  cells := P.territories i
  nonempty := P.territory_nonempty i
  edgeConnected := P.territory_connected i

/-- Membership in the ambient cell set is equivalent to membership in some
territory. -/
theorem mem_cells_iff_exists_territory {D : SeedSystem ι}
    (P : SeededPartition D) {c : Cell} :
    c ∈ D.cells ↔ ∃ i, c ∈ P.territories i := by
  rw [← P.cover]
  exact mem_coveredCells

/-- Every ambient cell belongs to a unique territory. -/
theorem mem_cells_iff_existsUnique_territory {D : SeedSystem ι}
    (P : SeededPartition D) {c : Cell} :
    c ∈ D.cells ↔ ∃! i, c ∈ P.territories i := by
  constructor
  · intro hc
    rcases P.mem_cells_iff_exists_territory.mp hc with ⟨i, hci⟩
    refine ⟨i, hci, ?_⟩
    intro j hcj
    by_contra hij
    exact (Finset.disjoint_left.mp
      (P.territory_pairwise_disjoint i j (fun hji ↦ hij hji.symm))) hci hcj
  · rintro ⟨i, hci, _⟩
    exact P.territory_subset i hci

/-- A territory contains no cell of another designated seed. -/
theorem disjoint_foreign_seed {D : SeedSystem ι}
    (P : SeededPartition D) {i j : ι} (hij : i ≠ j) :
    Disjoint (P.territories i) (D.seeds j) := by
  apply Finset.disjoint_left.mpr
  intro c hci hcj
  exact (Finset.disjoint_left.mp
    (P.territory_pairwise_disjoint i j hij)) hci
      (P.seed_subset j hcj)

/-- Intersecting a territory with the union of all seeds recovers exactly its
designated seed set. -/
theorem inter_allSeedCells {D : SeedSystem ι}
    (P : SeededPartition D) (i : ι) :
    P.territories i ∩ allSeedCells D.seeds = D.seeds i := by
  ext c
  constructor
  · intro hc
    rcases Finset.mem_inter.mp hc with ⟨hct, hca⟩
    rcases mem_coveredCells.mp hca with ⟨j, hcj⟩
    by_cases hij : i = j
    · simpa [hij] using hcj
    · exfalso
      exact (Finset.disjoint_left.mp (P.disjoint_foreign_seed hij)) hct hcj
  · intro hc
    exact Finset.mem_inter.mpr
      ⟨P.seed_subset i hc, mem_coveredCells.mpr ⟨i, hc⟩⟩

/-- Adding any separately recorded forced cells preserves the reconstruction
identity supplied by the territories. -/
theorem forced_union_covered {D : SeedSystem ι}
    (P : SeededPartition D) (forced : Finset Cell) :
    forced ∪ coveredCells P.territories = forced ∪ D.cells := by
  rw [P.cover]

end SeededPartition

private theorem edgePath_mono_insert {t : Finset Cell} {x a b : Cell}
    (h : Relation.ReflTransGen (EdgeAdjacentIn t) a b) :
    Relation.ReflTransGen (EdgeAdjacentIn (insert x t)) a b := by
  exact Relation.ReflTransGen.mono (fun _ _ huv ↦
    ⟨Finset.mem_insert_of_mem huv.1,
      Finset.mem_insert_of_mem huv.2.1, huv.2.2⟩) a b h

/-- Attaching one cell by an edge to a connected cell set preserves edge
connectedness. -/
private theorem edgeConnected_insert_of_adjacent {t : Finset Cell}
    (ht : EdgeConnected t) {x a : Cell} (ha : a ∈ t)
    (hxa : EdgeAdjacent x a) : EdgeConnected (insert x t) := by
  have hxaIn : EdgeAdjacentIn (insert x t) x a :=
    ⟨Finset.mem_insert_self x t, Finset.mem_insert_of_mem ha, hxa⟩
  have haxIn : EdgeAdjacentIn (insert x t) a x :=
    ⟨Finset.mem_insert_of_mem ha, Finset.mem_insert_self x t,
      edgeAdjacent_symm hxa⟩
  intro u hu v hv
  rcases Finset.mem_insert.mp hu with hux | hut
  · subst u
    rcases Finset.mem_insert.mp hv with hvx | hvt
    · subst v
      exact Relation.ReflTransGen.refl
    · exact
        (Relation.ReflTransGen.single hxaIn).trans
          (edgePath_mono_insert (x := x) (ht a ha v hvt))
  · rcases Finset.mem_insert.mp hv with hvx | hvt
    · subst v
      exact
        (edgePath_mono_insert (x := x) (ht u hut a ha)).trans
          (Relation.ReflTransGen.single haxIn)
    · exact edgePath_mono_insert (x := x) (ht u hut v hvt)

/-- Replace territory `owner` by the result of adjoining `x`. -/
def extendTerritories (territories : ι → Finset Cell)
    (owner : ι) (x : Cell) : ι → Finset Cell :=
  fun i ↦ if i = owner then insert x (territories i) else territories i

@[simp]
theorem extendTerritories_same (territories : ι → Finset Cell)
    (owner : ι) (x : Cell) :
    extendTerritories territories owner x owner =
      insert x (territories owner) := by
  simp [extendTerritories]

theorem extendTerritories_of_ne (territories : ι → Finset Cell)
    {owner i : ι} (hi : i ≠ owner) (x : Cell) :
    extendTerritories territories owner x i = territories i := by
  simp [extendTerritories, hi]

/-- Adjoining `x` to one territory adjoins exactly `x` to the covered set. -/
theorem coveredCells_extend (territories : ι → Finset Cell)
    (owner : ι) (x : Cell) :
    coveredCells (extendTerritories territories owner x) =
      insert x (coveredCells territories) := by
  ext c
  constructor
  · intro hc
    rcases mem_coveredCells.mp hc with ⟨i, hci⟩
    by_cases hi : i = owner
    · subst i
      rw [extendTerritories_same] at hci
      rcases Finset.mem_insert.mp hci with rfl | hci
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem
          (mem_coveredCells.mpr ⟨owner, hci⟩)
    · exact Finset.mem_insert.mpr
        (Or.inr (mem_coveredCells.mpr
          ⟨i, by simpa [extendTerritories, hi] using hci⟩))
  · intro hc
    rcases Finset.mem_insert.mp hc with rfl | hc
    · exact mem_coveredCells.mpr
        ⟨owner, by simp [extendTerritories]⟩
    · rcases mem_coveredCells.mp hc with ⟨i, hci⟩
      by_cases hi : i = owner
      · subst i
        exact mem_coveredCells.mpr
          ⟨owner, by simp [extendTerritories, hci]⟩
      · exact mem_coveredCells.mpr
          ⟨i, by simpa [extendTerritories, hi] using hci⟩

namespace PartialSeededPartition

/-- Extend one partial territory by a fresh adjacent ambient cell. -/
def extend {D : SeedSystem ι} (P : PartialSeededPartition D)
    (owner : ι) (x : Cell) (hxCells : x ∈ D.cells)
    (a : Cell) (ha : a ∈ P.territories owner)
    (hxa : EdgeAdjacent x a)
    (hxFresh : x ∉ coveredCells P.territories) :
    PartialSeededPartition D where
  territories := extendTerritories P.territories owner x
  territory_subset := by
    intro i c hc
    by_cases hi : i = owner
    · subst i
      rw [extendTerritories_same] at hc
      rcases Finset.mem_insert.mp hc with rfl | hc
      · exact hxCells
      · exact P.territory_subset owner hc
    · rw [extendTerritories_of_ne P.territories hi x] at hc
      exact P.territory_subset i hc
  seed_subset := by
    intro i c hc
    by_cases hi : i = owner
    · subst i
      rw [extendTerritories_same]
      exact Finset.mem_insert_of_mem (P.seed_subset owner hc)
    · rw [extendTerritories_of_ne P.territories hi x]
      exact P.seed_subset i hc
  territory_connected := by
    intro i
    by_cases hi : i = owner
    · subst i
      rw [extendTerritories_same]
      exact edgeConnected_insert_of_adjacent
        (P.territory_connected owner) ha hxa
    · rw [extendTerritories_of_ne P.territories hi x]
      exact P.territory_connected i
  territory_pairwise_disjoint := by
    intro i j hij
    apply Finset.disjoint_left.mpr
    intro c hci hcj
    by_cases hi : i = owner
    · subst i
      have hj : j ≠ owner := by
        intro h
        exact hij h.symm
      rw [extendTerritories_same] at hci
      rw [extendTerritories_of_ne P.territories hj x] at hcj
      rcases Finset.mem_insert.mp hci with rfl | hci
      · exact hxFresh (mem_coveredCells.mpr ⟨j, hcj⟩)
      · exact (Finset.disjoint_left.mp
          (P.territory_pairwise_disjoint owner j hij)) hci hcj
    · rw [extendTerritories_of_ne P.territories hi x] at hci
      by_cases hj : j = owner
      · subst j
        rw [extendTerritories_same] at hcj
        rcases Finset.mem_insert.mp hcj with rfl | hcj
        · exact hxFresh (mem_coveredCells.mpr ⟨i, hci⟩)
        · exact (Finset.disjoint_left.mp
            (P.territory_pairwise_disjoint i owner hi)) hci hcj
      · rw [extendTerritories_of_ne P.territories hj x] at hcj
        exact (Finset.disjoint_left.mp
          (P.territory_pairwise_disjoint i j hij)) hci hcj

@[simp]
theorem covered_extend {D : SeedSystem ι}
    (P : PartialSeededPartition D) (owner : ι) (x : Cell)
    (hxCells : x ∈ D.cells) (a : Cell)
    (ha : a ∈ P.territories owner) (hxa : EdgeAdjacent x a)
    (hxFresh : x ∉ coveredCells P.territories) :
    coveredCells (P.extend owner x hxCells a ha hxa hxFresh).territories =
      insert x (coveredCells P.territories) := by
  exact coveredCells_extend P.territories owner x

end PartialSeededPartition

/-- A path from an uncovered cell to a covered cell crosses a frontier edge
from an uncovered ambient cell to a covered ambient cell. -/
private theorem exists_frontier_of_path {cells assigned : Finset Cell}
    {x y : Cell} (hx : x ∉ assigned) (hy : y ∈ assigned)
    (hpath : Relation.ReflTransGen (EdgeAdjacentIn cells) x y) :
    ∃ u, u ∈ cells ∧ u ∉ assigned ∧
      ∃ v, v ∈ cells ∧ v ∈ assigned ∧ EdgeAdjacent u v := by
  revert hx hy
  induction hpath with
  | refl =>
      intro hx hy
      exact (hx hy).elim
  | @tail b c hxb hbc ih =>
      intro hx hy
      by_cases hb : b ∈ assigned
      · exact ih hx hb
      · exact ⟨b, hbc.1, hb, c, hbc.2.1, hy, hbc.2.2⟩

namespace SeedSystem

/-- The seeds themselves form the initial partial partition. -/
def initialPartial (D : SeedSystem ι) : PartialSeededPartition D where
  territories := D.seeds
  territory_subset := D.seed_subset
  seed_subset := fun _ ↦ Finset.Subset.rfl
  territory_connected := D.seed_connected
  territory_pairwise_disjoint := D.seed_pairwise_disjoint

private theorem exists_completion_aux (D : SeedSystem ι) (n : ℕ)
    (P : PartialSeededPartition D)
    (hcard : (D.cells \ coveredCells P.territories).card = n) :
    Nonempty (SeededPartition D) := by
  induction n using Nat.strong_induction_on generalizing P with
  | h n ih =>
      by_cases hcover : coveredCells P.territories = D.cells
      · exact ⟨{
          territories := P.territories
          territory_subset := P.territory_subset
          seed_subset := P.seed_subset
          territory_connected := P.territory_connected
          territory_pairwise_disjoint := P.territory_pairwise_disjoint
          cover := hcover }⟩
      · have hremaining :
            (D.cells \ coveredCells P.territories).Nonempty := by
          by_contra hempty
          have heq : D.cells \ coveredCells P.territories = ∅ :=
            Finset.not_nonempty_iff_eq_empty.mp hempty
          have hsub : D.cells ⊆ coveredCells P.territories := by
            intro c hc
            by_contra hnc
            have hm : c ∈ D.cells \ coveredCells P.territories :=
              Finset.mem_sdiff.mpr ⟨hc, hnc⟩
            rw [heq] at hm
            simpa using hm
          exact hcover (Finset.Subset.antisymm P.covered_subset hsub)
        rcases hremaining with ⟨c, hc⟩
        rcases Finset.mem_sdiff.mp hc with ⟨hcCells, hcFresh⟩
        rcases D.reaches_seed c hcCells with
          ⟨seedOwner, s, hsSeed, hpath⟩
        have hsTerritory : s ∈ P.territories seedOwner :=
          P.seed_subset seedOwner hsSeed
        have hsCovered : s ∈ coveredCells P.territories :=
          mem_coveredCells.mpr ⟨seedOwner, hsTerritory⟩
        rcases exists_frontier_of_path hcFresh hsCovered hpath with
          ⟨u, huCells, huFresh, v, _hvCells, hvCovered, huv⟩
        rcases mem_coveredCells.mp hvCovered with ⟨owner, hvTerritory⟩
        let P' : PartialSeededPartition D :=
          P.extend owner u huCells v hvTerritory huv huFresh
        have hcovered' :
            coveredCells P'.territories =
              insert u (coveredCells P.territories) := by
          simpa only [P'] using
            P.covered_extend owner u huCells v hvTerritory huv huFresh
        have hstrict :
            D.cells \ coveredCells P'.territories ⊂
              D.cells \ coveredCells P.territories := by
          rw [hcovered']
          rw [Finset.ssubset_iff_subset_ne]
          constructor
          · intro z hz
            rcases Finset.mem_sdiff.mp hz with ⟨hzCells, hzNot⟩
            exact Finset.mem_sdiff.mpr
              ⟨hzCells, fun hzOld ↦
                hzNot (Finset.mem_insert_of_mem hzOld)⟩
          · intro heq
            have huOld :
                u ∈ D.cells \ coveredCells P.territories :=
              Finset.mem_sdiff.mpr ⟨huCells, huFresh⟩
            have huNew :
                u ∉ D.cells \ insert u (coveredCells P.territories) := by
              intro hu
              exact (Finset.mem_sdiff.mp hu).2 (Finset.mem_insert_self _ _)
            rw [heq] at huNew
            exact huNew huOld
        have hlt :
            (D.cells \ coveredCells P'.territories).card < n := by
          have hlt' := Finset.card_lt_card hstrict
          rw [hcard] at hlt'
          exact hlt'
        exact ih _ hlt P' rfl

/-- A finite seed system has a connected partition subordinate to its seeds. -/
theorem exists_seededPartition (D : SeedSystem ι) :
    Nonempty (SeededPartition D) := by
  apply D.exists_completion_aux
    (D.cells \ coveredCells D.initialPartial.territories).card
    D.initialPartial
  rfl

/-- Choose one connected partition.  All mathematical properties of the
choice are exposed by `SeededPartition`; no computation depends on which
valid frontier-growth order is selected. -/
noncomputable def choosePartition (D : SeedSystem ι) : SeededPartition D :=
  Classical.choice D.exists_seededPartition

end SeedSystem

end LeanProofs.KlarnerConstant
