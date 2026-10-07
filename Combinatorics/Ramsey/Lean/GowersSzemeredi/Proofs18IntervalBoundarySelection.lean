import GowersSzemeredi.Proofs18IntervalBoundaryBand
import GowersSzemeredi.Proofs18ExceptionalCellSelection

/-! Small modular diameter bounds the total mass of cells crossing an
interval boundary, allowing relative-density selection inside the interval. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- Membership in the full embedded interval is determined by its standard
representative. -/
theorem mem_finiteIntervalSupport {N L : Nat} [NeZero N] (hL : L ≤ N) (x : ZMod N) :
    x ∈ finiteIntervalImage N (Finset.univ : Finset (Fin L)) ↔ x.val < L := by
  constructor
  · exact finiteIntervalImage_val_lt hL Finset.univ
  · intro hx
    exact Finset.mem_image.mpr ⟨⟨x.val, hx⟩, Finset.mem_univ _, ZMod.natCast_zmod_val x⟩

/-- In a partition into small-diameter cells, the entire crossing-cell
family has mass at most 4*floor(epsilon*N)+2. -/
theorem interval_crossing_cells_mass {N M L : Nat} [NeZero N]
    (P : Fin M → ModAP N) (hL : L ≤ N) (epsilon : Real)
    (hpart : IsPartition (fun i ↦ (P i).carrier) Finset.univ)
    (hdiam : ∀ i, diameterAtMostReal (P i).carrier (epsilon * N)) :
    ∃ B : Finset (Fin M),
      (∀ i, i ∉ B → (P i).carrier ⊆ finiteIntervalImage N (Finset.univ : Finset (Fin L)) ∨
        Disjoint (P i).carrier (finiteIntervalImage N (Finset.univ : Finset (Fin L)))) ∧
      (∑ i ∈ B, (P i).carrier.card) ≤ 4 * Nat.floor (epsilon * N) + 2 := by
  classical
  let S := finiteIntervalImage N (Finset.univ : Finset (Fin L))
  let B := Finset.univ.filter (fun i ↦ ¬ (P i).carrier ⊆ S ∧ ¬ Disjoint (P i).carrier S)
  refine ⟨B, ?_, ?_⟩
  · intro i hi
    by_cases hsub : (P i).carrier ⊆ S
    · exact Or.inl hsub
    · right
      by_contra hdis
      exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsub, hdis⟩)
  · have hcell (i : Fin M) (hi : i ∈ B) :
        (P i).carrier ⊆ intervalBoundaryBand N L (Nat.floor (epsilon * N)) := by
      obtain ⟨hsub, hdis⟩ := (Finset.mem_filter.mp hi).2
      obtain ⟨d, hd, hdreal⟩ := hdiam i
      have hdD : d ≤ Nat.floor (epsilon * N) := Nat.le_floor hdreal
      obtain ⟨y, hy, hyS⟩ := Finset.not_subset.mp hsub
      obtain ⟨x, hxP, hxS⟩ := Finset.not_disjoint_iff.mp hdis
      have hx : x.val < L := (mem_finiteIntervalSupport hL x).mp hxS
      have hyL : L ≤ y.val := Nat.le_of_not_gt (fun hyL ↦ hyS ((mem_finiteIntervalSupport hL y).mpr hyL))
      exact (crossing_cell_subset_intervalBoundaryBand (P i).carrier L d hd ⟨x, hxP, hx⟩ ⟨y, hy, hyL⟩).trans
        (intervalBoundaryBand_mono N L hdD)
    have hdisjoint : (↑B : Set (Fin M)).PairwiseDisjoint (fun i ↦ (P i).carrier) := by
      intro i _ j _ hij
      exact hpart.2 i j (bne_iff_ne.mpr hij)
    calc
      _ = (B.biUnion (fun i ↦ (P i).carrier)).card := (Finset.card_biUnion hdisjoint).symm
      _ ≤ (intervalBoundaryBand N L (Nat.floor (epsilon * N))).card := by
        apply Finset.card_le_card
        intro x hx
        obtain ⟨i, hi, hxP⟩ := Finset.mem_biUnion.mp hx
        exact hcell i hi hxP
      _ ≤ _ := intervalBoundaryBand_card _ _ _

/-- A small-diameter discrepancy partition produces a long cell contained
in the embedded interval with a positive increment in its original density. -/
theorem interval_small_diameter_relative_increment {N M L : Nat} [NeZero N]
    (P : Fin M → ModAP N) (hL : L ≤ N) (A : Finset (ZMod N)) (delta beta : Real)
    (hAS : A ⊆ finiteIntervalImage N (Finset.univ : Finset (Fin L)))
    (hδ : 0 ≤ delta) (hδone : delta ≤ 1) (hβ : 0 < beta)
    (hcard : (A.card : Real) = delta * L)
    (hpart : IsPartition (fun i ↦ (P i).carrier) Finset.univ)
    (hdiam : ∀ i, diameterAtMostReal (P i).carrier (beta / 64 * N))
    (hscale : 32 ≤ beta * N)
    (hdis : beta * N ≤ ∑ i, ‖∑ x ∈ (P i).carrier,
      relativeBalanced A (finiteIntervalImage N (Finset.univ : Finset (Fin L))) delta x‖) :
    ∃ j : Fin M,
      (P j).carrier ⊆ finiteIntervalImage N (Finset.univ : Finset (Fin L)) ∧
      beta * N / (8 * M) ≤ ((P j).carrier.card : Real) ∧
      (delta + beta / 8) * (P j).carrier.card ≤ (A ∩ (P j).carrier).card := by
  obtain ⟨B, hgood, hbadNat⟩ := interval_crossing_cells_mass P hL (beta / 64) hpart hdiam
  have hbad : ∑ i ∈ B, ((P i).carrier.card : Real) ≤ beta * N / 8 := by
    have hc : (∑ i ∈ B, ((P i).carrier.card : Real)) ≤
        4 * (Nat.floor (beta / 64 * N) : Real) + 2 := by exact_mod_cast hbadNat
    have hf := Nat.floor_le (show (0 : Real) ≤ beta / 64 * N by positivity)
    linarith only [hc, hf, hscale]
  have hcard' : (A.card : Real) = delta * (finiteIntervalImage N (Finset.univ : Finset (Fin L))).card := by
    simpa only [finiteIntervalImage_card hL, Finset.card_univ, Fintype.card_fin] using hcard
  obtain ⟨j, _, hsub, hsize, hinc⟩ := relative_density_increment_away_from_boundary A _ delta beta P B
    hAS hδ hδone hβ hcard' hpart hgood hbad hdis
  exact ⟨j, hsub, hsize, hinc⟩

end LeanProofs.GowersSzemeredi
