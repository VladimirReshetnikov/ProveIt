import GowersSzemeredi.Proofs16PairedTupleChains
import GowersSzemeredi.Proofs16ColumnImageBridges

/-! The endpoint domain and Freiman defect of a four-pair/eight-column
configuration, and finite product bounds for sums of local images. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def pairedColumnSpectrum {N : Nat} (T : ZMod N → Finset (ZMod N)) (q : PairedColumnTuple N) :
    Finset (ZMod N) := Finset.univ.biUnion fun i => T (q i).1 ∪ T (q i).2

def pairedColumnDefect {N : Nat} (L : ZMod N → ZMod N → ZMod N) (q : PairedColumnTuple N)
    (y : ZMod N) : ZMod N := ∑ i, (L (q i).1 y-L (q i).2 y)

def PairedColumnImageRelation {N : Nat} [NeZero N] (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (rho : Real) (K : Nat) (q : PairedColumnTuple N) : Prop :=
  ((bohr (pairedColumnSpectrum T q) rho).image (pairedColumnDefect L q)).card ≤ K

theorem mem_paired_column_spectrum_bohr {N : Nat} [NeZero N]
    (T : ZMod N → Finset (ZMod N)) (q : PairedColumnTuple N) (rho : Real) (y : ZMod N) :
    y ∈ bohr (pairedColumnSpectrum T q) rho ↔
      ∀ i, y ∈ bohr (T (q i).1) rho ∧ y ∈ bohr (T (q i).2) rho := by
  constructor
  · intro hy i
    constructor
    · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun t ht => ?_⟩
      exact (Finset.mem_filter.mp hy).2 t (Finset.mem_biUnion.mpr
        ⟨i,Finset.mem_univ _,Finset.mem_union_left _ ht⟩)
    · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun t ht => ?_⟩
      exact (Finset.mem_filter.mp hy).2 t (Finset.mem_biUnion.mpr
        ⟨i,Finset.mem_univ _,Finset.mem_union_right _ ht⟩)
  · intro hy
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun t ht => ?_⟩
    obtain ⟨i,_,ht⟩ := Finset.mem_biUnion.mp ht
    rcases Finset.mem_union.mp ht with ht | ht
    · exact (Finset.mem_filter.mp (hy i).1).2 t ht
    · exact (Finset.mem_filter.mp (hy i).2).2 t ht

theorem paired_column_spectrum_card {N d : Nat} (T : ZMod N → Finset (ZMod N))
    (q : PairedColumnTuple N) (hT : ∀ i, (T (q i).1).card ≤ d ∧ (T (q i).2).card ≤ d) :
    (pairedColumnSpectrum T q).card ≤ 8*d := by
  apply Finset.card_biUnion_le.trans
  calc (∑ i : Fin 4, (T (q i).1 ∪ T (q i).2).card) ≤ ∑ _i : Fin 4, 2*d :=
      Finset.sum_le_sum fun i _ => (Finset.card_union_le _ _).trans (by
        have := (hT i).1
        have := (hT i).2
        omega)
    _ = _ := by simp; ring

/-- The endpoint defect is Freiman-linear before auxiliary constraints are removed. -/
theorem paired_column_defect_freiman {N : Nat} [NeZero N]
    (T : ZMod N → Finset (ZMod N)) (L : ZMod N → ZMod N → ZMod N)
    (q : PairedColumnTuple N) (rho : Real)
    (hL : ∀ i, IsFreimanLinearOn (bohr (T (q i).1) rho) (L (q i).1) ∧
      IsFreimanLinearOn (bohr (T (q i).2) rho) (L (q i).2)) :
    IsFreimanLinearOn (bohr (pairedColumnSpectrum T q) rho) (pairedColumnDefect L q) := by
  intro a b c e ha hb hc he hadd
  have hm := fun y hy => (mem_paired_column_spectrum_bohr T q rho y).mp hy
  have hf : ∀ i, (L (q i).1 a-L (q i).2 a)+(L (q i).1 b-L (q i).2 b) =
      (L (q i).1 c-L (q i).2 c)+(L (q i).1 e-L (q i).2 e) := by
    intro i
    have ea := (hL i).1 a b c e (hm a ha i).1 (hm b hb i).1 (hm c hc i).1 (hm e he i).1 hadd
    have eb := (hL i).2 a b c e (hm a ha i).2 (hm b hb i).2 (hm c hc i).2 (hm e he i).2 hadd
    linear_combination ea-eb
  dsimp only [pairedColumnDefect]
  rw [←Finset.sum_add_distrib, ←Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => hf i

/-- A sum takes at most the product of its summands' finite image sizes. -/
theorem image_sum_defects_card_le {V H I : Type*} [AddCommGroup H] [DecidableEq H] [Fintype I]
    (D : Finset V) (f : I → V → H) (K : I → Nat) (hK : ∀ i, (D.image (f i)).card ≤ K i) :
    (D.image (fun y => ∑ i, f i y)).card ≤ ∏ i, K i := by
  let P := Fintype.piFinset fun i => D.image (f i)
  have hsub : D.image (fun y => ∑ i, f i y) ⊆ P.image (fun g => ∑ i, g i) := by
    intro z hz
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_image.mpr ⟨fun i => f i y,
      Fintype.mem_piFinset.mpr (fun i => Finset.mem_image_of_mem (f i) hy),rfl⟩
  calc (D.image (fun y => ∑ i, f i y)).card ≤ (P.image (fun g => ∑ i, g i)).card := Finset.card_le_card hsub
    _ ≤ P.card := Finset.card_image_le
    _ = ∏ i, (D.image (f i)).card := Fintype.card_piFinset _
    _ ≤ _ := Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun i _ => hK i)

/-- The four shared-anchor defects telescope to the original eight-column defect. -/
theorem paired_column_chain_defect {N : Nat} (L : ZMod N → ZMod N → ZMod N)
    (q : PairedColumnTuple N) (u y : ZMod N) :
    pairedColumnDefect L q y = ∑ i : Fin 4, columnQuadDefect L (q i).1 (q i).2
      (u+pairedTupleShift q (i+1)) (u+pairedTupleShift q i) y := by
  rw [pairedColumnDefect, Fin.sum_univ_four, Fin.sum_univ_four]
  change ((L (q 0).1 y-L (q 0).2 y)+(L (q 1).1 y-L (q 1).2 y)+
      (L (q 2).1 y-L (q 2).2 y)+(L (q 3).1 y-L (q 3).2 y)) =
    (L (q 0).1 y-L (q 0).2 y-L (u+pairedTupleShift q 1) y+L (u+pairedTupleShift q 0) y)+
    (L (q 1).1 y-L (q 1).2 y-L (u+pairedTupleShift q 2) y+L (u+pairedTupleShift q 1) y)+
    (L (q 2).1 y-L (q 2).2 y-L (u+pairedTupleShift q 3) y+L (u+pairedTupleShift q 2) y)+
    (L (q 3).1 y-L (q 3).2 y-L (u+pairedTupleShift q 0) y+L (u+pairedTupleShift q 3) y)
  ring

end LeanProofs.GowersSzemeredi
