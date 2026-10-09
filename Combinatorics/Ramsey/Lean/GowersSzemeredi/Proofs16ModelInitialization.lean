import GowersSzemeredi.Proofs16GlobalColumnModels
import GowersSzemeredi.Proofs16ModelEliminationRounds

/-! Initialize elimination from the models of four-term alternating lists.
Models vanishing on the kernel neighborhood already give zero relations. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def columnQuadAnchor {N : Nat} (q : Fin 4 → ZMod N) : ColumnAnchorTuple N 3 :=
  (q 0, ![q 1, q 2, q 3])

theorem columnQuadAnchor_list {N : Nat} (q : Fin 4 → ZMod N) :
    columnAnchorList (columnQuadAnchor q) = [q 0,q 1,q 2,q 3] := by
  simp [columnAnchorList,columnQuadAnchor,List.ofFn_succ]

theorem columnQuadAnchor_eval {N : Nat} (q : Fin 4 → ZMod N) (f : ZMod N → ZMod N) :
    columnAnchorEval f (columnAnchorList (columnQuadAnchor q)) =
      f (q 0)-f (q 1)+f (q 2)-f (q 3) := by
  rw [columnQuadAnchor_list]
  simp only [columnAnchorEval]
  abel

/-- A full model cover splits into already-zero relations and active models.
The conclusion uses the smaller of the comparison and kernel radii. -/
theorem column_models_initialize {J : Type*} {N : Nat} [NeZero N]
    (A Gamma : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (I : Finset J)
    (f : J → ZMod N → ZMod N) (r u : Real)
    (hcover : ∀ a ∈ columnAnchorFibre A 3 0, ∃ j ∈ I,
      ∀ y ∈ bohr Gamma r, (∀ x ∈ columnAnchorList a, y ∈ bohr (T x) r) →
        columnAnchorEval (fun x => L x y) (columnAnchorList a) = f j y) :
    ColumnQuadModelAlternatives A Gamma T L (min r u) r
      (I.filter (fun j => ∃ y ∈ bohr Gamma u, f j y ≠ 0)) f := by
  intro q hq hadd
  have hqa : columnQuadAnchor q ∈ columnAnchorFibre A 3 0 := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_,?_⟩
    · simp [columnQuadAnchor_list, hq]
    · simpa only [columnQuadAnchor_eval,id_eq] using hadd
  obtain ⟨j,hj,hmodel⟩ := hcover _ hqa
  have hm : ∀ y ∈ bohr Gamma r, (∀ i, y ∈ bohr (T (q i)) r) →
      columnQuadValue L q y = f j y := by
    intro y hy hdom
    have hd : ∀ x ∈ columnAnchorList (columnQuadAnchor q), y ∈ bohr (T x) r := by
      simp [columnQuadAnchor_list, hdom]
    simpa only [columnQuadAnchor_eval,columnQuadValue] using hmodel y hy hd
  by_cases hactive : ∃ y ∈ bohr Gamma u, f j y ≠ 0
  · exact Or.inr ⟨j,Finset.mem_filter.mpr ⟨hj,hactive⟩,hm⟩
  · left
    intro y hy hd
    have hz : f j y = 0 := by
      by_contra hne
      exact hactive ⟨y,bohr_mono_radius _ (min_le_right _ _) hy,hne⟩
    exact (hm y (bohr_mono_radius _ (min_le_left _ _) hy)
      (fun i => bohr_mono_radius _ (min_le_left _ _) (hd i))).trans hz

end LeanProofs.GowersSzemeredi
