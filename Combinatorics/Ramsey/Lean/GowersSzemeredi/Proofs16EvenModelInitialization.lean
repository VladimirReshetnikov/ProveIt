import GowersSzemeredi.Proofs16EvenModelEliminationRounds
import GowersSzemeredi.Proofs16ModelCoverZeroCore

/-! Instantiate the even-list alternatives from complete anchor-fibre covers. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem exists_columnAnchorTuple_of_length {N m : Nat} (as : List (ZMod N))
    (hlen : as.length = m+1) : ∃ a : ColumnAnchorTuple N m, columnAnchorList a = as := by
  cases as with
  | nil => simp at hlen
  | cons x xs =>
    have hm : m = xs.length := by simp only [List.length_cons] at hlen; omega
    subst m
    exact ⟨(x,xs.get),by simp [columnAnchorList,List.ofFn_get]⟩

/-- Inactive models already vanish on the kernel neighborhood; all other
models retain their comparisons at the original testing radius. -/
theorem even_models_initialize {J : Type*} {N k : Nat} [NeZero N] [NeZero k]
    (A Gamma : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (I : Finset J)
    (f : J → ZMod N → ZMod N) (r u : Real)
    (hcover : ∀ a ∈ columnAnchorFibre A (2*k-1) 0, ∃ j ∈ I,
      ∀ y ∈ bohr Gamma r, (∀ x ∈ columnAnchorList a, y ∈ bohr (T x) r) →
        columnAnchorEval (fun x => L x y) (columnAnchorList a) = f j y) :
    ColumnEvenModelAlternatives A Gamma T L k (min r u) r
      (I.filter (fun j => ∃ y ∈ bohr Gamma u, f j y ≠ 0)) f := by
  intro as hlen has hadd
  have hk := NeZero.pos k
  obtain ⟨a,ha⟩ := exists_columnAnchorTuple_of_length (m := 2*k-1) as (by omega)
  have haF : a ∈ columnAnchorFibre A (2*k-1) 0 := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha.symm ▸ has,ha.symm ▸ hadd⟩
  obtain ⟨j,hj,hmodel⟩ := hcover a haF
  rw [ha] at hmodel
  by_cases hactive : ∃ y ∈ bohr Gamma u, f j y ≠ 0
  · exact Or.inr ⟨j,Finset.mem_filter.mpr ⟨hj,hactive⟩,hmodel⟩
  · left
    intro y hy hd
    have hz : f j y = 0 := by
      by_contra hne
      exact hactive ⟨y,bohr_mono_radius _ (min_le_right _ _) hy,hne⟩
    exact (hmodel y (bohr_mono_radius _ (min_le_left _ _) hy)
      (fun x hx => bohr_mono_radius _ (min_le_left _ _) (hd x hx))).trans hz

end LeanProofs.GowersSzemeredi
