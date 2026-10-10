import GowersSzemeredi.Proofs16GlobalFullyExactTransfer
import GowersSzemeredi.Proofs16ColumnTupleRelations

/-! Connect the paired exact transfer to the existing respected-eight-tuple
interface. Swapping the last two endpoint pairs changes the sum of four
differences into an additive quadruple, without changing any frequencies. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def balancedColumnPairs {N : Nat} (e : PairedColumnTuple N) : PairedColumnTuple N :=
  ![e 0,e 1,((e 2).2,(e 2).1),((e 3).2,(e 3).1)]

theorem balanced_column_pairs_index {N : Nat} (e : PairedColumnTuple N) :
    pairedColumnIndex (balancedColumnPairs e) =
      ((e 0).1-(e 0).2)+((e 1).1-(e 1).2)-
        (((e 2).1-(e 2).2)+((e 3).1-(e 3).2)) := by
  rw [pairedColumnIndex, Fin.sum_univ_four]
  change ((e 0).1-(e 0).2)+((e 1).1-(e 1).2)+
    ((e 2).2-(e 2).1)+((e 3).2-(e 3).1) = _
  ring

theorem balanced_column_pairs_spectrum {N : Nat}
    (T : ZMod N → Finset (ZMod N)) (e : PairedColumnTuple N) :
    pairedColumnSpectrum T (balancedColumnPairs e) = pairedColumnSpectrum T e := by
  ext r
  simp only [pairedColumnSpectrum, Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    fin_cases i <;> simpa [balancedColumnPairs, Finset.mem_union, or_comm] using hi
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    fin_cases i <;> simpa [balancedColumnPairs, Finset.mem_union, or_comm] using hi

theorem balanced_column_pairs_defect {N : Nat}
    (L : ZMod N → ZMod N → ZMod N) (e : PairedColumnTuple N) (y : ZMod N) :
    pairedColumnDefect L (balancedColumnPairs e) y =
      columnDifferenceMap L (e 0) y+columnDifferenceMap L (e 1) y-
        (columnDifferenceMap L (e 2) y+columnDifferenceMap L (e 3) y) := by
  rw [pairedColumnDefect, Fin.sum_univ_four]
  change (L (e 0).1 y-L (e 0).2 y)+(L (e 1).1 y-L (e 1).2 y)+
    (L (e 2).2 y-L (e 2).1 y)+(L (e 3).2 y-L (e 3).1 y) = _
  dsimp only [columnDifferenceMap]
  ring

/-- Exact balanced sums respect the difference-map additive quadruple on
its full natural eight-endpoint domain. -/
theorem column_difference_quadruple_of_paired_exact {N : Nat} [NeZero N]
    (S : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (rho : Real)
    (h8 : ∀ q : PairedColumnTuple N, (∀ i, (q i).1 ∈ S ∧ (q i).2 ∈ S) →
      pairedColumnIndex q = 0 → ∀ y ∈ bohr (pairedColumnSpectrum T q) rho,
        pairedColumnDefect L q y = 0)
    (e : PairedColumnTuple N) (he : ∀ i, (e i).1 ∈ S ∧ (e i).2 ∈ S)
    (hadd : IsAdditiveQuadruple (fun i => (e i).1-(e i).2)) :
    ∀ y ∈ bohr (pairedColumnSpectrum T e) rho, ColumnDifferenceQuadruple L e y := by
  have hb : ∀ i, ((balancedColumnPairs e) i).1 ∈ S ∧ ((balancedColumnPairs e) i).2 ∈ S := by
    intro i
    fin_cases i <;> simpa [balancedColumnPairs, and_comm] using he _
  have hi : pairedColumnIndex (balancedColumnPairs e) = 0 := by
    rw [balanced_column_pairs_index]
    exact sub_eq_zero.mpr hadd
  intro y hy
  have hz := h8 (balancedColumnPairs e) hb hi y (by rwa [balanced_column_pairs_spectrum])
  rw [balanced_column_pairs_defect] at hz
  exact sub_eq_zero.mp hz

/-- The same exact tuple data supplies the native respected-tuple predicate,
including its documented quarter-radius convention. -/
theorem column_tuple_respected_of_paired_exact {N : Nat} [NeZero N]
    (S : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) {rho : Real} (hr : 0 ≤ rho)
    (h8 : ∀ q : PairedColumnTuple N, (∀ i, (q i).1 ∈ S ∧ (q i).2 ∈ S) →
      pairedColumnIndex q = 0 → ∀ y ∈ bohr (pairedColumnSpectrum T q) rho,
        pairedColumnDefect L q y = 0)
    (v : Fin 8 → ZMod N) (hv : ∀ i, v i ∈ S)
    (hadd : IsAdditiveQuadruple (fun i =>
      (columnTuplePairs v i).1-(columnTuplePairs v i).2)) : ColumnTupleRespected T L rho v := by
  intro y hy
  change y ∈ bohr (pairedColumnSpectrum T (columnTuplePairs v)) (rho/4) at hy
  exact column_difference_quadruple_of_paired_exact S T L rho h8 (columnTuplePairs v)
    (fun i => ⟨hv _,hv _⟩) hadd y (bohr_mono_radius _ (by linarith) hy)

end LeanProofs.GowersSzemeredi
