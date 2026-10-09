import GowersSzemeredi.Proofs16SelectedBohrGluing
import GowersSzemeredi.Proofs16ColumnDifferenceExtension

/-! Gluing needs local column linearity and the chosen pair's agreement.
No global bihomomorphism or agreement of all column quadruples is assumed. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def ColumnPairCompatible {N : Nat} [NeZero N]
    (T : ZMod N → Finset (ZMod N)) (L : ZMod N → ZMod N → ZMod N)
    (r : Real) (p q : ZMod N × ZMod N) : Prop :=
  ∀ y ∈ bohr (columnDifferenceSpectrum T p) r, y ∈ bohr (columnDifferenceSpectrum T q) r →
    columnDifferenceMap L p y = columnDifferenceMap L q y

def columnPairExtension {N : Nat} [NeZero N]
    (T : ZMod N → Finset (ZMod N)) (L : ZMod N → ZMod N → ZMod N)
    (r : Real) (p q : ZMod N × ZMod N) : ZMod N → ZMod N :=
  bohrSumExtension (columnDifferenceSpectrum T p) (columnDifferenceSpectrum T q)
    (columnDifferenceMap L p) (columnDifferenceMap L q) r

theorem columnDifferenceMap_freiman_of_local {N : Nat} [NeZero N]
    (T : ZMod N → Finset (ZMod N)) (L : ZMod N → ZMod N → ZMod N) (r : Real)
    (hL : ∀ x, IsFreimanLinearOn (bohr (T x) r) (L x)) (p : ZMod N × ZMod N) :
    IsFreimanLinearOn (bohr (columnDifferenceSpectrum T p) r) (columnDifferenceMap L p) := by
  have hm (y : ZMod N) (hy : y ∈ bohr (columnDifferenceSpectrum T p) r) :
      y ∈ bohr (T p.1) r ∧ y ∈ bohr (T p.2) r := by
    simpa only [columnDifferenceSpectrum,bohr_union,Finset.mem_inter] using hy
  intro a b c d ha hb hc hd he
  have h1 := hL p.1 a b c d (hm a ha).1 (hm b hb).1 (hm c hc).1 (hm d hd).1 he
  have h2 := hL p.2 a b c d (hm a ha).2 (hm b hb).2 (hm c hc).2 (hm d hd).2 he
  dsimp only [columnDifferenceMap]
  linear_combination h1-h2

theorem columnDifferenceMap_zero_of_local {N : Nat}
    (L : ZMod N → ZMod N → ZMod N) (hL : ∀ x, L x 0 = 0) (p : ZMod N × ZMod N) :
    columnDifferenceMap L p 0 = 0 := by
  simp only [columnDifferenceMap,hL,sub_self]

theorem column_pair_selected_extension {N : Nat} [NeZero N]
    (T : ZMod N → Finset (ZMod N)) (L : ZMod N → ZMod N → ZMod N)
    (D : Finset (ZMod N)) (p q : ZMod N × ZMod N) {r sigma : Real} (hr : 0 ≤ r)
    (hL : ∀ x, IsFreimanLinearOn (bohr (T x) r) (L x)) (hzero : ∀ x, L x 0 = 0)
    (hpq : ColumnPairCompatible T L r p q)
    (hD : bohr D sigma ⊆ bohrQuarterSum (columnDifferenceSpectrum T p) (columnDifferenceSpectrum T q) r) :
    IsFreimanLinearOn (bohr D sigma) (columnPairExtension T L r p q) ∧
      columnPairExtension T L r p q 0 = 0 ∧
      (∀ y ∈ bohr (columnDifferenceSpectrum T p) (r/4), columnPairExtension T L r p q y = columnDifferenceMap L p y) ∧
      (∀ y ∈ bohr (columnDifferenceSpectrum T q) (r/4), columnPairExtension T L r p q y = columnDifferenceMap L q y) :=
  selected_bohr_sum_extension _ _ D _ _ hr
    (columnDifferenceMap_freiman_of_local T L r hL p) (columnDifferenceMap_freiman_of_local T L r hL q)
    (columnDifferenceMap_zero_of_local L hzero p) (columnDifferenceMap_zero_of_local L hzero q) hpq hD

end LeanProofs.GowersSzemeredi
