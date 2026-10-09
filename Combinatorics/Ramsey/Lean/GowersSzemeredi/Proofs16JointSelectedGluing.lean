import GowersSzemeredi.Proofs16HigherAnchorCoherence

/-! The actual complements of the selection failure sets supply the
containments used in local extension and higher coherence. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem joint_good_quadruple_extension {N d : Nat} [NeZero N]
    (s : PairSelectionState N) (C : Finset (Fin 4 → ZMod N))
    (T : ZMod N → Finset (ZMod N)) (L : ZMod N → ZMod N → ZMod N)
    (q : Fin 4 → ZMod N) {r : Real} (hr : 0 ≤ r)
    (hL : ∀ x, IsFreimanLinearOn (bohr (T x) r) (L x)) (hzero : ∀ x, L x 0 = 0)
    (hcompat : ColumnPairCompatible T L r (q 0,q 1) (q 2,q 3))
    (hq : q ∈ C) (hgood : q ∉ jointQuadrupleFailures C T s d r) :
    let f := columnPairExtension T L r (q 0,q 1) (q 2,q 3)
    IsFreimanLinearOn (bohr (pairSelectedQuadrupleFrequencies s.frequencies q) (jointSelectionRadius d r)) f ∧
      f 0 = 0 ∧
      (∀ y ∈ bohr (columnDifferenceSpectrum T (q 0,q 1)) (r/4), f y = columnDifferenceMap L (q 0,q 1) y) ∧
      (∀ y ∈ bohr (columnDifferenceSpectrum T (q 2,q 3)) (r/4), f y = columnDifferenceMap L (q 2,q 3) y) := by
  apply column_pair_selected_extension T L _ _ _ hr hL hzero hcompat
  by_contra h
  exact hgood (Finset.mem_filter.mpr ⟨hq,h⟩)

theorem joint_good_higher_coherence {N d : Nat} [NeZero N]
    (s : PairSelectionState N) (H : Finset (HigherArrangementParameter N))
    (T : ZMod N → Finset (ZMod N)) (L : ZMod N → ZMod N → ZMod N)
    (p : HigherArrangementParameter N) {r : Real} (hr : 0 ≤ r)
    (hL : ∀ x, IsFreimanLinearOn (bohr (T x) r) (L x)) (hzero : ∀ x, L x 0 = 0)
    (hcompat : ∀ j : Fin 4, ColumnPairCompatible T L r
      (higherArrangementEndpointPair p (Fin.castAdd 4 j)) (higherArrangementEndpointPair p (Fin.natAdd 4 j)))
    (hp : p ∈ H) (hgood : p ∉ jointHigherFailures H T s d r)
    (hleft : ∀ y ∈ bohr (higherLeftFrequencies T (higherArrangementEndpoints p)) (r/4),
      ColumnDifferenceQuadruple L (fun j : Fin 4 => higherArrangementEndpointPair p (Fin.castAdd 4 j)) y)
    (hright : ∀ y ∈ bohr (higherRightFrequencies T (higherArrangementEndpoints p)) (r/4),
      ColumnDifferenceQuadruple L (fun j : Fin 4 => higherArrangementEndpointPair p (Fin.natAdd 4 j)) y) :
    ∀ y ∈ bohr (higherSelectedPairFrequencies s.frequencies p) (jointSelectionRadius d r),
      higherAnchorExtension T L r p 0 y+higherAnchorExtension T L r p 1 y =
        higherAnchorExtension T L r p 2 y+higherAnchorExtension T L r p 3 y := by
  apply higher_anchor_extensions_coherent T s.frequencies L p hr hL hzero hcompat _ hleft hright
  by_contra h
  exact hgood (Finset.mem_filter.mpr ⟨hp,h⟩)

end LeanProofs.GowersSzemeredi
