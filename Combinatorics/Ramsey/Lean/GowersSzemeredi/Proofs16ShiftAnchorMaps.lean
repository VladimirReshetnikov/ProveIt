import GowersSzemeredi.Proofs16ShiftAnchorArrangement

/-! The selected local maps form one shift-indexed family. Good pair
containments give their Freiman domains; a good higher arrangement gives
an additive identity on the intersection of four selected domains. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def shiftAnchorQuadruple {N : Nat} (x y : ZMod N → ZMod N) (a : ZMod N) : Fin 4 → ZMod N :=
  ![x a+a,x a,y a+a,y a]

def shiftAnchorMap {N : Nat} [NeZero N]
    (T : ZMod N → Finset (ZMod N)) (L : ZMod N → ZMod N → ZMod N) (r : Real)
    (x y : ZMod N → ZMod N) (a : ZMod N) : ZMod N → ZMod N :=
  columnPairExtension T L r (shiftAnchorPair x a) (shiftAnchorPair y a)

theorem shiftAnchorMap_local {N d : Nat} [NeZero N]
    (s : PairSelectionState N) (C : Finset (Fin 4 → ZMod N))
    (T : ZMod N → Finset (ZMod N)) (L : ZMod N → ZMod N → ZMod N)
    (x y : ZMod N → ZMod N) (a : ZMod N) {r : Real} (hr : 0 ≤ r)
    (hL : ∀ t, IsFreimanLinearOn (bohr (T t) r) (L t)) (hzero : ∀ t, L t 0 = 0)
    (hcompat : ColumnPairCompatible T L r (shiftAnchorPair x a) (shiftAnchorPair y a))
    (hq : shiftAnchorQuadruple x y a ∈ C)
    (hgood : shiftAnchorQuadruple x y a ∉ jointQuadrupleFailures C T s d r) :
    IsFreimanLinearOn (bohr (shiftAnchorFrequencies s.frequencies x y a) (jointSelectionRadius d r))
      (shiftAnchorMap T L r x y a) ∧ shiftAnchorMap T L r x y a 0 = 0 ∧
      (∀ z ∈ bohr (columnDifferenceSpectrum T (shiftAnchorPair x a)) (r/4),
        shiftAnchorMap T L r x y a z = columnDifferenceMap L (shiftAnchorPair x a) z) ∧
      (∀ z ∈ bohr (columnDifferenceSpectrum T (shiftAnchorPair y a)) (r/4),
        shiftAnchorMap T L r x y a z = columnDifferenceMap L (shiftAnchorPair y a) z) :=
  joint_good_quadruple_extension s C T L (shiftAnchorQuadruple x y a) hr hL hzero hcompat hq hgood

theorem shiftAnchorMaps_coherent {N d : Nat} [NeZero N]
    (s : PairSelectionState N) (H : Finset (HigherArrangementParameter N))
    (T : ZMod N → Finset (ZMod N)) (L : ZMod N → ZMod N → ZMod N)
    (x y : ZMod N → ZMod N) (a : Fin 4 → ZMod N) {r : Real} (hr : 0 ≤ r)
    (ha : a 0+a 1 = a 2+a 3)
    (hL : ∀ t, IsFreimanLinearOn (bohr (T t) r) (L t)) (hzero : ∀ t, L t 0 = 0)
    (hcompat : ∀ j : Fin 4, ColumnPairCompatible T L r (shiftAnchorPair x (a j)) (shiftAnchorPair y (a j)))
    (hp : shiftAnchorArrangement x y a ∈ H)
    (hgood : shiftAnchorArrangement x y a ∉ jointHigherFailures H T s d r)
    (hleft : ∀ z ∈ bohr (Finset.univ.biUnion (fun j : Fin 4 => columnDifferenceSpectrum T (shiftAnchorPair x (a j)))) (r/4),
      ColumnDifferenceQuadruple L (fun j : Fin 4 => shiftAnchorPair x (a j)) z)
    (hright : ∀ z ∈ bohr (Finset.univ.biUnion (fun j : Fin 4 => columnDifferenceSpectrum T (shiftAnchorPair y (a j)))) (r/4),
      ColumnDifferenceQuadruple L (fun j : Fin 4 => shiftAnchorPair y (a j)) z) :
    ∀ z, (∀ j : Fin 4, z ∈ bohr (shiftAnchorFrequencies s.frequencies x y (a j)) (jointSelectionRadius d r)) →
      shiftAnchorMap T L r x y (a 0) z+shiftAnchorMap T L r x y (a 1) z =
        shiftAnchorMap T L r x y (a 2) z+shiftAnchorMap T L r x y (a 3) z := by
  have hcompat' : ∀ j : Fin 4, ColumnPairCompatible T L r
      (higherArrangementEndpointPair (shiftAnchorArrangement x y a) (Fin.castAdd 4 j))
      (higherArrangementEndpointPair (shiftAnchorArrangement x y a) (Fin.natAdd 4 j)) := by
    simpa only [shiftAnchorArrangement_left_pair x y a ha,shiftAnchorArrangement_right_pair x y a ha] using hcompat
  have hl : ∀ z ∈ bohr (higherLeftFrequencies T (higherArrangementEndpoints (shiftAnchorArrangement x y a))) (r/4),
      ColumnDifferenceQuadruple L (fun j : Fin 4 => higherArrangementEndpointPair (shiftAnchorArrangement x y a) (Fin.castAdd 4 j)) z := by
    simpa only [higherLeftFrequencies_eq_pair_union,shiftAnchorArrangement_left_pair x y a ha] using hleft
  have hg : ∀ z ∈ bohr (higherRightFrequencies T (higherArrangementEndpoints (shiftAnchorArrangement x y a))) (r/4),
      ColumnDifferenceQuadruple L (fun j : Fin 4 => higherArrangementEndpointPair (shiftAnchorArrangement x y a) (Fin.natAdd 4 j)) z := by
    simpa only [higherRightFrequencies_eq_pair_union,shiftAnchorArrangement_right_pair x y a ha] using hright
  have h := joint_good_higher_coherence s H T L (shiftAnchorArrangement x y a) hr hL hzero hcompat' hp hgood hl hg
  intro z hz
  have hz' : z ∈ bohr (higherSelectedPairFrequencies s.frequencies (shiftAnchorArrangement x y a)) (jointSelectionRadius d r) := by
    rw [shiftAnchorArrangement_selected_frequencies s.frequencies x y a ha]
    exact (mem_bohr_family_union _ _ _).mpr hz
  simpa only [higherAnchorExtension,shiftAnchorArrangement_left_pair x y a ha,
    shiftAnchorArrangement_right_pair x y a ha,shiftAnchorMap] using h z hz'

end LeanProofs.GowersSzemeredi
