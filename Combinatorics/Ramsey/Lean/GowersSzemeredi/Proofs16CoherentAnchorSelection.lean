import GowersSzemeredi.Proofs16DenseHigherAnchorSelection

/-! Dense good arrangements yield actual normalized local Freiman maps
with many coherent additive quadruples. All required compatibility and
containment properties are recorded in the good-arrangement predicate. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def GoodHigherAnchorArrangement {N : Nat} [NeZero N]
    (T : ZMod N → Finset (ZMod N)) (F : (ZMod N × ZMod N) → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (r sigma : Real) (p : HigherArrangementParameter N) : Prop :=
  let e := fun j : Fin 4 => higherArrangementEndpointPair p (Fin.castAdd 4 j)
  let u := fun j : Fin 4 => higherArrangementEndpointPair p (Fin.natAdd 4 j)
  (∀ j, ColumnPairCompatible T L r (e j) (u j)) ∧
  (∀ j, bohr (F (e j) ∪ F (u j)) sigma ⊆ bohrQuarterSum (columnDifferenceSpectrum T (e j)) (columnDifferenceSpectrum T (u j)) r) ∧
  (bohr (higherSelectedPairFrequencies F p) sigma ⊆ bohrQuarterSum
    (higherLeftFrequencies T (higherArrangementEndpoints p)) (higherRightFrequencies T (higherArrangementEndpoints p)) r) ∧
  (∀ z ∈ bohr (higherLeftFrequencies T (higherArrangementEndpoints p)) (r/4), ColumnDifferenceQuadruple L e z) ∧
  (∀ z ∈ bohr (higherRightFrequencies T (higherArrangementEndpoints p)) (r/4), ColumnDifferenceQuadruple L u z)

theorem shift_anchor_maps_of_good_arrangement {N : Nat} [NeZero N]
    (T : ZMod N → Finset (ZMod N)) (F : (ZMod N × ZMod N) → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (x y : ZMod N → ZMod N) (a : Fin 4 → ZMod N)
    {r sigma : Real} (hr : 0 ≤ r) (ha : a 0+a 1 = a 2+a 3)
    (hL : ∀ t, IsFreimanLinearOn (bohr (T t) r) (L t)) (hzero : ∀ t, L t 0 = 0)
    (hgood : GoodHigherAnchorArrangement T F L r sigma (shiftAnchorArrangement x y a)) :
    (∀ j : Fin 4, IsFreimanLinearOn (bohr (shiftAnchorFrequencies F x y (a j)) sigma)
      (shiftAnchorMap T L r x y (a j)) ∧ shiftAnchorMap T L r x y (a j) 0 = 0) ∧
    (∀ z, (∀ j : Fin 4, z ∈ bohr (shiftAnchorFrequencies F x y (a j)) sigma) →
      shiftAnchorMap T L r x y (a 0) z+shiftAnchorMap T L r x y (a 1) z =
        shiftAnchorMap T L r x y (a 2) z+shiftAnchorMap T L r x y (a 3) z) := by
  obtain ⟨hcompat,hpair,hcontain,hleft,hright⟩ := hgood
  constructor
  · intro j
    have h := column_pair_selected_extension T L _ _ _ hr hL hzero (hcompat j) (hpair j)
    have h' := And.intro h.1 h.2.1
    simpa only [shiftAnchorArrangement_left_pair x y a ha,shiftAnchorArrangement_right_pair x y a ha,
      shiftAnchorMap,shiftAnchorFrequencies] using h'
  · have h := higher_anchor_extensions_coherent T F L (shiftAnchorArrangement x y a) hr hL hzero
      hcompat hcontain hleft hright
    intro z hz
    have hz' : z ∈ bohr (higherSelectedPairFrequencies F (shiftAnchorArrangement x y a)) sigma := by
      rw [shiftAnchorArrangement_selected_frequencies F x y a ha]
      exact (mem_bohr_family_union _ _ _).mpr hz
    simpa only [higherAnchorExtension,shiftAnchorArrangement_left_pair x y a ha,
      shiftAnchorArrangement_right_pair x y a ha,shiftAnchorMap] using h z hz'

theorem exists_dense_coherent_anchor_maps {N : Nat} [NeZero N]
    (H : Finset (HigherArrangementParameter N))
    (T : ZMod N → Finset (ZMod N)) (F : (ZMod N × ZMod N) → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) {r sigma kappa : Real} (hr : 0 ≤ r)
    (hL : ∀ t, IsFreimanLinearOn (bohr (T t) r) (L t)) (hzero : ∀ t, L t 0 = 0)
    (hgood : ∀ p ∈ H, GoodHigherAnchorArrangement T F L r sigma p)
    (hmass : kappa*(N : Real)^11 ≤ H.card) (hN : 8 ≤ kappa*(N : Real)) :
    ∃ (x y : ZMod N → ZMod N) (Q : Finset (Fin 4 → ZMod N)),
      (kappa/2)*(N : Real)^3 ≤ Q.card ∧
      ∀ a ∈ Q, a 0+a 1 = a 2+a 3 ∧ Function.Injective a ∧
        (∀ j : Fin 4, IsFreimanLinearOn (bohr (shiftAnchorFrequencies F x y (a j)) sigma)
          (shiftAnchorMap T L r x y (a j)) ∧ shiftAnchorMap T L r x y (a j) 0 = 0) ∧
        (∀ z, (∀ j : Fin 4, z ∈ bohr (shiftAnchorFrequencies F x y (a j)) sigma) →
          shiftAnchorMap T L r x y (a 0) z+shiftAnchorMap T L r x y (a 1) z =
            shiftAnchorMap T L r x y (a 2) z+shiftAnchorMap T L r x y (a 3) z) := by
  obtain ⟨x,y,Q,hQ,hrealize⟩ := exists_dense_anchors_from_arrangements H hmass hN
  refine ⟨x,y,Q,hQ,?_⟩
  intro a ha
  obtain ⟨hadd,hinj,hmem⟩ := hrealize a ha
  exact ⟨hadd,hinj,shift_anchor_maps_of_good_arrangement T F L x y a hr hadd hL hzero (hgood _ hmem)⟩

end LeanProofs.GowersSzemeredi
