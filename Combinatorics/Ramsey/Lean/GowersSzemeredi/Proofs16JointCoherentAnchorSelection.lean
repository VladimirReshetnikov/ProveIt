import GowersSzemeredi.Proofs16JointGoodArrangements

/-! Simultaneous frequency selection, sparse original column failures,
and a dense supported arrangement family produce actual coherent global
anchors. The surviving arrangements retain membership in the input family. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem exists_joint_coherent_anchor_maps {N d : Nat} [NeZero N] [Fact N.Prime]
    (H : Finset (HigherArrangementParameter N)) (C : Finset (Fin 4 → ZMod N))
    (V : Finset (Fin 8 → ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) {r kappa eps eta delta : Real}
    (hr : 0 < r) (hr4 : r < 4) (hd : 0 < delta)
    (hT : ∀ x, (T x).card ≤ d)
    (hL : ∀ t, IsFreimanLinearOn (bohr (T t) r) (L t)) (hzero : ∀ t, L t 0 = 0)
    (hadd : ∀ q ∈ C, q 0-q 1 = q 2-q 3)
    (hC : ∀ p ∈ H, ∀ j, higherArrangementAnchorQuadruple p j ∈ C)
    (hV : ∀ p ∈ H, higherArrangementLeftColumns p ∈ V ∧ higherArrangementRightColumns p ∈ V)
    (hH : kappa*(N : Real)^11 ≤ H.card)
    (hcompat : ((incompatibleAnchorQuadruples C T L r).card : Real) ≤ eps*(N : Real)^3)
    (hrel : ((columnTupleFailures V T L r).card : Real) ≤ eta*(N : Real)^7)
    (hN : 8 ≤ (kappa-4*eps-2*eta-5*delta)*(N : Real)) :
    ∃ s : PairSelectionState N, s.JointValid T delta d r ∧
      (s.maps.length : Real)*jointSelectionGain delta d r ≤ jointSelectionRank d r ∧
      ∃ (x y : ZMod N → ZMod N) (Q : Finset (Fin 4 → ZMod N)),
        ((kappa-4*eps-2*eta-5*delta)/2)*(N : Real)^3 ≤ Q.card ∧
        ∀ a ∈ Q, a 0+a 1 = a 2+a 3 ∧ Function.Injective a ∧
          shiftAnchorArrangement x y a ∈ H ∧
          (∀ j : Fin 4, IsFreimanLinearOn
            (bohr (shiftAnchorFrequencies s.frequencies x y (a j)) (jointSelectionRadius d r))
            (shiftAnchorMap T L r x y (a j)) ∧ shiftAnchorMap T L r x y (a j) 0 = 0) ∧
          (∀ z, (∀ j : Fin 4, z ∈ bohr (shiftAnchorFrequencies s.frequencies x y (a j))
              (jointSelectionRadius d r)) →
            shiftAnchorMap T L r x y (a 0) z+shiftAnchorMap T L r x y (a 1) z =
              shiftAnchorMap T L r x y (a 2) z+shiftAnchorMap T L r x y (a 3) z) := by
  obtain ⟨s,hs,hquad,hhigher,hbudget⟩ := exists_joint_frequency_selection C H T hd hr hr4 hT hadd
  let G := jointGoodHigherArrangements H C V T L s d r
  have hG : (kappa-4*eps-2*eta-5*delta)*(N : Real)^11 ≤ G.card :=
    jointGoodHigherArrangements_mass H C V T L s hH hcompat hrel hquad.le hhigher.le
  obtain ⟨x,y,Q,hQ,hrealize⟩ := exists_dense_anchors_from_arrangements G hG hN
  refine ⟨s,hs,hbudget,x,y,Q,hQ,?_⟩
  intro a ha
  obtain ⟨hadd,hinj,hmem⟩ := hrealize a ha
  have hgood := jointGoodHigherArrangements_good H C V T L s r hC hV hmem
  have hmemH : shiftAnchorArrangement x y a ∈ H :=
    ((mem_higherArrangementAvoidingBadData H _ _ _ _ _).mp hmem).1
  exact ⟨hadd,hinj,hmemH,shift_anchor_maps_of_good_arrangement T s.frequencies L x y a hr.le
    hadd hL hzero hgood⟩

end LeanProofs.GowersSzemeredi
