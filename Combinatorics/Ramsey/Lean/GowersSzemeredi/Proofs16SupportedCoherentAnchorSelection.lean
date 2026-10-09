import GowersSzemeredi.Proofs16SupportedArrangementFamilies

/-! A dense column set with sparse incompatible quadruples and sparse
unrespected eight-column tuples yields a quantitatively dense system of
coherent global anchors. The arrangement mass is proved from the column
density, rather than supplied as a separate assumption. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem exists_supported_coherent_anchor_maps {N d : Nat} [NeZero N] [Fact N.Prime]
    (W : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) {r alpha eps eta delta : Real}
    (hr : 0 < r) (hr4 : r < 4) (hd : 0 < delta)
    (hT : ∀ x, (T x).card ≤ d)
    (hL : ∀ t, IsFreimanLinearOn (bohr (T t) r) (L t)) (hzero : ∀ t, L t 0 = 0)
    (ha : 0 ≤ alpha) (hW : alpha*(N : Real) ≤ W.card)
    (hcompat : ((incompatibleAnchorQuadruples (supportedAnchorQuadruples W) T L r).card : Real) ≤ eps*(N : Real)^3)
    (hrel : ((columnTupleFailures (supportedColumnTuples W) T L r).card : Real) ≤ eta*(N : Real)^7)
    (hN : 8 ≤ (alpha^16-4*eps-2*eta-5*delta)*(N : Real)) :
    ∃ s : PairSelectionState N, s.JointValid T delta d r ∧
      (s.maps.length : Real)*jointSelectionGain delta d r ≤ jointSelectionRank d r ∧
      ∃ (x y : ZMod N → ZMod N) (Q : Finset (Fin 4 → ZMod N)),
        ((alpha^16-4*eps-2*eta-5*delta)/2)*(N : Real)^3 ≤ Q.card ∧
        ∀ a ∈ Q, a 0+a 1 = a 2+a 3 ∧ Function.Injective a ∧
          shiftAnchorArrangement x y a ∈ supportedHigherArrangements W ∧
          (∀ j : Fin 4, IsFreimanLinearOn
            (bohr (shiftAnchorFrequencies s.frequencies x y (a j)) (jointSelectionRadius d r))
            (shiftAnchorMap T L r x y (a j)) ∧ shiftAnchorMap T L r x y (a j) 0 = 0) ∧
          (∀ z, (∀ j : Fin 4, z ∈ bohr (shiftAnchorFrequencies s.frequencies x y (a j))
              (jointSelectionRadius d r)) →
            shiftAnchorMap T L r x y (a 0) z+shiftAnchorMap T L r x y (a 1) z =
              shiftAnchorMap T L r x y (a 2) z+shiftAnchorMap T L r x y (a 3) z) := by
  apply exists_joint_coherent_anchor_maps (supportedHigherArrangements W)
    (supportedAnchorQuadruples W) (supportedColumnTuples W) T L hr hr4 hd hT hL hzero
    (fun q hq => (Finset.mem_filter.mp hq).2)
    (fun p hp j => supported_higher_anchor_quadruple_mem W hp j)
    (fun p hp => supported_higher_column_tuples_mem W hp)
    (supported_higher_arrangements_dense W ha hW) hcompat hrel hN

end LeanProofs.GowersSzemeredi
