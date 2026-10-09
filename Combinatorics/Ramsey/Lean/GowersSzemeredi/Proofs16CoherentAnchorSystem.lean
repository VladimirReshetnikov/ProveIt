import GowersSzemeredi.Proofs16EvenCoreColumnTuples

/-! A concrete coherent anchor system retains the selected state, its
map budget, the global anchors, and every realized supported arrangement. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def HasCoherentAnchorSystem {N : Nat} [NeZero N]
    (P : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (delta kappa : Real) (d : Nat) (r : Real) : Prop :=
  ∃ s : PairSelectionState N, s.JointValid T delta d r ∧
    (s.maps.length : Real)*jointSelectionGain delta d r ≤ jointSelectionRank d r ∧
    ∃ (x y : ZMod N → ZMod N) (Q : Finset (Fin 4 → ZMod N)),
      kappa*(N : Real)^3 ≤ Q.card ∧
      ∀ a ∈ Q, a 0+a 1 = a 2+a 3 ∧ Function.Injective a ∧
        shiftAnchorArrangement x y a ∈ supportedHigherArrangements P ∧
        (∀ j : Fin 4, IsFreimanLinearOn
          (bohr (shiftAnchorFrequencies s.frequencies x y (a j)) (jointSelectionRadius d r))
          (shiftAnchorMap T L r x y (a j)) ∧ shiftAnchorMap T L r x y (a j) 0 = 0) ∧
        (∀ z, (∀ j : Fin 4, z ∈ bohr (shiftAnchorFrequencies s.frequencies x y (a j))
            (jointSelectionRadius d r)) →
          shiftAnchorMap T L r x y (a 0) z+shiftAnchorMap T L r x y (a 1) z =
            shiftAnchorMap T L r x y (a 2) z+shiftAnchorMap T L r x y (a 3) z)

theorem coherent_anchor_system_of_even_core {N g d : Nat} [NeZero N] [Fact N.Prime]
    (P Gamma : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) {r rho beta : Real}
    (hr : 0 < r) (hr4 : r < 4) (hrrho : r ≤ rho) (hb : 0 < beta)
    (hP : beta*(N : Real) ≤ P.card) (hG : Gamma.card ≤ g)
    (hT : ∀ x ∈ P, (T x).card ≤ d)
    (hL : ∀ x ∈ P, IsFreimanLinearOn (bohr (T x) rho) (L x)) (hzero : ∀ x ∈ P, L x 0 = 0)
    (hrel : EvenColumnCoreRelations P Gamma T L r 4)
    (hN : 16 ≤ beta^16*(N : Real)) :
    HasCoherentAnchorSystem P (coreColumnSpectrum P Gamma T) (coreColumnMap P L)
      (beta^16/10) (beta^16/4) (g+d) r := by
  have hcompat : ((incompatibleAnchorQuadruples (supportedAnchorQuadruples P)
      (coreColumnSpectrum P Gamma T) (coreColumnMap P L) r).card : Real) ≤ 0*(N : Real)^3 := by
    rw [even_core_incompatible_anchor_quadruples_empty P Gamma T L hrel]
    simp
  have htuples : ((columnTupleFailures (supportedColumnTuples P)
      (coreColumnSpectrum P Gamma T) (coreColumnMap P L) r).card : Real) ≤ 0*(N : Real)^7 := by
    rw [even_core_column_tuple_failures_empty P Gamma T L hr.le hrel]
    simp
  have hsize : 8 ≤ (beta^16-4*0-2*0-5*(beta^16/10))*(N : Real) := by
    nlinarith only [hN]
  have h := exists_supported_coherent_anchor_maps P (coreColumnSpectrum P Gamma T) (coreColumnMap P L)
    hr hr4 (show 0 < beta^16/10 by positivity) (coreColumnSpectrum_card_le P Gamma T hG hT)
    (coreColumnMap_freiman P Gamma T L hrrho hL) (coreColumnMap_zero P L hzero)
    hb.le hP hcompat htuples hsize
  have he : (beta^16-4*0-2*0-5*(beta^16/10))/2 = beta^16/4 := by ring
  simpa only [HasCoherentAnchorSystem,he] using h

end LeanProofs.GowersSzemeredi
