import GowersSzemeredi.Proofs16AdditiveQuadrupleProjection

/-! Preserve coherent anchors with one exact index set per position.
The original selected Bohr domains and all map-domain memberships remain
valid, with the same uniform quadruple-density bound. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem HasCoherentAnchorSystemOn.row_indices_uniform {N d : Nat} [NeZero N]
    {H : Finset (HigherArrangementParameter N)} {T : ZMod N → Finset (ZMod N)}
    {L : ZMod N → ZMod N → ZMod N} {delta kappa r : Real}
    (h : HasCoherentAnchorSystemOn H T L delta kappa d r) (hk : 0 < kappa) (hd : 0 < delta)
    (hT : ∀ x, (T x).card ≤ d) :
    ∃ (s : PairSelectionState N) (J : Fin 4 → Finset (Fin s.maps.length))
      (x y : ZMod N → ZMod N) (R : Finset (Fin 4 → ZMod N)),
      s.JointValid T delta d r ∧
      (s.maps.length : Real)*jointSelectionGain delta d r ≤ jointSelectionRank d r ∧
      (∀ j, (J j).card ≤ 2*jointSelectionRank d r) ∧
      uniformAnchorIndexDensity delta kappa d r*(N : Real)^3 ≤ R.card ∧
      ∀ a ∈ R, a 0+a 1 = a 2+a 3 ∧ Function.Injective a ∧
        shiftAnchorArrangement x y a ∈ H ∧
        (∀ j : Fin 4, IsFreimanLinearOn
          (bohr (commonIndexAnchorFrequencies s (J j) (a j)) (jointSelectionRadius d r))
          (shiftAnchorMap T L r x y (a j)) ∧ shiftAnchorMap T L r x y (a j) 0 = 0) ∧
        (∀ z, (∀ j : Fin 4, z ∈ bohr (commonIndexAnchorFrequencies s (J j) (a j))
            (jointSelectionRadius d r)) →
          shiftAnchorMap T L r x y (a 0) z+shiftAnchorMap T L r x y (a 1) z =
            shiftAnchorMap T L r x y (a 2) z+shiftAnchorMap T L r x y (a 3) z) ∧
        (∀ j, commonIndexAnchorFrequencies s (J j) (a j) = shiftAnchorFrequencies s.frequencies x y (a j) ∧
          ∀ i ∈ J j, a j ∈ (s.maps.get i).domain) := by
  obtain ⟨s,hs,hbudget,x,y,Q,hQmass,hcoherent⟩ := h
  have hn : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hQ : Q.Nonempty := by
    apply Finset.card_pos.mp
    have hp : (0 : Real) < Q.card := (by positivity : 0 < kappa*(N : Real)^3).trans_le hQmass
    exact_mod_cast hp
  obtain ⟨J,R,hJ,hRQ,hcount,hR,hfreq⟩ := joint_anchor_row_indices s T hT hs x y Q hQ
  have hcountR : (Q.card : Real) ≤ ((s.maps.length+1 : Nat) : Real)^(8*jointSelectionRank d r)*(R.card : Real) := by
    exact_mod_cast hcount
  have hpos : 0 < ((s.maps.length+1 : Nat) : Real)^(8*jointSelectionRank d r) := by positivity
  have hmass : (kappa/((s.maps.length+1 : Nat) : Real)^(8*jointSelectionRank d r))*(N : Real)^3 ≤ R.card := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hpos).mpr
    simpa only [mul_comm] using hQmass.trans hcountR
  have huniform : uniformAnchorIndexDensity delta kappa d r*(N : Real)^3 ≤ R.card :=
    (mul_le_mul_of_nonneg_right (uniformAnchorIndexDensity_le hd hk.le hbudget)
      (show 0 ≤ (N : Real)^3 by positivity)).trans hmass
  refine ⟨s,J,x,y,R,hs,hbudget,hJ,huniform,?_⟩
  intro a ha
  obtain ⟨hadd,hinj,hmem,hlocal,hrelation⟩ := hcoherent a (hRQ ha)
  have he (j : Fin 4) : commonIndexAnchorFrequencies s (J j) (a j) =
      shiftAnchorFrequencies s.frequencies x y (a j) := (hfreq a ha j).1
  refine ⟨hadd,hinj,hmem,?_,?_,hfreq a ha⟩
  · intro j
    simpa only [he j] using hlocal j
  · intro z hz
    exact hrelation z (fun j => (he j) ▸ hz j)

end LeanProofs.GowersSzemeredi
