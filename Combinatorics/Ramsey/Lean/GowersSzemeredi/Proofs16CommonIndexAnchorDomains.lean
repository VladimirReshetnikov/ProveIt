import GowersSzemeredi.Proofs16JointAnchorCommonIndices

/-! Restrict the coherent anchor maps to Bohr sets defined by one fixed
small list of frequency-map indices. Quadruple density is retained with
loss `(m+1)^(8*rank)`. Common progression domains of all selected maps
remain a separate requirement for later structural steps. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def commonIndexAnchorFrequencies {N : Nat} [NeZero N] (s : PairSelectionState N)
    (J : Finset (Fin s.maps.length)) (a : ZMod N) : Finset (ZMod N) :=
  J.image (fun i => (s.maps.get i).toFun a)

theorem HasCoherentAnchorSystemOn.common_indices {N d : Nat} [NeZero N]
    {H : Finset (HigherArrangementParameter N)} {T : ZMod N → Finset (ZMod N)}
    {L : ZMod N → ZMod N → ZMod N} {delta kappa r : Real}
    (h : HasCoherentAnchorSystemOn H T L delta kappa d r) (hk : 0 < kappa)
    (hT : ∀ x, (T x).card ≤ d) :
    ∃ (s : PairSelectionState N) (J : Finset (Fin s.maps.length))
      (x y : ZMod N → ZMod N) (R : Finset (Fin 4 → ZMod N)),
      s.JointValid T delta d r ∧
      (s.maps.length : Real)*jointSelectionGain delta d r ≤ jointSelectionRank d r ∧
      J.card ≤ 8*jointSelectionRank d r ∧
      (kappa/((s.maps.length+1 : Nat) : Real)^(8*jointSelectionRank d r))*(N : Real)^3 ≤ R.card ∧
      ∀ a ∈ R, a 0+a 1 = a 2+a 3 ∧ Function.Injective a ∧
        shiftAnchorArrangement x y a ∈ H ∧
        (∀ j : Fin 4, IsFreimanLinearOn
          (bohr (commonIndexAnchorFrequencies s J (a j)) (jointSelectionRadius d r))
          (shiftAnchorMap T L r x y (a j)) ∧ shiftAnchorMap T L r x y (a j) 0 = 0) ∧
        (∀ z, (∀ j : Fin 4, z ∈ bohr (commonIndexAnchorFrequencies s J (a j))
            (jointSelectionRadius d r)) →
          shiftAnchorMap T L r x y (a 0) z+shiftAnchorMap T L r x y (a 1) z =
            shiftAnchorMap T L r x y (a 2) z+shiftAnchorMap T L r x y (a 3) z) := by
  obtain ⟨s,hs,hbudget,x,y,Q,hQmass,hcoherent⟩ := h
  have hn : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hQ : Q.Nonempty := by
    apply Finset.card_pos.mp
    have hp : (0 : Real) < Q.card := (by positivity : 0 < kappa*(N : Real)^3).trans_le hQmass
    exact_mod_cast hp
  obtain ⟨I,J,R,hI,hJ,hRQ,hcount,hR,hfreq⟩ := joint_anchor_common_indices s T hT hs x y Q hQ
  have hcountR : (Q.card : Real) ≤ ((s.maps.length+1 : Nat) : Real)^(8*jointSelectionRank d r)*(R.card : Real) := by
    exact_mod_cast hcount
  have hpos : 0 < ((s.maps.length+1 : Nat) : Real)^(8*jointSelectionRank d r) := by positivity
  have hmass : (kappa/((s.maps.length+1 : Nat) : Real)^(8*jointSelectionRank d r))*(N : Real)^3 ≤ R.card := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hpos).mpr
    simpa only [mul_comm] using hQmass.trans hcountR
  refine ⟨s,J,x,y,R,hs,hbudget,hJ,hmass,?_⟩
  intro a ha
  obtain ⟨hadd,hinj,hmem,hlocal,hrelation⟩ := hcoherent a (hRQ ha)
  have hdom (j : Fin 4) : bohr (commonIndexAnchorFrequencies s J (a j)) (jointSelectionRadius d r) ⊆
      bohr (shiftAnchorFrequencies s.frequencies x y (a j)) (jointSelectionRadius d r) := by
    intro z hz
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    intro t ht
    exact (Finset.mem_filter.mp hz).2 t (((hfreq a ha).2 j).2 ht)
  refine ⟨hadd,hinj,hmem,fun j => ⟨(hlocal j).1.mono (hdom j),(hlocal j).2⟩,?_⟩
  intro z hz
  exact hrelation z (fun j => hdom j (hz j))

theorem HasCoherentAnchorSystem.common_indices {N d : Nat} [NeZero N]
    {P : Finset (ZMod N)} {T : ZMod N → Finset (ZMod N)}
    {L : ZMod N → ZMod N → ZMod N} {delta kappa r : Real}
    (h : HasCoherentAnchorSystem P T L delta kappa d r) (hk : 0 < kappa)
    (hT : ∀ x, (T x).card ≤ d) :
    ∃ (s : PairSelectionState N) (J : Finset (Fin s.maps.length))
      (x y : ZMod N → ZMod N) (R : Finset (Fin 4 → ZMod N)),
      s.JointValid T delta d r ∧
      (s.maps.length : Real)*jointSelectionGain delta d r ≤ jointSelectionRank d r ∧
      J.card ≤ 8*jointSelectionRank d r ∧
      (kappa/((s.maps.length+1 : Nat) : Real)^(8*jointSelectionRank d r))*(N : Real)^3 ≤ R.card ∧
      ∀ a ∈ R, a 0+a 1 = a 2+a 3 ∧ Function.Injective a ∧
        shiftAnchorArrangement x y a ∈ supportedHigherArrangements P ∧
        (∀ j : Fin 4, IsFreimanLinearOn
          (bohr (commonIndexAnchorFrequencies s J (a j)) (jointSelectionRadius d r))
          (shiftAnchorMap T L r x y (a j)) ∧ shiftAnchorMap T L r x y (a j) 0 = 0) ∧
        (∀ z, (∀ j : Fin 4, z ∈ bohr (commonIndexAnchorFrequencies s J (a j))
            (jointSelectionRadius d r)) →
          shiftAnchorMap T L r x y (a 0) z+shiftAnchorMap T L r x y (a 1) z =
            shiftAnchorMap T L r x y (a 2) z+shiftAnchorMap T L r x y (a 3) z) := by
  exact HasCoherentAnchorSystemOn.common_indices h hk hT

end LeanProofs.GowersSzemeredi
