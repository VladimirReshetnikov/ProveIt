import GowersSzemeredi.Proofs16CommonIndexAnchorDomains

/-! The common-index density loss can be bounded independently of the
modulus using the proved joint map-count budget. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

def uniformAnchorIndexDensity (delta kappa : Real) (d : Nat) (r : Real) : Real :=
  kappa/((jointSelectionRank d r : Real)/jointSelectionGain delta d r+1)^(8*jointSelectionRank d r)

theorem uniformAnchorIndexDensity_pos {delta kappa : Real} (hd : 0 < delta) (hk : 0 < kappa)
    (d : Nat) (r : Real) : 0 < uniformAnchorIndexDensity delta kappa d r := by
  have hg := jointSelectionGain_pos hd d r
  unfold uniformAnchorIndexDensity
  positivity

theorem uniformAnchorIndexDensity_le {delta kappa r : Real} {d m : Nat}
    (hd : 0 < delta) (hk : 0 ≤ kappa)
    (hbudget : (m : Real)*jointSelectionGain delta d r ≤ jointSelectionRank d r) :
    uniformAnchorIndexDensity delta kappa d r ≤
      kappa/((m+1 : Nat) : Real)^(8*jointSelectionRank d r) := by
  have hg := jointSelectionGain_pos hd d r
  have hm : (m : Real) ≤ (jointSelectionRank d r : Real)/jointSelectionGain delta d r :=
    (le_div_iff₀ hg).mpr hbudget
  have hb : ((m+1 : Nat) : Real) ≤ (jointSelectionRank d r : Real)/jointSelectionGain delta d r+1 := by
    simpa only [Nat.cast_add,Nat.cast_one,add_comm] using add_le_add_right hm 1
  have hp := pow_le_pow_left₀ (show 0 ≤ ((m+1 : Nat) : Real) by positivity) hb (8*jointSelectionRank d r)
  exact div_le_div_of_nonneg_left hk (by positivity) hp

theorem HasCoherentAnchorSystem.common_indices_uniform {N d : Nat} [NeZero N]
    {P : Finset (ZMod N)} {T : ZMod N → Finset (ZMod N)}
    {L : ZMod N → ZMod N → ZMod N} {delta kappa r : Real}
    (h : HasCoherentAnchorSystem P T L delta kappa d r) (hk : 0 < kappa) (hd : 0 < delta)
    (hT : ∀ x, (T x).card ≤ d) :
    ∃ (s : PairSelectionState N) (J : Finset (Fin s.maps.length))
      (x y : ZMod N → ZMod N) (R : Finset (Fin 4 → ZMod N)),
      s.JointValid T delta d r ∧
      (s.maps.length : Real)*jointSelectionGain delta d r ≤ jointSelectionRank d r ∧
      J.card ≤ 8*jointSelectionRank d r ∧
      uniformAnchorIndexDensity delta kappa d r*(N : Real)^3 ≤ R.card ∧
      ∀ a ∈ R, a 0+a 1 = a 2+a 3 ∧ Function.Injective a ∧
        shiftAnchorArrangement x y a ∈ supportedHigherArrangements P ∧
        (∀ j : Fin 4, IsFreimanLinearOn
          (bohr (commonIndexAnchorFrequencies s J (a j)) (jointSelectionRadius d r))
          (shiftAnchorMap T L r x y (a j)) ∧ shiftAnchorMap T L r x y (a j) 0 = 0) ∧
        (∀ z, (∀ j : Fin 4, z ∈ bohr (commonIndexAnchorFrequencies s J (a j))
            (jointSelectionRadius d r)) →
          shiftAnchorMap T L r x y (a 0) z+shiftAnchorMap T L r x y (a 1) z =
            shiftAnchorMap T L r x y (a 2) z+shiftAnchorMap T L r x y (a 3) z) := by
  obtain ⟨s,J,x,y,R,hs,hbudget,hJ,hmass,hproperties⟩ := h.common_indices hk hT
  refine ⟨s,J,x,y,R,hs,hbudget,hJ,?_,hproperties⟩
  exact (mul_le_mul_of_nonneg_right (uniformAnchorIndexDensity_le hd hk.le hbudget)
    (show 0 ≤ (N : Real)^3 by positivity)).trans hmass

end LeanProofs.GowersSzemeredi
