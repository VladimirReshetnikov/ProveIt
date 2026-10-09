import GowersSzemeredi.Proofs16AffineRowBohrDomains

/-! Coherent anchor systems yield four systems on one proper progression
whose Bohr frequencies are Freiman maps. The constants are absorbed in a
fixed spectrum and every retained quadruple remains coherent. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def HasCoherentProgressionRows {N : Nat} [NeZero N]
    (H : Finset (HigherArrangementParameter N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (delta kappa : Real) (d : Nat) (r : Real) : Prop :=
    ∃ (s : PairSelectionState N) (J : Fin 4 → Finset (Fin s.maps.length))
      (x y : ZMod N → ZMod N) (P : OAI.Erdos3.BohrProgression.CyclicCenteredGAP N)
      (t : Fin 4 → ZMod N) (S : Finset (Fin 4 → ZMod N))
      (psi : Fin 4 → Fin s.maps.length → ZMod N → ZMod N)
      (c : Fin 4 → Fin s.maps.length → ZMod N),
      s.JointValid T delta d r ∧
      (s.maps.length : Real)*jointSelectionGain delta d r ≤ jointSelectionRank d r ∧
      (∀ j, (J j).card ≤ 2*jointSelectionRank d r) ∧
      P.rank ≤ rowCommonBohrRank delta (uniformAnchorIndexDensity delta kappa d r) d r+1 ∧ P.Proper ∧
      rowProgressionDensity delta (uniformAnchorIndexDensity delta kappa d r) d r*N ≤ (P.carrier.card : Real) ∧
      t 0+t 1 = t 2+t 3 ∧ S.Nonempty ∧
      rowProgressionQuadrupleDensity delta (uniformAnchorIndexDensity delta kappa d r) d r*(N : Real)^3 ≤ S.card ∧
      (affineRowConstants J c).card ≤ 8*jointSelectionRank d r ∧
      (∀ j, ∀ i ∈ J j, FreimanHom 2 P.carrier (psi j i) ∧ psi j i 0 = 0) ∧
      ∀ b ∈ S, b 0+b 1 = b 2+b 3 ∧ (∀ j, b j ∈ P.carrier) ∧
        Function.Injective (fun j => t j+b j) ∧
        shiftAnchorArrangement x y (fun j => t j+b j) ∈ H ∧
        (∀ j, IsFreimanLinearOn (affineRowBohrDomain J c psi (jointSelectionRadius d r) j (b j))
          (shiftAnchorMap T L r x y (t j+b j)) ∧ shiftAnchorMap T L r x y (t j+b j) 0 = 0) ∧
        (∀ z, (∀ j, z ∈ affineRowBohrDomain J c psi (jointSelectionRadius d r) j (b j)) →
          shiftAnchorMap T L r x y (t 0+b 0) z+shiftAnchorMap T L r x y (t 1+b 1) z =
            shiftAnchorMap T L r x y (t 2+b 2) z+shiftAnchorMap T L r x y (t 3+b 3) z) ∧
        (∀ j, ∀ i ∈ J j, (s.maps.get i).toFun (t j+b j) = c j i+psi j i (b j))

theorem HasCoherentAnchorSystemOn.progression_rows {N d : Nat} [NeZero N]
    {H : Finset (HigherArrangementParameter N)} {T : ZMod N → Finset (ZMod N)}
    {L : ZMod N → ZMod N → ZMod N} {delta kappa r : Real}
    (h : HasCoherentAnchorSystemOn H T L delta kappa d r) (hk : 0 < kappa) (hd : 0 < delta)
    (hT : ∀ x, (T x).card ≤ d) :
    HasCoherentProgressionRows H T L delta kappa d r := by
  obtain ⟨s,J,x,y,R,hs,hbudget,hJ,hR,hproperties⟩ := h.row_indices_uniform hk hd hT
  obtain ⟨P,t,S,psi,c,hPrank,hPproper,hPmass,ht,hSne,hS,hpsi,hrealize⟩ :=
    joint_rows_on_proper_progression s T J R hs hJ (uniformAnchorIndexDensity_pos hd hk d r) hR
      (fun a ha => (hproperties a ha).1) (fun a ha j => ((hproperties a ha).2.2.2.2.2 j).2)
  have hconst : (affineRowConstants J c).card ≤ 8*jointSelectionRank d r := by
    have h := affineRowConstants_card_le J c hJ
    omega
  refine ⟨s,J,x,y,P,t,S,psi,c,hs,hbudget,hJ,hPrank,hPproper,hPmass,ht,hSne,hS,hconst,hpsi,?_⟩
  intro b hb
  obtain ⟨hbadd,hbP,hbR,hbaffine⟩ := hrealize b hb
  obtain ⟨haadd,hainj,haH,halocal,hacoherent,hafreq⟩ := hproperties _ hbR
  have hsub (j : Fin 4) : affineRowBohrDomain J c psi (jointSelectionRadius d r) j (b j) ⊆
      bohr (commonIndexAnchorFrequencies s (J j) (t j+b j)) (jointSelectionRadius d r) :=
    affine_row_bohr_subset J c psi (fun i => (s.maps.get i).toFun) j (t j) (b j)
      (jointSelectionRadius d r) (hbaffine j)
  refine ⟨hbadd,hbP,hainj,haH,fun j => ⟨(halocal j).1.mono (hsub j),(halocal j).2⟩,?_,hbaffine⟩
  intro z hz
  exact hacoherent z (fun j => hsub j (hz j))

end LeanProofs.GowersSzemeredi
