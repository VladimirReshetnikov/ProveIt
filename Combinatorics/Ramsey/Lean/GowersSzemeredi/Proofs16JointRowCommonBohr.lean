import GowersSzemeredi.Proofs16FourRowCommonFrequencyBohr

/-! The actual joint selection state yields a dense subfamily whose
frequency maps have compatible difference domains on one Bohr set.
All prior properties of retained quadruples survive by subset inclusion. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem joint_rows_common_bohr {N d : Nat} [NeZero N]
    (s : PairSelectionState N) (T : ZMod N → Finset (ZMod N))
    (J : Fin 4 → Finset (Fin s.maps.length)) (R : Finset (Fin 4 → ZMod N))
    {delta r kappa : Real} (hs : s.JointValid T delta d r)
    (hJ : ∀ j, (J j).card ≤ 2*jointSelectionRank d r) (hk : 0 < kappa)
    (hmass : kappa*(N : Real)^3 ≤ R.card)
    (hadd : ∀ a ∈ R, a 0+a 1 = a 2+a 3)
    (hdom : ∀ a ∈ R, ∀ j, ∀ i ∈ J j, a j ∈ (s.maps.get i).domain) :
    ∃ (R' : Finset (Fin 4 → ZMod N)) (Gamma : Finset (ZMod N))
      (psi : Fin 4 → Fin s.maps.length → ZMod N → ZMod N),
      R' ⊆ R ∧ rowEightDensity delta kappa d r*(N : Real)^3 ≤ R'.card ∧
      (Gamma.card : Real) ≤ 64*(rowEightDensity delta kappa d r)^(-(2 : Real)) ∧
      ∀ j, rowEightDensity delta kappa d r*N ≤ ((anchorRowSupport R' j).card : Real) ∧
        ∀ i ∈ J j, FreimanHom 2 (bohr Gamma (1/(8*Real.pi))) (psi j i) ∧ psi j i 0 = 0 ∧
          ∀ x ∈ anchorRowSupport R' j, ∀ y ∈ anchorRowSupport R' j,
            x-y ∈ bohr Gamma (1/(8*Real.pi)) →
              (s.maps.get i).toFun x-(s.maps.get i).toFun y = psi j i (x-y) := by
  obtain ⟨R',hsub,hR',hrows⟩ := joint_rows_eight_density s T J R hs hJ hk hmass hadd hdom
  obtain ⟨Gamma,psi,hG,hpsi⟩ := four_row_common_frequency_bohr (anchorRowSupport R') J
    (fun _j i => (s.maps.get i).toFun) (rowEightDensity_pos hk)
    (fun j => (hrows j).1) (fun j => (hrows j).2)
  exact ⟨R',Gamma,psi,hsub,hR',hG,fun j => ⟨(hrows j).1,hpsi j⟩⟩

end LeanProofs.GowersSzemeredi
