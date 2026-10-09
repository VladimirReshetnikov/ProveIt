import GowersSzemeredi.Proofs16RowProgressionParameters

/-! The original frequency maps become affine on dense portions of
additive translates of one proper progression. The varying maps are
Freiman on the whole progression, and retained quadruples map back to
the original coherent family. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem joint_rows_on_proper_progression {N d : Nat} [NeZero N]
    (s : PairSelectionState N) (T : ZMod N → Finset (ZMod N))
    (J : Fin 4 → Finset (Fin s.maps.length)) (R : Finset (Fin 4 → ZMod N))
    {delta r kappa : Real} (hs : s.JointValid T delta d r)
    (hJ : ∀ j, (J j).card ≤ 2*jointSelectionRank d r) (hk : 0 < kappa)
    (hmass : kappa*(N : Real)^3 ≤ R.card)
    (hadd : ∀ a ∈ R, a 0+a 1 = a 2+a 3)
    (hdom : ∀ a ∈ R, ∀ j, ∀ i ∈ J j, a j ∈ (s.maps.get i).domain) :
    ∃ (P : OAI.Erdos3.BohrProgression.CyclicCenteredGAP N) (t : Fin 4 → ZMod N)
      (S : Finset (Fin 4 → ZMod N)) (psi : Fin 4 → Fin s.maps.length → ZMod N → ZMod N)
      (c : Fin 4 → Fin s.maps.length → ZMod N),
      P.rank ≤ rowCommonBohrRank delta kappa d r+1 ∧ P.Proper ∧
      rowProgressionDensity delta kappa d r*N ≤ (P.carrier.card : Real) ∧
      t 0+t 1 = t 2+t 3 ∧ S.Nonempty ∧
      rowProgressionQuadrupleDensity delta kappa d r*(N : Real)^3 ≤ S.card ∧
      (∀ j, ∀ i ∈ J j, FreimanHom 2 P.carrier (psi j i) ∧ psi j i 0 = 0) ∧
      ∀ b ∈ S, b 0+b 1 = b 2+b 3 ∧ (∀ j, b j ∈ P.carrier) ∧
        (fun j => t j+b j) ∈ R ∧
        ∀ j, ∀ i ∈ J j, (s.maps.get i).toFun (t j+b j) = c j i+psi j i (b j) := by
  obtain ⟨R',Gamma,psi,hR'R,hR',hG,hrows⟩ := joint_rows_common_bohr s T J R hs hJ hk hmass hadd hdom
  have hG' : Gamma.card ≤ rowCommonBohrRank delta kappa d r :=
    (Nat.cast_le (α := Real)).mp (hG.trans (Nat.le_ceil _))
  have hrho : (0 : Real) < 1/(8*Real.pi) := by positivity
  obtain ⟨P,t,S,hPrank,hPproper,hPsub,hPmass,ht,hSne,hS,hrealize⟩ :=
    additive_quadruples_on_proper_progression R' Gamma hrho (rowEightDensity_pos hk) hG'
      (fun a ha => hadd a (hR'R ha)) hR'
  obtain ⟨c,hc⟩ := frequency_rows_affine_on_progression R' S Gamma P t J
    (fun _j i => (s.maps.get i).toFun) psi hrho.le hPsub hSne
    (fun b hb => (hrealize b hb).2.1) (fun b hb => (hrealize b hb).2.2)
    (fun j => (hrows j).2)
  refine ⟨P,t,S,psi,c,hPrank,hPproper,hPmass,ht,hSne,hS,?_,?_⟩
  · intro j i hi
    have hp := (hrows j).2 i hi
    have hsub : P.carrier ⊆ bohr Gamma (1/(8*Real.pi)) :=
      hPsub.trans (bohr_mono_radius _ (by linarith : (1/(8*Real.pi))/4 ≤ 1/(8*Real.pi)))
    exact ⟨IsAddFreimanHom.subset hsub hp.1 (Set.mapsTo_univ _ _),hp.2.1⟩
  · intro b hb
    obtain ⟨hadd,hP,hmem⟩ := hrealize b hb
    exact ⟨hadd,hP,hR'R hmem,fun j i hi => hc j i hi (b j) (Finset.mem_image.mpr ⟨b,hb,rfl⟩)⟩

end LeanProofs.GowersSzemeredi
