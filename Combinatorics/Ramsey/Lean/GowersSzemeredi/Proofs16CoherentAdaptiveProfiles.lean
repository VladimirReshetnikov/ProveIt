import GowersSzemeredi.Proofs16DenseBohrGraphProfiles
import GowersSzemeredi.Proofs16CoherentAdaptiveGraphSchedule

/-! All admissible radius profiles on one coherent refinement, using the
same stopping state and original source witnesses throughout. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem exists_coherent_adaptive_profiles {N ell cells H : Nat}
    [NeZero N] [NeZero cells] [NeZero H] [Fact N.Prime]
    (Q : Finset (Fin 4 → ZMod N)) (X Gamma B : Finset (ZMod N))
    (theta : Fin ell → ZMod N → ZMod N) (F : ZMod N → ZMod N → ZMod N)
    (e : Nat × Real → Real) {rho sigma kappa : Real}
    (hrho : 0 < rho) (hrhoMax : rho ≤ 1/(8*Real.pi)) (hs : 0 ≤ sigma) (hk : 0 < kappa)
    (he : ∀ a, 0 < a.2 → 0 < e a ∧
      e a ≤ (1/(H : Real)^(coherentGraphFrequencyBound B.card ell))/2)
    (hcells : 4 ≤ rho*cells) (d : Nat) (hG : Gamma.card ≤ d) (hB : B.card ≤ d)
    (htheta : ∀ i, FreimanHom 2 (bohr Gamma rho) (theta i) ∧ theta i 0 = 0)
    (hX : X ⊆ bohr Gamma (rho/4)) (hfamily : CoherentFrequencyFamily X B theta F sigma Q)
    (hmass : kappa*(N : Real)^3 ≤ Q.card)
    (hN : coherentAdaptiveGraphModulusBound e H (coherentGraphFrequencyBound B.card ell)
      cells ell rho (d,kappa) ≤ N) :
    let m := coherentGraphFrequencyBound B.card ell
    ∃ s : Nat, s ≤ ell-Module.finrank (ZMod N) (relationSubmodule (bohr Gamma rho) theta) ∧
    let final := (coherentAdaptiveGraphState e H m cells ell rho)^[s] (d,kappa)
    ∃ (S B' V : Finset (ZMod N)) (R : Finset (Fin 4 → ZMod N)) (source : ZMod N → ZMod N),
      IsCoherentFrequencyRefinement Q X Gamma B theta F rho (sigma/(2 : Real)^s)
        final.2 final.1 (B.card+4*s*ell) (4^s) S B' V R source ∧
      B'.card ≤ final.1 ∧ 0 < final.2 ∧
      DenseBohrGraphProfiles B' (bohr S (rho/4)) theta H m (e final) := by
  let m := coherentGraphFrequencyBound B.card ell
  let epsilon := fun a => (e a)^4/6
  let cutoff := fun a => relationProfileCutoff ((e a)^4) H m
  let Phi := coherentAdaptiveGraphState e H m cells ell rho
  let n := ell-Module.finrank (ZMod N) (relationSubmodule (bohr Gamma rho) theta)
  have hNmass : ∀ j ≤ n, 8 ≤ (Phi^[j] (d,kappa)).2*(N : Real) := by
    intro j hj
    exact coherentAdaptiveGraphModulusBound_mass e H m cells ell hrho hk
      (hj.trans (Nat.sub_le _ _)) hN
  obtain ⟨s,hsn,S,B',V,R,source,hprops,hBstate,hbad⟩ :=
    coherent_adaptive_relation_iteration theta epsilon cutoff
      (fun a ha => div_pos (pow_pos (he a ha).1 _) (by norm_num)) hrho hrhoMax hcells
      n (d,kappa) Gamma B X F Q sigma hk hs hG hB (by dsimp only [n]; omega)
      htheta hX hfamily hmass hNmass
  let final := Phi^[s] (d,kappa)
  have hfinal : 0 < final.2 := coherentAdaptiveState_pos epsilon cutoff cells ell hrho hk s
  have hsk : s ≤ ell := hsn.trans (Nat.sub_le _ _)
  have hfreq : B'.card+2*ell ≤ m := by
    have hb := hprops.2.2.2.1
    have hmul := Nat.mul_le_mul_right ell (Nat.mul_le_mul_left 4 hsk)
    dsimp only [m,coherentGraphFrequencyBound]
    omega
  refine ⟨s,hsn,S,B',V,R,source,hprops,hBstate,hfinal,?_⟩
  exact denseBohrGraphProfiles_of_sparse_relations B' (bohr S rho) (bohr S (rho/4))
    (bohr_mono_radius _ (by linarith)) ⟨0,zero_mem_bohr S (by positivity)⟩ theta
    (fun i => (hprops.2.2.2.2.1 i).2) m hfreq (he final hfinal).1 (he final hfinal).2
    (coherentAdaptiveGraphModulusBound_analytic e H m cells ell rho (d,kappa) hsk hN) hbad.le

end LeanProofs.GowersSzemeredi
