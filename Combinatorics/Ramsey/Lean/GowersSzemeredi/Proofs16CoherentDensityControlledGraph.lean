import GowersSzemeredi.Proofs16CoherentAdaptiveDenseGraph

/-! Coherent refinement with an explicit power-small box error measured
against the density actually retained, and a positive graph density. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem exists_coherent_density_controlled_graph {N ell cells H : Nat}
    [NeZero N] [NeZero cells] [NeZero H] [Fact N.Prime]
    (Q : Finset (Fin 4 → ZMod N)) (X Gamma B : Finset (ZMod N))
    (theta : Fin ell → ZMod N → ZMod N) (F : ZMod N → ZMod N → ZMod N)
    (power : Nat) {rho sigma kappa scale : Real}
    (hrho : 0 < rho) (hrhoMax : rho ≤ 1/(8*Real.pi))
    (hs : 0 < sigma) (hsMax : sigma < 1/4) (hk : 0 < kappa) (hscale : 0 < scale)
    (hcells : 4 ≤ rho*cells) (hH : (2 : Real)^ell ≤ sigma*H)
    (d : Nat) (hG : Gamma.card ≤ d) (hB : B.card ≤ d)
    (htheta : ∀ i, FreimanHom 2 (bohr Gamma rho) (theta i) ∧ theta i 0 = 0)
    (hX : X ⊆ bohr Gamma (rho/4)) (hfamily : CoherentFrequencyFamily X B theta F sigma Q)
    (hmass : kappa*(N : Real)^3 ≤ Q.card)
    (hN : coherentAdaptiveGraphModulusBound
      (coherentDensityAccuracy H (coherentGraphFrequencyBound B.card ell) power scale)
      H (coherentGraphFrequencyBound B.card ell) cells ell rho (d,kappa) ≤ N) :
    let m := coherentGraphFrequencyBound B.card ell
    let e := coherentDensityAccuracy H m power scale
    ∃ s : Nat, s ≤ ell-Module.finrank (ZMod N) (relationSubmodule (bohr Gamma rho) theta) ∧
    let final := (coherentAdaptiveGraphState e H m cells ell rho)^[s] (d,kappa)
    let tau := sigma/(2 : Real)^s
    ∃ (S B' V : Finset (ZMod N)) (R : Finset (Fin 4 → ZMod N))
      (source : ZMod N → ZMod N) (delta : Real),
      IsCoherentFrequencyRefinement Q X Gamma B theta F rho tau
        final.2 final.1 (B.card+4*s*ell) (4^s) S B' V R source ∧
      B'.card ≤ final.1 ∧ 0 < final.2 ∧
      (1/((4*H : Nat) : Real)^m)/2 ≤ delta ∧ delta ≤ 1 ∧
      boxSum (fun (z : ↥(bohr B' tau)) (u : ↥(bohr S (rho/4))) =>
        (if (z : ZMod N) ∈ bohr (Finset.univ.image fun i => theta i u) (tau/4)
          then (1 : Real) else 0)-delta) ≤
      (final.2^power/scale)^4*((bohr B' tau).card : Real)^2*((bohr S (rho/4)).card : Real)^2 := by
  let m := coherentGraphFrequencyBound B.card ell
  let e := coherentDensityAccuracy H m power scale
  obtain ⟨s,hsn,S,B',V,R,source,delta,hprops,hBstate,hfinal,hd,hd1,hbox⟩ :=
    exists_coherent_adaptive_dense_graph Q X Gamma B theta F e hrho hrhoMax hs hsMax hk
      (fun a ha => ⟨coherentDensityAccuracy_pos H m power hscale ha,
        coherentDensityAccuracy_le_half H m power scale a⟩)
      hcells hH d hG hB htheta hX hfamily hmass hN
  refine ⟨s,hsn,S,B',V,R,source,delta,hprops,hBstate,hfinal,hd,hd1,?_⟩
  exact hbox.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (coherentDensityAccuracy_fourth_le H m power hscale hfinal)
      (sq_nonneg _)) (sq_nonneg _))

end LeanProofs.GowersSzemeredi
