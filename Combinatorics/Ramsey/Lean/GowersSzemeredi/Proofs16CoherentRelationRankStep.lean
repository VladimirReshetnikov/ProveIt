import GowersSzemeredi.Proofs16CoherentBohrRefinement
import GowersSzemeredi.Proofs16RelationRankBudget

/-! A failed bounded-relation estimate admits a strict relation-rank
increase which preserves a dense family of coherent quadruples. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem coherent_relation_rank_step {N ell cells : Nat} [NeZero N] [NeZero cells] [Fact N.Prime]
    (Q : Finset (Fin 4 → ZMod N)) (X Gamma B : Finset (ZMod N))
    (theta : Fin ell → ZMod N → ZMod N) (F : ZMod N → ZMod N → ZMod N)
    {rho sigma kappa epsilon : Real} (hrho : 0 < rho) (hrhoMax : rho ≤ 1/(8*Real.pi))
    (hk : 0 < kappa) (heps : 0 < epsilon) (hcells : 4 ≤ rho*cells) (cutoff : Nat)
    (htheta : ∀ i, FreimanHom 2 (bohr Gamma rho) (theta i) ∧ theta i 0 = 0)
    (hX : X ⊆ bohr Gamma (rho/4))
    (hlocal : ∀ x ∈ X, IsFreimanLinearOn (freimanFrequencyBohr B theta sigma x) (F x) ∧ F x 0 = 0)
    (hquad : ∀ a ∈ Q, a 0+a 1 = a 2+a 3 ∧ (∀ j, a j ∈ X) ∧
      ∀ z, (∀ j, z ∈ freimanFrequencyBohr B theta sigma (a j)) →
        F (a 0) z+F (a 1) z = F (a 2) z+F (a 3) z)
    (hmass : kappa*(N : Real)^3 ≤ Q.card)
    (hbad : epsilon*((bohr Gamma (rho/4)).card : Real)^2 ≤
      (boundedBadRelationPairs (fun i : ↥B => (i : ZMod N)) (bohr Gamma rho)
        theta (bohr Gamma (rho/4)) cutoff).card)
    (hN : 8 ≤ (kappa*(quarterBohrDensity
      (relationRankStep epsilon ((2*cutoff+1)^(B.card+2*ell) : Nat) cells Gamma.card) rho)^4)*(N : Real)) :
    let D := relationRankStep epsilon ((2*cutoff+1)^(B.card+2*ell) : Nat) cells Gamma.card
    ∃ Gamma' : Finset (ZMod N), Gamma ⊆ Gamma' ∧ Gamma'.card ≤ D ∧
      relationSubmodule (bohr Gamma rho) theta < relationSubmodule (bohr Gamma' rho) theta ∧
      (∀ i, FreimanHom 2 (bohr Gamma' rho) (theta i) ∧ theta i 0 = 0) ∧
      HasCoherentTranslationRefinement Q X (bohr Gamma' (rho/4)) Gamma B theta F rho sigma
        (kappa*(quarterBohrDensity D rho)^4/512) := by
  obtain ⟨Gamma',hGG,hG',hfull,hquarter,hstrict⟩ := bounded_bad_pair_refinement_rank
    (fun i : ↥B => (i : ZMod N)) Gamma hrho hrhoMax hcells theta
    (fun i => (htheta i).1.isFreimanLinearOn (by decide)) cutoff heps hbad
  simp only [Fintype.card_coe,Fintype.card_fin] at hG'
  obtain ⟨t,color,V,R,ht,htmem,hV,hVmass,hRmass,hB',htheta',hlocal',hquad'⟩ :=
    coherent_bohr_refinement Q X Gamma Gamma' B theta F hrho hk htheta hX hGG hG'
      hlocal hquad hmass hN
  exact ⟨Gamma',hGG,hG',hstrict,htheta',t,color,V,R,ht,htmem,hV,hVmass,hRmass,hlocal',hquad'⟩

end LeanProofs.GowersSzemeredi
