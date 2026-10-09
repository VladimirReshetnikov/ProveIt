import GowersSzemeredi.Proofs16CoherentSparseDomain
import GowersSzemeredi.Proofs16ExplicitGraphCutoff

/-! A quasirandom Bohr graph whose selected local maps still carry many
coherent quadruples, with source witnesses and explicit uniform bounds. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def coherentGraphFrequencyBound (b ell : Nat) : Nat := b+4*ell*ell+2*ell

theorem exists_coherent_quasirandom_domain {N ell cells H : Nat}
    [NeZero N] [NeZero cells] [NeZero H] [Fact N.Prime]
    (Q : Finset (Fin 4 → ZMod N)) (X Gamma B : Finset (ZMod N))
    (theta : Fin ell → ZMod N → ZMod N) (F : ZMod N → ZMod N → ZMod N)
    {rho sigma kappa epsilon : Real} (hrho : 0 < rho) (hrhoMax : rho ≤ 1/(8*Real.pi))
    (hs : 0 < sigma) (hsMax : sigma < 1/4) (hk : 0 < kappa)
    (heps : 0 < epsilon) (hepsOne : epsilon ≤ 1) (hcells : 4 ≤ rho*cells)
    (hH : (2 : Real)^ell ≤ sigma*H) (d : Nat) (hG : Gamma.card ≤ d) (hB : B.card ≤ d)
    (htheta : ∀ i, FreimanHom 2 (bohr Gamma rho) (theta i) ∧ theta i 0 = 0)
    (hX : X ⊆ bohr Gamma (rho/4)) (hfamily : CoherentFrequencyFamily X B theta F sigma Q)
    (hmass : kappa*(N : Real)^3 ≤ Q.card)
    (hNanalytic : 1/relationProfileSmoothing epsilon H (coherentGraphFrequencyBound B.card ell) ≤ N)
    (hNregular : coherentRegularityModulusBound (epsilon/6)
      (relationProfileCutoff epsilon H (coherentGraphFrequencyBound B.card ell)) cells ell d rho kappa ≤ N) :
    let cutoff := relationProfileCutoff epsilon H (coherentGraphFrequencyBound B.card ell)
    let tau := sigma/(2 : Real)^ell
    ∃ (S B' V : Finset (ZMod N)) (R : Finset (Fin 4 → ZMod N))
      (source : ZMod N → ZMod N) (delta : Real),
      IsCoherentFrequencyRefinement Q X Gamma B theta F rho tau
        (coherentRegularityDensity (epsilon/6) cutoff cells ell d rho kappa)
        (coherentRegularityRank (epsilon/6) cutoff cells ell d) (B.card+4*ell*ell) (4^ell) S B' V R source ∧
      0 ≤ delta ∧ delta ≤ 1 ∧
      boxSum (fun (z : ↥(bohr B' tau)) (u : ↥(bohr S (rho/4))) =>
        (if (z : ZMod N) ∈ bohr (Finset.univ.image fun i => theta i u) (tau/4)
          then (1 : Real) else 0)-delta) ≤
      epsilon*((bohr B' tau).card : Real)^2*((bohr S (rho/4)).card : Real)^2 := by
  let m := coherentGraphFrequencyBound B.card ell
  let cutoff := relationProfileCutoff epsilon H m
  let tau := sigma/(2 : Real)^ell
  obtain ⟨S,B',V,R,source,hprops,hbad⟩ := exists_coherent_sparse_relation_domain Q X Gamma B theta F
    hrho hrhoMax hs.le hk (by positivity : 0 < epsilon/6) hcells cutoff d hG hB htheta hX
    hfamily hmass hNregular
  obtain ⟨hGS,hS,hBB',hB',hthetaS,hV,hVmass,hRmass,hoffset,hsource,hquad,hfamily'⟩ := hprops
  have htau : 0 < tau := by dsimp [tau]; positivity
  have htauLe : tau ≤ sigma := div_le_self hs.le (one_le_pow₀ (by norm_num))
  have htauH : 1 ≤ tau*(H : Real) := by
    dsimp only [tau]
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ (by positivity)).mpr (by simpa only [one_mul] using hH)
  have hfreq : Fintype.card ↥B'+2*Fintype.card (Fin ell) ≤ m := by
    simp only [Fintype.card_coe,Fintype.card_fin]
    dsimp only [m,coherentGraphFrequencyBound]
    omega
  have hC : bohr S (rho/4) ⊆ bohr S rho := bohr_mono_radius _ (by linarith)
  have hCne : (bohr S (rho/4)).Nonempty := ⟨0,zero_mem_bohr S (by positivity)⟩
  obtain ⟨delta,hd0,hd1,hbox⟩ := tuple_bohr_quasirandom_explicit (Q := H)
    (fun i : ↥B' => (i : ZMod N)) (bohr S rho) (bohr S (rho/4)) hC hCne theta
    (fun i => (hthetaS i).2) m htau.le (show 0 ≤ tau/4 by positivity)
    (htauLe.trans_lt hsMax) (show tau/4 < 1/4 by linarith) heps hepsOne hNanalytic htauH hfreq hbad.le
  have himage : Finset.univ.image (fun i : ↥B' => (i : ZMod N)) = B' := by ext z; simp
  rw [boxSum_finset_congr (congrArg (fun T => bohr T tau) himage)
    (fun z (u : ↥(bohr S (rho/4))) =>
      (if z ∈ bohr (Finset.univ.image fun i => theta i u) (tau/4) then (1 : Real) else 0)-delta)] at hbox
  rw [himage] at hbox
  exact ⟨S,B',V,R,source,delta,⟨hGS,hS,hBB',hB',hthetaS,hV,hVmass,hRmass,hoffset,hsource,hquad,hfamily'⟩,
    hd0,hd1,hbox⟩

end LeanProofs.GowersSzemeredi
