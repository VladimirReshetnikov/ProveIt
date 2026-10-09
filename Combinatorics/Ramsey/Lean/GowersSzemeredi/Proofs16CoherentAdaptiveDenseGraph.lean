import GowersSzemeredi.Proofs16CoherentAdaptiveGraphSchedule
import GowersSzemeredi.Proofs16TupleDensityLower

/-! A positive-density quasirandom graph and a coherent family on the same
refined domain, with error chosen at its exact retained density. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem exists_coherent_adaptive_dense_graph {N ell cells H : Nat}
    [NeZero N] [NeZero cells] [NeZero H] [Fact N.Prime]
    (Q : Finset (Fin 4 → ZMod N)) (X Gamma B : Finset (ZMod N))
    (theta : Fin ell → ZMod N → ZMod N) (F : ZMod N → ZMod N → ZMod N)
    (e : Nat × Real → Real) {rho sigma kappa : Real}
    (hrho : 0 < rho) (hrhoMax : rho ≤ 1/(8*Real.pi))
    (hs : 0 < sigma) (hsMax : sigma < 1/4) (hk : 0 < kappa)
    (he : ∀ a, 0 < a.2 → 0 < e a ∧
      e a ≤ (1/((4*H : Nat) : Real)^(coherentGraphFrequencyBound B.card ell))/2)
    (hcells : 4 ≤ rho*cells) (hH : (2 : Real)^ell ≤ sigma*H)
    (d : Nat) (hG : Gamma.card ≤ d) (hB : B.card ≤ d)
    (htheta : ∀ i, FreimanHom 2 (bohr Gamma rho) (theta i) ∧ theta i 0 = 0)
    (hX : X ⊆ bohr Gamma (rho/4)) (hfamily : CoherentFrequencyFamily X B theta F sigma Q)
    (hmass : kappa*(N : Real)^3 ≤ Q.card)
    (hN : coherentAdaptiveGraphModulusBound e H (coherentGraphFrequencyBound B.card ell)
      cells ell rho (d,kappa) ≤ N) :
    let m := coherentGraphFrequencyBound B.card ell
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
      (e final)^4*((bohr B' tau).card : Real)^2*((bohr S (rho/4)).card : Real)^2 := by
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
      n (d,kappa) Gamma B X F Q sigma hk hs.le hG hB (by dsimp only [n]; omega)
      htheta hX hfamily hmass hNmass
  let final := Phi^[s] (d,kappa)
  let tau := sigma/(2 : Real)^s
  have hfinal : 0 < final.2 := coherentAdaptiveState_pos epsilon cutoff cells ell hrho hk s
  have hsk : s ≤ ell := hsn.trans (Nat.sub_le _ _)
  obtain ⟨hGS,hS,hBB',hB',hthetaS,hV,hVmass,hRmass,hoffset,hsource,hquad,hfamily'⟩ := hprops
  have htau : 0 < tau := by dsimp [tau]; positivity
  have htauLe : tau ≤ sigma := div_le_self hs.le (one_le_pow₀ (by norm_num))
  have htauH : 1 ≤ tau*(H : Real) := by
    have hp : (2 : Real)^s ≤ (2 : Real)^ell := pow_le_pow_right₀ (by norm_num) hsk
    dsimp only [tau]
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ (by positivity)).mpr (by simpa only [one_mul] using hp.trans hH)
  have hfreq : Fintype.card ↥B'+2*Fintype.card (Fin ell) ≤ m := by
    simp only [Fintype.card_coe,Fintype.card_fin]
    have hmul := Nat.mul_le_mul_right ell (Nat.mul_le_mul_left 4 hsk)
    dsimp only [m,coherentGraphFrequencyBound]
    omega
  have hC : bohr S (rho/4) ⊆ bohr S rho := bohr_mono_radius _ (by linarith)
  have hCne : (bohr S (rho/4)).Nonempty := ⟨0,zero_mem_bohr S (by positivity)⟩
  have hHone : (1 : Real) ≤ H := by exact_mod_cast NeZero.pos H
  have hbetaOne : 1/((4*H : Nat) : Real)^m ≤ 1 := by
    have hbase : (1 : Real) ≤ (4*H : Nat) := by push_cast; linarith
    exact (div_le_one (by positivity)).mpr (one_le_pow₀ hbase)
  have heOne : e final ≤ 1 := by have h := (he final hfinal).2; change e final ≤ (1/((4*H : Nat) : Real)^m)/2 at h; linarith
  have he4 : (e final)^4 ≤ 1 := by simpa using pow_le_pow_left₀ (he final hfinal).1.le heOne 4
  have hNanalytic := coherentAdaptiveGraphModulusBound_analytic e H m cells ell rho (d,kappa) hsk hN
  obtain ⟨delta,hd0,hd1,hbox⟩ := tuple_bohr_quasirandom_explicit (Q := H)
    (fun i : ↥B' => (i : ZMod N)) (bohr S rho) (bohr S (rho/4)) hC hCne theta
    (fun i => (hthetaS i).2) m htau.le (show 0 ≤ tau/4 by positivity)
    (htauLe.trans_lt hsMax) (show tau/4 < 1/4 by linarith)
    (pow_pos (he final hfinal).1 _) he4 hNanalytic htauH hfreq hbad.le
  have himage : Finset.univ.image (fun i : ↥B' => (i : ZMod N)) = B' := by ext z; simp
  rw [boxSum_finset_congr (congrArg (fun T => bohr T tau) himage)
    (fun z (u : ↥(bohr S (rho/4))) =>
      (if z ∈ bohr (Finset.univ.image fun i => theta i u) (tau/4) then (1 : Real) else 0)-delta)] at hbox
  rw [himage] at hbox
  have hcell : 1 ≤ tau/4*((4*H : Nat) : Real) := by push_cast; nlinarith only [htauH]
  have hd := tuple_bohr_density_lower (Q := 4*H) B' (bohr S (rho/4)) hCne theta m htau.le
    (show tau/4 ≤ tau by linarith) hcell (by simp only [Fintype.card_coe,Fintype.card_fin] at hfreq ⊢; omega)
    (he final hfinal).1.le hbox
  refine ⟨s,hsn,S,B',V,R,source,delta,
    ⟨hGS,hS,hBB',hB',hthetaS,hV,hVmass,hRmass,hoffset,hsource,hquad,hfamily'⟩,
    hBstate,hfinal,?_,hd1,hbox⟩
  have h := (he final hfinal).2
  change e final ≤ (1/((4*H : Nat) : Real)^m)/2 at h
  linarith

end LeanProofs.GowersSzemeredi
