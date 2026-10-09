import GowersSzemeredi.Proofs16CoherentBridgeSystem

/-! Construct a coherent family with a finite weak-transitivity system.
Its accuracy is chosen for the density retained at the exact final state. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem exists_coherent_bridge_system {N ell cells : Nat}
    [NeZero N] [NeZero cells] [Fact N.Prime]
    (Q : Finset (Fin 4 → ZMod N)) (X Gamma B : Finset (ZMod N))
    (theta : Fin ell → ZMod N → ZMod N) (F : ZMod N → ZMod N → ZMod N)
    (power depth : Nat) {rho sigma kappa scale : Real}
    (hrho : 0 < rho) (hrhoMax : rho ≤ 1/(8*Real.pi))
    (hs : 0 < sigma) (hsMax : sigma < 1/4) (hk : 0 < kappa) (hscale : 0 < scale)
    (hcells : 4 ≤ rho*cells) (d : Nat) (hG : Gamma.card ≤ d) (hB : B.card ≤ d)
    (htheta : ∀ i, FreimanHom 2 (bohr Gamma rho) (theta i) ∧ theta i 0 = 0)
    (hX : X ⊆ bohr Gamma (rho/4)) (hfamily : CoherentFrequencyFamily X B theta F sigma Q)
    (hmass : kappa*(N : Real)^3 ≤ Q.card)
    (hN : let H := coherentRadiusProfileCells sigma ell depth
      let m := coherentGraphFrequencyBound B.card ell
      let k := 4*(B.card+4*ell*ell+ell)
      let e := fun a : Nat × Real => coherentBridgeAccuracy H m k (a.2^power/scale)
      coherentAdaptiveGraphModulusBound e H m cells ell rho (d,kappa) ≤ N) :
    let H := coherentRadiusProfileCells sigma ell depth
    let m := coherentGraphFrequencyBound B.card ell
    let k := 4*(B.card+4*ell*ell+ell)
    let e := fun a : Nat × Real => coherentBridgeAccuracy H m k (a.2^power/scale)
    ∃ s : Nat, s ≤ ell ∧
    let final := (coherentAdaptiveGraphState e H m cells ell rho)^[s] (d,kappa)
    let tau := sigma/(2 : Real)^s
    ∃ (S B' V : Finset (ZMod N)) (R : Finset (Fin 4 → ZMod N)) (source : ZMod N → ZMod N),
      IsCoherentFrequencyRefinement Q X Gamma B theta F rho tau
        final.2 final.1 (B.card+4*s*ell) (4^s) S B' V R source ∧
      B'.card ≤ final.1 ∧ 0 < final.2 ∧
      DenseBohrGraphProfiles B' (bohr S (rho/4)) theta H m (e final) ∧
      CoherentBridgeSystem B' V theta (fun u => F (source u)) tau (final.2^power/scale) depth := by
  let H := coherentRadiusProfileCells sigma ell depth
  letI : NeZero H := ⟨ne_of_gt (coherentRadiusProfileCells_pos hs ell depth)⟩
  let m := coherentGraphFrequencyBound B.card ell
  let k := 4*(B.card+4*ell*ell+ell)
  let e := fun a : Nat × Real => coherentBridgeAccuracy H m k (a.2^power/scale)
  have he (a : Nat × Real) (ha : 0 < a.2) : 0 < e a ∧ e a ≤ (1/(H : Real)^m)/2 :=
    ⟨coherentBridgeAccuracy_pos H m k (by positivity),coherentBridgeAccuracy_le_half H m k _⟩
  obtain ⟨s,hsn,S,B',V,R,source,hprops,hBstate,hfinal,hprofile⟩ :=
    exists_coherent_adaptive_profiles Q X Gamma B theta F e hrho hrhoMax hs.le hk he
      hcells d hG hB htheta hX hfamily hmass hN
  let final := (coherentAdaptiveGraphState e H m cells ell rho)^[s] (d,kappa)
  let tau := sigma/(2 : Real)^s
  have hsk : s ≤ ell := hsn.trans (Nat.sub_le _ _)
  have heta : 0 < final.2^power/scale := by positivity
  have htau : 0 < tau := by dsimp [tau]; positivity
  have htauLe : tau ≤ sigma := div_le_self hs.le (one_le_pow₀ (by norm_num))
  have hcard : 4*(B'.card+ell) ≤ k := by
    have hb := hprops.2.2.2.1
    have hmul := Nat.mul_le_mul_right ell (Nat.mul_le_mul_left 4 hsk)
    dsimp only [k]
    omega
  have hbase : (1 : Real) ≤ (2*H : Nat) := by exact_mod_cast (show 1 ≤ 2*H by have := NeZero.pos H; omega)
  have hsmall : 4*((2*H : Nat) : Real)^(4*(B'.card+ell))*e final < (1/(H : Real)^m)*(final.2^power/scale) :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hbase hcard)
      (by norm_num)) (he final hfinal).1.le).trans_lt (coherentBridgeAccuracy_small H m k heta)
  refine ⟨s,hsk,S,B',V,R,source,hprops,hBstate,hfinal,hprofile,?_⟩
  apply hprofile.bridge_system htau (htauLe.trans_lt hsMax) (he final hfinal).1.le heta
    (fun i hi => coherentRadiusProfileCells_spec hs hsk hi) hprops.2.2.2.2.2.1
    (fun j => ((hprops.2.2.2.2.1 j).1.isFreimanLinearOn (by decide)).mono
      (bohr_mono_radius _ (by linarith : rho/4 ≤ rho)))
    hprops.2.2.2.2.2.2.2.2.2.2.2.1 hsmall

end LeanProofs.GowersSzemeredi
