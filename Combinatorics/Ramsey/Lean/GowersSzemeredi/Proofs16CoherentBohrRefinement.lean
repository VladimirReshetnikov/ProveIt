import GowersSzemeredi.Proofs16CoherentTranslationLocalization

/-! An explicit refinement to an enlarged frequency-domain spectrum.
The varying family is unchanged, so its relation-rank potential can be
used in a terminating regularity iteration. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def quarterBohrDensity (d : Nat) (rho : Real) : Real :=
  1/(refinementCells (rho/4) : Real)^d

theorem quarterBohrDensity_pos (d : Nat) {rho : Real} (hrho : 0 < rho) :
    0 < quarterBohrDensity d rho := by
  have hc : 0 < refinementCells (rho/4) := Nat.ceil_pos.mpr (by positivity)
  have hcR : (0 : Real) < refinementCells (rho/4) := by exact_mod_cast hc
  unfold quarterBohrDensity
  positivity

theorem quarterBohrDensity_card_le {N d : Nat} [NeZero N]
    (Gamma : Finset (ZMod N)) {rho : Real} (hrho : 0 < rho) (hG : Gamma.card ≤ d) :
    quarterBohrDensity d rho*N ≤ ((bohr Gamma (rho/4)).card : Real) := by
  let M := refinementCells (rho/4)
  have hM : 0 < M := Nat.ceil_pos.mpr (by positivity)
  letI : NeZero M := ⟨ne_of_gt hM⟩
  have hc : 1 ≤ (rho/4)*(M : Real) := by
    have h : 1/(rho/4) ≤ (M : Real) := Nat.le_ceil _
    simpa only [mul_comm] using (div_le_iff₀ (by positivity : 0 < rho/4)).mp h
  have h := bohr_card_lower Gamma M hc
  have hp : M^Gamma.card ≤ M^d := Nat.pow_le_pow_right hM hG
  have hN : (N : Real) ≤ (M : Real)^d*(bohr Gamma (rho/4)).card := by
    exact_mod_cast h.trans (Nat.mul_le_mul_right _ hp)
  have hMR : (0 : Real) < M := by exact_mod_cast hM
  change (1/(M : Real)^d)*(N : Real) ≤ _
  rw [one_div_mul_eq_div]
  exact (div_le_iff₀ (pow_pos hMR d)).mpr (by simpa only [mul_comm] using hN)

theorem coherent_bohr_refinement {N ell d : Nat} [NeZero N]
    (Q : Finset (Fin 4 → ZMod N)) (X Gamma Gamma' B : Finset (ZMod N))
    (theta : Fin ell → ZMod N → ZMod N) (F : ZMod N → ZMod N → ZMod N)
    {rho sigma kappa : Real} (hrho : 0 < rho) (hk : 0 < kappa)
    (htheta : ∀ i, FreimanHom 2 (bohr Gamma rho) (theta i) ∧ theta i 0 = 0)
    (hX : X ⊆ bohr Gamma (rho/4)) (hGG : Gamma ⊆ Gamma') (hG' : Gamma'.card ≤ d)
    (hlocal : ∀ x ∈ X, IsFreimanLinearOn (freimanFrequencyBohr B theta sigma x) (F x) ∧ F x 0 = 0)
    (hquad : ∀ a ∈ Q, a 0+a 1 = a 2+a 3 ∧ (∀ j, a j ∈ X) ∧
      ∀ z, (∀ j, z ∈ freimanFrequencyBohr B theta sigma (a j)) →
        F (a 0) z+F (a 1) z = F (a 2) z+F (a 3) z)
    (hmass : kappa*(N : Real)^3 ≤ Q.card)
    (hN : 8 ≤ (kappa*(quarterBohrDensity d rho)^4)*(N : Real)) :
    ∃ (t : Fin 4 → ZMod N) (color : ZMod N → Fin 4) (V : Finset (ZMod N))
      (R : Finset (Fin 4 → ZMod N)),
      t 0+t 1 = t 2+t 3 ∧ (∀ j, t j ∈ bohr Gamma (rho/2)) ∧
      V ⊆ bohr Gamma' (rho/4) ∧
      (kappa*(quarterBohrDensity d rho)^4/512)*N ≤ (V.card : Real) ∧
      (kappa*(quarterBohrDensity d rho)^4/512)*(N : Real)^3 ≤ R.card ∧
      (translatedFrequencyBase B theta t).card ≤ B.card+4*ell ∧
      (∀ i, FreimanHom 2 (bohr Gamma' rho) (theta i) ∧ theta i 0 = 0) ∧
      (∀ u ∈ V, t (color u)+u ∈ X ∧
        IsFreimanLinearOn (freimanFrequencyBohr (translatedFrequencyBase B theta t) theta (sigma/2) u)
          (F (t (color u)+u)) ∧ F (t (color u)+u) 0 = 0) ∧
      ∀ b ∈ R, b 0+b 1 = b 2+b 3 ∧ Function.Injective b ∧
        (∀ j, b j ∈ V ∧ color (b j) = j) ∧ (fun j => t j+b j) ∈ Q ∧
        ∀ z, (∀ j, z ∈ freimanFrequencyBohr (translatedFrequencyBase B theta t) theta (sigma/2) (b j)) →
          F (t (color (b 0))+b 0) z+F (t (color (b 1))+b 1) z =
            F (t (color (b 2))+b 2) z+F (t (color (b 3))+b 3) z := by
  have hsub (s : Real) : bohr Gamma' s ⊆ bohr Gamma s := by
    intro z hz
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun v hv => (Finset.mem_filter.mp hz).2 v (hGG hv)⟩
  obtain ⟨t,color,V,R,ht,htmem,hV,hVmass,hRmass,hlocal',hquad'⟩ :=
    coherent_translation_localization Q X (bohr Gamma' (rho/4)) Gamma B theta F hrho.le hk
      (quarterBohrDensity_pos d hrho) htheta hX (hsub _) hlocal hquad hmass
      (quarterBohrDensity_card_le Gamma' hrho hG') hN
  refine ⟨t,color,V,R,ht,htmem,hV,hVmass,hRmass,translatedFrequencyBase_card_le B theta t,
    ?_,hlocal',hquad'⟩
  intro i
  exact ⟨IsAddFreimanHom.subset (hsub rho) (htheta i).1 (Set.mapsTo_univ _ _),(htheta i).2⟩

end LeanProofs.GowersSzemeredi
