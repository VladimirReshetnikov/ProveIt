import DiophantineConsistency.NativeAdaptiveRankWindow

set_option autoImplicit false
set_option Elab.async false

namespace DiophantineConsistency.NativeAdaptiveRankWindowChecks

open NativeAdaptiveRankWindow NativeAdaptiveMainBootstrap NativeAdaptiveCarrierBootstrap

private theorem base17 : 1<(17 : ℕ) := by decide

-- A generic box example with unrestricted J; not a complete adaptive zero.
example : 3*(16 : ℤ)<target 16 1 1 1 0 0 ∧
    target 16 1 1 1 0 0≤16^4-16^3-16-1 := by
  norm_num [target]

-- Signed divisibility is sufficient, without a supplied natural quotient.
example : (16 : ℤ) ∣ 2*(2 : ℤ)-3-1 := by
  exact first_index_residue_of_dvd (by decide : 0<(8 : ℕ))
    (by norm_num : (16 : ℤ) ∣ 2*(8 : ℤ))
    (by norm_num [Pell.yn_succ] : (68 : ℤ)=2*(Pell.yn base17 2 : ℤ))
    (by norm_num : (16 : ℤ) ∣ 68-3-1)

example : (3 : ℤ)+1≤2*(2 : ℤ) := by
  exact first_index_lower_of_dvd (by decide : 0<(8 : ℕ))
    (by norm_num : (16 : ℤ) ∣ 2*(8 : ℤ)) (by norm_num)
    (by norm_num [Pell.yn_succ] : (68 : ℤ)=2*(Pell.yn base17 2 : ℤ))
    (by norm_num : (16 : ℤ) ∣ 68-3-1)

example : 2*((2 : ℕ)*(1+1)+2)<2*(2*(1*2^2)+1)-1 :=
  base_separation (by decide) (by decide)

-- The full client takes the literal A0/A1 cuts, not either classification.
example (ports : Fin 4 → ℤ) (hports : NativePellBootstrap.PortBox ports)
    (hbeta : 15≤ports 0) {J F alpha X Y k eta gamma r q R Bt : ℤ}
    (hJ : 0<J) (hF : 0<F) (halpha : 0<alpha)
    (hX : 0<X) (hY : 0<Y) (hk : 0<k)
    (heta : 0<eta) (hgamma : 0<gamma) (hr : 0<r)
    (hq : q=ports 0*J+1)
    (hR : R=target q F alpha J (ports 2) (ports 3))
    (hBt : Bt=(q*ports 1+X)*(q-F-alpha)-q*F)
    (h0 : firstA0 q (X*k*Y^2) k r Y Bt=0)
    (h1 : mainA1 q X Y k eta gamma (k-R-1)=0) :
    2*R<k*Y+eta := by
  obtain ⟨_,_,n,p,D,_,_,_,_,_,_,_,_,_,_,hhalf⟩ :=
    adaptive_early_bounds ports hports hbeta hJ hF halpha hX hY hk heta hgamma hr hq hR hBt h0 h1
  exact hhalf

#print axioms target_window
#print axioms first_index_residue_of_dvd
#print axioms first_index_lower_of_dvd
#print axioms base_separation
#print axioms adaptive_early_bounds

end DiophantineConsistency.NativeAdaptiveRankWindowChecks
