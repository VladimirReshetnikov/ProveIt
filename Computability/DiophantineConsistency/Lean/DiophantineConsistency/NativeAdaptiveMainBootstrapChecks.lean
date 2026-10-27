import DiophantineConsistency.NativeAdaptiveMainBootstrap

set_option autoImplicit false
set_option Elab.async false

namespace DiophantineConsistency.NativeAdaptiveMainBootstrapChecks

open NativeAdaptiveMainBootstrap

-- These sign controls are generic arithmetic examples, not complete
-- thirteen-input polynomial zeros. q=3 is allowed and v may be negative.
example : 0 < mainDstar 3 1 27 2 1 1 (-10) := by
  exact mainDstar_positive (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example : mainDstar 3 1 27 2 1 1 (-10) = 795099 := by
  norm_num [mainDstar]

example : 0 < target 3 1 1 3 0 0 := by
  exact target_positive (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

-- The signed-to-natural classification retains the positive first root.
example : ∃ p : ℕ, 0 < p ∧
    (3 : ℤ)=(Pell.xn (by decide : 1 < 3) p : ℤ) ∧
    (1 : ℤ)=(Pell.yn (by decide : 1 < 3) p : ℤ) := by
  exact classify_positive_main_norm (by norm_num : (0 : ℤ) ≤ 1)
    (by norm_num : (0 : ℤ) < 1) (by norm_num : (0 : ℤ) < 3) (by norm_num)

example {q X Y k eta gamma v : ℤ}
    (hq : 1 < q) (hX : 0 < X) (hY : 0 < Y)
    (hk : 0 < k) (heta : 0 < eta) (hgamma : 0 < gamma)
    (hYdiv : q^3 ∣ Y) (hv : v < k)
    (h1 : mainA1 q X Y k eta gamma v=0) : q^4 ∣ v := by
  obtain ⟨D,hD,he,hn,hd,hp⟩ := main_carrier_bootstrap hq hX hY hk heta hgamma hYdiv hv h1
  exact hd

example {q X Y k eta gamma F alpha J MC MF : ℤ}
    (hq : 1 < q) (hX : 0 < X) (hY : 0 < Y)
    (hk : 0 < k) (heta : 0 < eta) (hgamma : 0 < gamma)
    (hYdiv : q^3 ∣ Y) (halpha : 0 < alpha) (hJ : 0 < J)
    (hMC : 0 ≤ MC) (hMF : 0 ≤ MF) (hC : 0 < q-F-alpha)
    (h1 : mainA1 q X Y k eta gamma (k-target q F alpha J MC MF-1)=0) :
    q^4 ∣ k-target q F alpha J MC MF-1 := by
  obtain ⟨D,hD,he,hn,hd,hp⟩ := main_carrier_of_target hq hX hY hk heta hgamma hYdiv
    halpha hJ hMC hMF hC h1
  exact hd

#print axioms target
#print axioms mainDstar
#print axioms mainA1
#print axioms target_positive
#print axioms target_positive_of_transport
#print axioms mainDstar_positive
#print axioms classify_positive_main_norm
#print axioms main_carrier_bootstrap
#print axioms main_carrier_of_target

end DiophantineConsistency.NativeAdaptiveMainBootstrapChecks
