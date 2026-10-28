import DiophantineConsistency.NativeAdaptivePowerRecovery

set_option autoImplicit false
set_option Elab.async false

namespace DiophantineConsistency.NativeAdaptivePowerRecoveryChecks
open NativeAdaptivePowerRecovery NativeAdaptiveCarrierBootstrap
open NativeAdaptiveMainBootstrap NativeAdaptiveStrongIndex

example : (6:ℕ)*8^16<9^16 := nine_dominates (by omega)

example {Y : ℤ} (hY : 0<Y) (hb : (2:ℤ)^49≤4*Y)
    (hd : 8*Y+3 ∣ 3*(1-(2:ℤ)^49)) : False :=
  unit_projection_impossible hY (by omega) hb hd

-- No source/index/parity/power premise appears in this actual-tuple client.
example (ports : Fin 4 → ℤ) (hports : NativePellBootstrap.PortBox ports)
    (hbeta : 15≤ports 0) {J F alpha X Y k eta zeta gamma r q R Bt f i T u : ℤ}
    (hJ : 0<J) (hF : 0<F) (halpha : 0<alpha)
    (hX : 0<X) (hY : 0<Y) (heta : 0<eta) (hzeta : 0<zeta)
    (hgamma : 0<gamma) (hr : 0<r)
    (hf : 0<f) (hi : 0 < i) (hT : 0<T) (hu : 0<u)
    (hk : k=eta+zeta) (hq : q=ports 0*J+1)
    (hR : R=target q F alpha J (ports 2) (ports 3))
    (hBt : Bt=(q*ports 1+X)*(q-F-alpha)-q*F)
    (h0 : firstA0 q (X*k*Y^2) k r Y Bt=0)
    (h1 : mainA1 q X Y k eta gamma (k-R-1)=0)
    (hs : strongFactor (Y*(X+1)) (k*Y+eta) f i=1)
    (ha : auxiliaryFactor (Y*(X+1)) (k*Y+eta) f T R u=1) :
    X=(2:ℤ)^R.toNat :=
  (adaptive_X_eq_two_pow ports hports hbeta hJ hF halpha hX hY heta hzeta hgamma hr
    hf hi hT hu hk hq hR hBt h0 h1 hs ha).1

#print axioms doubled_ratio_lower
#print axioms sharp_interval_growth
#print axioms nine_dominates
#print axioms binary_comparison
#print axioms large_base_growth
#print axioms unit_base_growth
#print axioms unit_projection_impossible
#print axioms small_projection_unique
#print axioms adaptive_X_eq_two_pow

end DiophantineConsistency.NativeAdaptivePowerRecoveryChecks
