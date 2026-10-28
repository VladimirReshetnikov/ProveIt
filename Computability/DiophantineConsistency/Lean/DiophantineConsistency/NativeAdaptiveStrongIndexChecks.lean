import DiophantineConsistency.NativeAdaptiveStrongIndex

set_option autoImplicit false
set_option Elab.async false

namespace DiophantineConsistency.NativeAdaptiveStrongIndexChecks

open NativeAdaptiveStrongIndex NativeAdaptiveCarrierBootstrap NativeAdaptiveMainBootstrap

-- Exact quotient algebra does not assume the main index has been recovered.
example (c f T R h : ℤ) (hh : f^2-1=c^2*h) :
    auxiliaryValue c f T R=(f^2*T-R*c*h-1)*c-R := by
  dsimp [auxiliaryValue]
  linear_combination -R*hh

example : auxiliaryValue 10 2 1 4=14 := by norm_num [auxiliaryValue]

-- The literal polynomial's alternative evaluation order is identical.
example (a c f T R u : ℤ) :
    auxiliaryFactor a c f T R u =
      (auxiliaryValue c f T R+u)^2-
        ((a+2)^2-1)*(f^2-1)*((auxiliaryValue c f T R+u)^2-(auxiliaryValue c f T R)^2) := by
  dsimp [auxiliaryFactor]
  ring

-- This client supplies literal cuts only, never a source or main index.
example (ports : Fin 4 → ℤ) (hports : NativePellBootstrap.PortBox ports)
    (hbeta : 15≤ports 0) {J F alpha X Y k eta gamma r q R Bt f i T u : ℤ}
    (hJ : 0<J) (hF : 0<F) (halpha : 0<alpha)
    (hX : 0<X) (hY : 0<Y) (hk : 0<k)
    (heta : 0<eta) (hgamma : 0<gamma) (hr : 0<r)
    (hf : 0<f) (hi : 0 < i) (hT : 0<T) (hu : 0<u)
    (hq : q=ports 0*J+1)
    (hR : R=target q F alpha J (ports 2) (ports 3))
    (hBt : Bt=(q*ports 1+X)*(q-F-alpha)-q*F)
    (h0 : firstA0 q (X*k*Y^2) k r Y Bt=0)
    (h1 : mainA1 q X Y k eta gamma (k-R-1)=0)
    (hs : strongFactor (Y*(X+1)) (k*Y+eta) f i=1)
    (ha : auxiliaryFactor (Y*(X+1)) (k*Y+eta) f T R u=1) :
    k*Y+eta=(Pell.yn (by omega : 1<(Y*(X+1)).toNat+2) R.toNat : ℤ) := by
  obtain ⟨D,_,_,_,hc,_⟩ := adaptive_main_index_exact ports hports hbeta
    hJ hF halpha hX hY hk heta hgamma hr hf hi hT hu hq hR hBt h0 h1 hs ha
  exact hc

#print axioms strong_square_divisibility
#print axioms literal_index_of_strong
#print axioms adaptive_main_index_exact

end DiophantineConsistency.NativeAdaptiveStrongIndexChecks
