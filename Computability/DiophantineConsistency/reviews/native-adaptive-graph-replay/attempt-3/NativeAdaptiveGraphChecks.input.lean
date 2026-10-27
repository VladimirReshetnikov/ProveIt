import DiophantineConsistency.NativeAdaptiveGraph

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.NativeAdaptiveGraphChecks
open NativeAdaptiveGraph

-- The declared input order binds all thirteen coordinates through these cuts.
example (p : Fin 4 → ℤ) (x : Fin 13 → ℤ) :
    (core p x).q=p 0*x 0+1 ∧
    (core p x).Bt=((core p x).q*p 1+x 6)*((core p x).q-x 1-x 2)-(core p x).q*x 1 ∧
    (core p x).k=x 9+x 10 := ⟨q_eq p x,Bt_eq p x,k_eq p x⟩

example (p : Fin 4 → ℤ) (x : Fin 13 → ℤ) :
    (core p x).V=NativeAdaptiveStrongIndex.auxiliaryValue (core p x).c (x 3) (x 5) (core p x).rank :=
  V_eq p x

example (p : Fin 4 → ℤ) (x : Fin 13 → ℤ) :
    (core p x).A0=NativeAdaptiveCarrierBootstrap.firstA0 (core p x).q
      (core p x).ell (core p x).k (x 8) (x 7) (core p x).Bt := A0_eq p x

example (p : Fin 4 → ℤ) (x : Fin 13 → ℤ) :
    (core p x).A1=NativeAdaptiveMainBootstrap.mainA1 (core p x).q (x 6) (x 7)
      (core p x).k (x 9) (x 12) ((core p x).k-(core p x).rank-1) := A1_eq p x

-- The literal fourth port appears once in the source-shifted target.
example (p : Fin 4 → ℤ) (x : Fin 13 → ℤ) :
    (core p x).rank=((core p x).q-1)*((core p x).q-x 1)*((core p x).q^2-1)+
      x 2*((core p x).q^2-1)+(p 2+(core p x).q*p 3)*x 0 := by
  rw [rank_eq]
  unfold NativeAdaptiveMainBootstrap.target
  ring

-- Signed unit extraction really has no positivity premise. This zero is outside
-- the strictly positive source domain (J=0, i=0, r=0, gamma=0).
def outsideDomain (j : Fin 13) : ℤ := if j=3 ∨ j=11 then 1 else 0
example : value (fun _ => (0:ℤ)) outsideDomain=0 := by decide
example : ¬(∀ j,0<outsideDomain j) := by
  intro h
  have h0 := h 0
  norm_num [outsideDomain] at h0

example (p : Fin 4 → ℤ) (x : Fin 13 → ℤ)
    (hz : value p x=0) :
    (core p x).A0=0 ∧ (core p x).A1=0 ∧ (core p x).Fs=1 ∧ (core p x).Fa=1 :=
  (value_zero_iff_factors p x).mp hz

#print axioms value_map
#print axioms eval_polynomial
#print axioms rank_eq
#print axioms firstZ_eq
#print axioms Dstar_eq
#print axioms value_zero_iff_factors
#print axioms value_zero_iff_cuts
#print axioms positive_zero_source
end DiophantineConsistency.NativeAdaptiveGraphChecks
