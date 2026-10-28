import DiophantineConsistency.NativeAdaptiveCanonical

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.NativeAdaptiveCanonicalChecks
open NativeAdaptiveCanonical

example (p : Fin 4 → ℤ) (hp : Carrier65Witness.PortBounds p) :
    NativePellBootstrap.PortBox p := portBox_of_bounds p hp

example (p : Fin 4 → ℤ) (hp : NativePellBootstrap.PortBox p) (hb : 15≤p 0)
    (s : Fin 31 → ℕ) (hs : ∀ j, 0<s j)
    (hrows : ∀ j, SplitCertificate59.sourceRows p (fun i => (s i:ℤ)) j=0) :
    1<s 3 := source_old_z_gt_one p hp hb s hs hrows

example (p : Fin 4 → ℤ) (hp : NativePellBootstrap.PortBox p)
    (v : Fin 15 → ℤ) (hv : ∀ j, 0<v j) (hc : Carrier66.Canonical p v) :
    ∃ t : ℤ, v 9<t ∧ (Carrier66.core p v).k-(Carrier66.core p v).rank-1=
      (Carrier66.core p v).q^2*(Carrier66.core p v).Y*t :=
  canonical_shift p hp v hv hc

example (p : Fin 4 → ℤ) (v : Fin 15 → ℤ) (r gamma : ℤ) :
    assignment p v r gamma 0=v 0 ∧ assignment p v r gamma 1=v 1 ∧
    assignment p v r gamma 2=v 2 ∧ assignment p v r gamma 3=v 4 ∧
    assignment p v r gamma 4=(Carrier66.core p v).delta*v 6 ∧
    assignment p v r gamma 5=v 7 ∧
    assignment p v r gamma 6=(Carrier66.core p v).X ∧
    assignment p v r gamma 7=(Carrier66.core p v).Y ∧
    assignment p v r gamma 8=r ∧ assignment p v r gamma 9=v 11 ∧
    assignment p v r gamma 10=v 12 ∧
    assignment p v r gamma 11=v 13-(Carrier66.core p v).V ∧
    assignment p v r gamma 12=gamma := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

example (p : Fin 4 → ℤ) (hp : Carrier65Witness.PortBounds p)
    (v : Fin 14 → ℤ) (hv : ∀ j, 0<v j)
    (hz : MvPolynomial.eval v (Carrier65.polynomial p)=0) :
    ∃ x : Fin 13 → ℤ, (∀ j, 0<x j) ∧
      MvPolynomial.eval x (NativeAdaptiveGraph.polynomial p)=0 ∧
      x 0=v 0 ∧ x 1=v 1 ∧ x 2=v 2 := by
  rw [Carrier65.eval_polynomial] at hz
  obtain ⟨x,hx,h0,hJ,hF,hA⟩ := carrier_zero_adaptive_zero p hp v hv hz
  exact ⟨x,hx,by rwa [NativeAdaptiveGraph.eval_polynomial],hJ,hF,hA⟩

#print axioms portBox_of_bounds
#print axioms source_old_z_gt_one
#print axioms canonical_shift
#print axioms assignment_shapes
#print axioms canonical_adaptive_zero
#print axioms carrier_zero_adaptive_zero
end DiophantineConsistency.NativeAdaptiveCanonicalChecks
