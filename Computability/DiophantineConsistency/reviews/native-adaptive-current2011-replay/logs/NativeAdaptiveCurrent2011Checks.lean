import DiophantineConsistency.NativeAdaptiveCurrent2011

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.NativeAdaptiveCurrent2011Checks
open NativeAdaptiveCurrent2011 CurrentCarrierArithmetic2011
attribute [local irreducible] CurrentKernel2011.K

example (p : Fin 4 → ℤ) {d MC MF : ℕ}
    (hi : NativeSourceMask.Interface p d MC MF) (h4 : MC % 4 = 2)
    (x : Fin 13 → ℤ) (hx : ∀ j, 0 < x j)
    (hz : MvPolynomial.eval x (NativeAdaptiveGraph.polynomial p) = 0) :
    ∃ v : Fin 14 → ℤ, (∀ j, 0 < v j) ∧
      MvPolynomial.eval v (Carrier65.polynomial p) = 0 ∧
      v 0 = x 0 ∧ v 1 = x 1 ∧ v 2 = x 2 := by
  rw [NativeAdaptiveGraph.eval_polynomial] at hz
  obtain ⟨v,hv,h0,hJ,hF,hA⟩ := adaptive_zero_carrier_zero p hi h4 x hx hz
  exact ⟨v,hv,by rwa [Carrier65.eval_polynomial],hJ,hF,hA⟩

example (p : Fin 4 → ℤ) {d MC MF : ℕ}
    (hi : NativeSourceMask.Interface p d MC MF) (h4 : MC % 4 = 2)
    (hp : Carrier65Witness.PortBounds p) :
    PositiveZero (NativeAdaptiveGraph.polynomial p) ↔
      PositiveZero (Carrier65.polynomial p) :=
  positive_polynomial_zero_iff_carrier p hi h4 hp

example : polynomial = NativeAdaptiveGraph.polynomial
    (CurrentMasks2011.ports (CurrentKernel2011.K : ℤ)) := rfl

example (x : Fin 13 → ℤ) :
    (NativeAdaptiveGraph.core currentPorts x).rank =
      NativeAdaptiveMainBootstrap.target (NativeAdaptiveGraph.core currentPorts x).q
        (x 1) (x 2) (x 0) (CurrentMasks2011.lowPort : ℤ)
        ((CurrentMasks2011.highPort + CurrentMasks2011.beta : ℕ) : ℤ) :=
  NativeAdaptiveGraph.rank_eq currentPorts x

example : (¬ ∃ x : Fin 13 → ℤ, (∀ j, 0 < x j) ∧
    MvPolynomial.eval x polynomial = 0) ↔ DiophantineConsistency.ConZFC :=
  no_positive_zero_iff_conZFC

example (h : ¬ DiophantineConsistency.ConZFC) :
    ∃ x : Fin 13 → ℤ, (∀ j, 0 < x j) ∧ MvPolynomial.eval x polynomial = 0 :=
  not_conZFC_positive_zero h

#print axioms adaptive_zero_carrier_zero
#print axioms positive_zero_iff_carrier
#print axioms positive_polynomial_zero_iff_carrier
#print axioms current_width
#print axioms current_ports
#print axioms current_positive_zero_iff_carrier
#print axioms current_positive_zero_iff_source
#print axioms positive_zero_iff_not_conZFC
#print axioms no_positive_zero_iff_conZFC
#print axioms not_conZFC_positive_zero
end DiophantineConsistency.NativeAdaptiveCurrent2011Checks
