import DiophantineConsistency.NativeAdaptiveCanonical
import DiophantineConsistency.NativeOrdinarySourceConstruction

/-! Positive-zero existence for the literal adaptive graph, first over its
complete scalar interfaces and then at the current length2011 ports.
The final consistency equivalence is external Lean mathematics, not an
object-language HA derivation or a degree/operation certificate. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace DiophantineConsistency.NativeAdaptiveCurrent2011

open CurrentCarrierArithmetic2011
attribute [local irreducible] CurrentKernel2011.K

/-- All positive adaptive zeros supply an actual Carrier65 zero. Private
Pell seeds are rebuilt; the same J,F,alpha remain visible. -/
theorem adaptive_zero_carrier_zero (p : Fin 4 → ℤ) {d MC MF : ℕ}
    (hi : NativeSourceMask.Interface p d MC MF) (hMC4 : MC % 4 = 2)
    (x : Fin 13 → ℤ) (hx : ∀ j, 0 < x j)
    (hz : NativeAdaptiveGraph.value p x = 0) :
    ∃ v : Fin 14 → ℤ, (∀ j, 0 < v j) ∧ Carrier65.value p v = 0 ∧
      v 0 = x 0 ∧ v 1 = x 1 ∧ v 2 = x 2 := by
  obtain ⟨s,hs,hrows,hJ,hF,hA,_⟩ :=
    NativeAdaptiveGraph.positive_zero_source p hi.portBox hi.width hi.beta x hx hz
  obtain ⟨v,hv,hzero,h0,h1,h2,_⟩ :=
    NativeOrdinarySourceConstruction.source_constructs_carrier65 p hi hMC4 s hs hrows
  rw [Carrier65.eval_polynomial] at hzero
  exact ⟨v,hv,hzero,h0.trans hJ,h1.trans hF,h2.trans hA⟩

/-- The forward mask/rank interfaces and reverse PortBounds are all retained. -/
theorem positive_zero_iff_carrier (p : Fin 4 → ℤ) {d MC MF : ℕ}
    (hi : NativeSourceMask.Interface p d MC MF) (hMC4 : MC % 4 = 2)
    (hp : Carrier65Witness.PortBounds p) :
    (∃ x : Fin 13 → ℤ, (∀ j, 0 < x j) ∧ NativeAdaptiveGraph.value p x = 0) ↔
    (∃ v : Fin 14 → ℤ, (∀ j, 0 < v j) ∧ Carrier65.value p v = 0) := by
  constructor
  · rintro ⟨x,hx,hz⟩
    obtain ⟨v,hv,h0,_⟩ := adaptive_zero_carrier_zero p hi hMC4 x hx hz
    exact ⟨v,hv,h0⟩
  · rintro ⟨v,hv,hz⟩
    obtain ⟨x,hx,h0,_⟩ := NativeAdaptiveCanonical.carrier_zero_adaptive_zero p hp v hv hz
    exact ⟨x,hx,h0⟩

theorem positive_polynomial_zero_iff_carrier (p : Fin 4 → ℤ) {d MC MF : ℕ}
    (hi : NativeSourceMask.Interface p d MC MF) (hMC4 : MC % 4 = 2)
    (hp : Carrier65Witness.PortBounds p) :
    PositiveZero (NativeAdaptiveGraph.polynomial p) ↔
      PositiveZero (Carrier65.polynomial p) := by
  simpa only [PositiveZero,NativeAdaptiveGraph.eval_polynomial,Carrier65.eval_polynomial]
    using positive_zero_iff_carrier p hi hMC4 hp

/-- This is the complete current tuple, with the source high port shifted once. -/
abbrev currentPorts : Fin 4 → ℤ := CurrentMasks2011.ports (CurrentKernel2011.K : ℤ)

noncomputable def polynomial : MvPolynomial (Fin 13) ℤ :=
  NativeAdaptiveGraph.polynomial currentPorts

theorem current_width : CurrentMasks2011.width = 94517 := rfl

theorem current_ports :
    currentPorts 0 = (CurrentMasks2011.beta : ℤ) ∧
    currentPorts 1 = (CurrentKernel2011.K : ℤ) ∧
    currentPorts 2 = (CurrentMasks2011.lowPort : ℤ) ∧
    currentPorts 3 = ((CurrentMasks2011.highPort + CurrentMasks2011.beta : ℕ) : ℤ) :=
  ⟨rfl,rfl,rfl,rfl⟩

theorem current_positive_zero_iff_carrier :
    PositiveZero polynomial ↔ PositiveZero CurrentPolynomialWindow2011.polynomial := by
  have hK : (0 : ℤ) < CurrentKernel2011.K := by exact_mod_cast CurrentKernel2011.K_pos
  exact positive_polynomial_zero_iff_carrier currentPorts CurrentWindowCarry2011.interface
    CurrentMasks2011.lowPort_four (CurrentCarrierArithmetic2011.portBounds _ hK)

theorem current_positive_zero_iff_source :
    PositiveZero polynomial ↔ NativeOrdinarySourceConstruction.CurrentPositiveSource :=
  current_positive_zero_iff_carrier.trans
    NativeOrdinarySourceConstruction.current_source_iff_positive_zero.symm

/-- The actual fixed polynomial and the repository's exact syntactic axiom predicate. -/
theorem positive_zero_iff_not_conZFC :
    PositiveZero polynomial ↔ ¬ DiophantineConsistency.ConZFC :=
  current_positive_zero_iff_carrier.trans CurrentPositiveZero2011.positive_zero_iff_not_conZFC

theorem no_positive_zero_iff_conZFC :
    (¬ PositiveZero polynomial) ↔ DiophantineConsistency.ConZFC :=
  (not_congr current_positive_zero_iff_carrier).trans
    CurrentPositiveZero2011.no_positive_zero_iff_conZFC

theorem not_conZFC_positive_zero (h : ¬ DiophantineConsistency.ConZFC) :
    ∃ x : Fin 13 → ℤ, (∀ j, 0 < x j) ∧ MvPolynomial.eval x polynomial = 0 :=
  positive_zero_iff_not_conZFC.mpr h

end DiophantineConsistency.NativeAdaptiveCurrent2011
