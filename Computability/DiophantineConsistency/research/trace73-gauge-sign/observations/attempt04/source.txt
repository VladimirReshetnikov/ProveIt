import Trace73Gauge
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.Ring.Basic

/-! A conditional negative-B positive zero, using the actual graph gauge. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
noncomputable section
namespace Trace73GaugeSign
open DiophantineConsistency.TenPositiveTrace75
variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

theorem B_negative_after_one (p : Fin 4 → R) (v : Fin 10 → R)
    (hh : 1 ≤ (regs p v).h) (hk : 0 ≤ p 1+v 5)
    (hf : 0<v 1) (ha : 0<v 2) :
    (regs p (Trace73Gauge.move p v 1)).B < 0 := by
  rw [Trace73Gauge.B_move]
  let h := p 0*v 0
  let k := p 1+v 5
  change 1 ≤ h at hh
  change 0 ≤ k at hk
  have hq : 0≤h+1 := by linarith
  have hstep : 0≤k*(h+1)+1 := by
    have := mul_nonneg hk hq
    linarith
  have hmul : 0≤(h-1)*(k*(h+1)+1) := mul_nonneg (by linarith) hstep
  have hmask : 0≤k*(v 1+v 2) := mul_nonneg hk (le_of_lt (add_pos hf ha))
  change k*((h+1)-v 1-v 2)-v 1-h*(k*(h+1)+1)*1<0
  nlinarith

theorem positive_zero_to_negative_B (p : Fin 4 → R) (v : Fin 10 → R)
    (hh : 1 ≤ (regs p v).h) (hk : 0 ≤ p 1+v 5)
    (hv : ∀ j, 0<v j) (hc : Trace73Gauge.step p v < v 7)
    (hz : Trace73Literal.graph73 p v = 0) :
    ∃ w : Fin 10 → R, (∀ j, 0<w j) ∧
      (regs p w).B < 0 ∧ Trace73Literal.graph73 p w = 0 := by
  let w := Trace73Gauge.move p v 1
  have hw : ∀ j, 0<w j := by
    intro j
    by_cases h1 : j=1
    · subst j
      change 0 < v 1 + (regs p v).h*1
      have := hv 1
      nlinarith
    by_cases h2 : j=2
    · subst j
      change 0 < v 2 + (regs p v).h*(regs p v).h*1
      have := hv 2
      have hs := sq_nonneg ((regs p v).h)
      nlinarith
    by_cases h7 : j=7
    · subst j
      change 0 < v 7-Trace73Gauge.step p v*1
      linarith
    · simpa [w,Trace73Gauge.move,h1,h2,h7] using hv j
  refine ⟨w,hw,B_negative_after_one p v hh hk (hv 1) (hv 2),?_⟩
  change Trace73Literal.graph73 p (Trace73Gauge.move p v 1) = 0
  rwa [Trace73Gauge.graph_move]

#print axioms Trace73GaugeSign.B_negative_after_one
#print axioms Trace73GaugeSign.positive_zero_to_negative_B
end Trace73GaugeSign
