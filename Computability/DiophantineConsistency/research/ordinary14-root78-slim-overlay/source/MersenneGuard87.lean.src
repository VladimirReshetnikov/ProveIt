import GuardStrict87Linear
import ModifiedCarrierFacts

/-! Source-only model reduction of the 87 strict guard to the two power
calibration facts. These facts are explicit premises, not inferred here. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.MersenneGuard87Draft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing PositiveMap86To87Draft
open ModifiedCarrierFactsDraft GuardStrict87LinearDraft
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Explicit Mersenne and power-recovery premises imply the strict guard
needed for the reverse map. Neither calibration premise follows here from hz. -/
theorem strict_of_power (p : Fin 4 → ℤ) (beta K t R : V) (v : Fin 14 → V)
    (hbeta : 0<beta) (ht : 4≤t) (hradix : beta=Exp.exp t-1)
    (hport : (p 0 : DiffRing V)=ι beta) (hK : (p 1 : DiffRing V)=ι K)
    (hv : ∀ j, 0<v j) (hX : v 6=Exp.exp R)
    (h3 : q beta v∣3*v 6)
    (hz : InternalZero (P87ShiftedGuard.graph p).output v) :
    C beta v*K<v 13 := by
  have hq : q beta v=(Exp.exp t-1)*v 0+1 := by
    dsimp [q]
    rw [hradix]
    ring
  have hd : q beta v∣v 6 := mersenne_divides_X t R _ (v 0) (v 6) ht hq hX h3
  have hbound : q beta v≤v 6 := Arithmetic.le_of_dvd (hv 6) hd
  exact strict_of_large_X p beta K v hbeta hport hK hv hbound hz

end DiophantineConsistency.MersenneGuard87Draft

#print axioms DiophantineConsistency.MersenneGuard87Draft.strict_of_power
