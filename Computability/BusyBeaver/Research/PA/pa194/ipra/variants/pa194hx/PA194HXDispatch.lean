import PA194HXLiteral
import PA194HXRows
import PA194BModelSteps
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSectionVars false
namespace PA194HXDispatch
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194BModelSteps

def table : ConPA.Machine.Table := PA194BModelSteps.table PA194HXRows.rows

theorem rowCount : PA194HXRows.rows.length = 388 := by decide +kernel

/-- The arithmetic transition list and the HX literal table agree at every
    working control and both possible read symbols. -/
theorem literalRows : ∀ q : Fin 194, ∀ b : Fin 2,
    let a := PA194HXRows.rows.getD (2*q.val+b.val) (0,0,194)
    PA194HX.Literal.machine q.val (b.val != 0) = some (a.1 != 0,a.2.1 != 0,a.2.2) := by
  decide +kernel

section models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem stepRow (q b : Nat) (l r : V) (hq : q < 194) (hb : b < 2)
    (hr : r % 2 = (b : V)) :
    ConPA.Machine.step table (config q l r) =
      next (PA194HXRows.rows.getD (2*q+b) (0,0,194)) l r := by
  exact PA194BModelSteps.stepRow PA194HXRows.rows q b l r hb (by rw [rowCount]; omega) hr

theorem haltFixed (l r : V) :
    ConPA.Machine.step table (config 194 l r) = config 194 l r :=
  PA194BModelSteps.halted PA194HXRows.rows rowCount l r

#print axioms stepRow
#print axioms haltFixed
end models
#print axioms rowCount
#print axioms literalRows
end PA194HXDispatch
