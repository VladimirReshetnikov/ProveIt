import PA194EqualZeroElimination
import PA194EmptyOrderIso
import PA194OrderIsoZeroReverse
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace PA194EqualZero
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph
open PA194InverseEqual
variable {Γ : List Form}

def unique (a b : Nat) (E : FormulaEquality Γ)
    (ha : ND.Proof Γ (equalZeroAt a)) (hb : ND.Proof Γ (equalZeroAt b)) :
    ND.Proof Γ (equalAt a b) := by
  apply eliminate a (equalAt a b) ha
  intro Δ hinc hax
  let E' := E.shifted.shifted.weaken hinc
  have hb' : ND.Proof Δ (equalZeroAt (b+1+1)) := by
    have h := ND.weaken (ND.shiftProof (ND.shiftProof hb)) hinc
    simpa only [equalZeroAt_shift] using h
  rw [equalAt_shift,equalAt_shift]
  apply eliminate (b+1+1) (equalAt (a+1+1) (b+1+1)) hb'
  intro Ω hinc' hby
  let E'' := E'.shifted.shifted.weaken hinc'
  let hax' := hax.shift.shift.weaken hinc'
  have hx := zeroFromIsoReverse (1+1+1) (0+1+1) hax'.zero hax'.iso
  have hy := zeroFromIsoReverse 1 0 hby.zero hby.iso
  have hiso := emptyOrderIso E'' (1+1+1) 1 hx hy
  rw [equalAt_shift,equalAt_shift]
  exact equalFromWitnesses (a+1+1+1+1) (b+1+1+1+1) (1+1+1) 1 hax'.left hby.left hiso
#print axioms unique
end PA194EqualZero
