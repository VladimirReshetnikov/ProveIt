import PA194CompressedExecutor
import PA194LocalQuotient

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

namespace PA194FoldedRuntimeRows
open PA194LocalQuotient PA194BidirectionalRow PA194CompressedExecutor

/-- Dense encoding of the native control used by the register oracle. Unknown
native controls map outside the active literal table. -/
def denseControl (q : Nat) : Nat := labels.idxOf q

def nativeControl (q : Nat) : Nat := labels[q]?.getD 254

/-- Request a symbolic transition directly from the literal folded table.
The checks ensure the symbolic native control and literal dense label agree,
and that the symbols and direction are Boolean. -/
def machine (q : Nat) (b : Bool) : Option (Bool × Bool × Nat) :=
  let d := denseControl q
  let (w,m,k) := PA194Rows.rows.getD (d+d+bit b) (0,0,194)
  let q' := nativeControl k
  if d < 194 ∧ w ≤ 1 ∧ m ≤ 1 ∧ denseControl q' = k then
    some (decide (w=1),decide (m=1),q')
  else none

theorem agreement : RowAgreement machine denseControl := by
  intro q b w dir q' h
  let d := denseControl q
  cases hh : PA194Rows.rows.getD (d+d+bit b) (0,0,194) with
  | mk sym rest =>
    cases rest with
    | mk mov dst =>
      have hh' : PA194Rows.rows.getD (denseControl q+denseControl q+bit b) (0,0,194) =
          (sym,mov,dst) := hh
      have eq : machine q b =
          if denseControl q < 194 ∧ sym ≤ 1 ∧ mov ≤ 1 ∧ denseControl (nativeControl dst) = dst
          then some (decide (sym=1),decide (mov=1),nativeControl dst)
          else none := by
        simp only [machine,hh']
      rw [eq] at h
      split at h
      · rename_i gv
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl,rfl,rfl⟩ := h
        have hb (n : Nat) (hn : n ≤ 1) : bit (decide (n=1)) = n := by
          have he : n = 0 ∨ n = 1 := by omega
          rcases he with rfl | rfl <;> rfl
        exact ⟨gv.1,by rw [hb sym gv.2.1,hb mov gv.2.2.1,gv.2.2.2]⟩
      · simp at h

theorem root_control : denseControl 84 = 24 := by decide +kernel
theorem terminal_control : denseControl 254 = 194 := by decide +kernel
#print axioms agreement
#print axioms root_control
#print axioms terminal_control
end PA194FoldedRuntimeRows
