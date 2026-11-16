import PA194HXNativeAlignment
import ConPAMachineCompressedExecutor
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PA194HXRowData
open PA194HXNativeLabels PA194HXContracts ConPA.Machine

abbrev RowView := Nat × Nat × Nat × Bool × Nat
def view (row : Row) : RowView := (row.q,row.b,row.w,row.right,row.q')
theorem view_injective : Function.Injective view := by
  intro r s h
  cases r
  cases s
  simpa [view,Row.mk.injEq] using h

def denseControl (q : Nat) : Nat := labels.idxOf q

def validNative (q : Nat) (b : Bool) : Bool :=
  match PA194HXContracts.cachedMachine q b with
  | none => true
  | some (w,dir,q') =>
    let i := 2 * denseControl q + b.toNat
    decide (i < PA194HXRows.rows.length) &&
      decide (view (PA194BModelSteps.indexedRow PA194HXRows.rows i) =
        (denseControl q,b.toNat,w.toNat,dir,denseControl q'))

theorem listed_valid : ∀ i : Fin 195, ∀ b : Bool,
    validNative (labels.getD i.val 254) b = true := by decide +kernel

theorem keys_listed : PA194FoldedCache.table.keys.all (fun q => decide (q ∈ labels)) = true := by
  decide +kernel


#print axioms listed_valid
#print axioms keys_listed
end PA194HXRowData
