module
/- M6 PA-model runtime port. This is a fresh append-one/table adaptation;
its theorem scope is not the completed PA-unprovability endpoint. -/
public import PA196.Arithmetic.Machine.PAInternalNativeRows
public import Mathlib.Tactic.Ring.Basic
@[expose] public section

namespace PA196.Arithmetic.Machine.PA.InternalTrace.MarkSkipGeneric
open M6
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic
open ScanBits
attribute [local irreducible] Step StepFormula.formula
section Models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]

theorem segment (q q' : Nat)
    (r0 : NativeTable.machine q false=some (false,true,q'))
    (self : NativeTable.machine q' true=some (true,true,q')) (n l t : V) : ∃ qs ls rs,
    Segment (n+2) qs ls rs (NativeRows.code q) l (4*repeatBits n 1 t+2)
      (NativeRows.code q') (repeatBits n 1 (4*l+1)) t := by
  have a := NativeRows.right r0 l
    ((1+1)*repeatBits n 1 t+1)
  simp only [Bool.toNat_false,Nat.cast_zero,add_zero] at a
  have b := NativeRows.right self
    ((1+1)*l) (repeatBits n 1 t)
  simp only [Bool.toNat_true,Nat.cast_one] at b
  obtain ⟨qs,ls,rs,h⟩ := NativeRows.scan_right self n ((1+1)*((1+1)*l)+1) t
  simp only [Bool.toNat_true,Nat.cast_one] at h
  have joined := segment_prepend a (segment_prepend b h)
  have hl : (1+1)*((1+1)*l)+1=4*l+1 := by ring1
  have hi : (1+1)*((1+1)*repeatBits n 1 t+1)=4*repeatBits n 1 t+2 := by ring1
  have result : ∃ qs ls rs,
      Segment (n+1+1) qs ls rs (NativeRows.code q) l ((1+1)*((1+1)*repeatBits n 1 t+1))
        (NativeRows.code q') (repeatBits n 1 ((1+1)*((1+1)*l)+1)) t := ⟨_,_,_,joined⟩
  simpa only [hl,hi,show n+1+1=n+2 by ring1] using result
theorem skip_cell (j : Nat) (hj : j<8) (n l t : V) : ∃ qs ls rs,
    Segment (n+2) qs ls rs (NativeRows.code (Runtime.sk (j+1))) l (4*repeatBits n 1 t+2)
      (NativeRows.code (Runtime.sk j)) (repeatBits n 1 (4*l+1)) t :=
  segment _ _ (Native.sk_next NativeTable.engine_rows j hj)
    (Native.sk_self NativeTable.engine_rows j (by omega)) n l t
end Models

#print axioms segment
end PA196.Arithmetic.Machine.PA.InternalTrace.MarkSkipGeneric

