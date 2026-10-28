import DiophantineConsistency.ArithmeticRegisterBoxes215

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticRegisterBoxes215Checks
open SetTheory.BusyBeaver.ZFC LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticMachineTape215 ArithmeticRegisterBoxes215
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (d z : V) : repeat3 d 0 z=z := repeat3_zero d z
example (d n z : V) : repeat3 d (n+1) z=d+8*repeat3 d n z := repeat3_succ d n z
example (n L R : V) : runFrom (3*n) (frameSparse 0 L (repeat3 6 n R))=
    frameSparse 0 (repeat3 5 n L) R := carry_spares n L R
example (n L R : V) : runFrom (3*n) (leftFrame 40 (repeat3 3 n L) R)=
    leftFrame 40 L (repeat3 6 n R) := return_spares n L R

-- All nine selectors, with arbitrary internal data and positive execution clocks.
example (v : Fin 9 → V) (r : Fin 9) (L k : V) :
    ∃ t : V, 0<t ∧ runFrom t (frameSparse (skipState r) L (plain v k))=
      leftFrame (markExit r) L (marked v r k) := box_mark v r L k
example (v : Fin 9 → V) (r : Fin 9) (L k : V) :
    ReachPos (frameSparse 64 L (marked v r k))
      (leftFrame 40 L (plain (Function.update v r (v r+1)) (k+1))) := box_inc v r L k
example (v : Fin 9 → V) (r : Fin 9) (L k : V) (hk : 0<k) (hv : v r=0) :
    ReachPos (frameSparse 0 L (marked v r k)) (leftFrame 97 L (plain v k)) := box_dec0 v r L k hk hv
example (v : Fin 9 → V) (r : Fin 9) (L k : V) (hv : 0<v r) :
    ReachPos (frameSparse 0 L (marked v r k))
      (leftFrame 40 (2*L+1) (plain (Function.update v r (v r-1)) k)) := box_decp v r L k hv

-- The last zero primary has a following spare, even at k=1 and L=0.
example : ReachPos (frameSparse 0 (0:V) (marked (fun _ => 0) 8 1))
    (leftFrame 97 0 (plain (fun _ => 0) 1)) := box_dec0 _ _ _ _ (by simp) rfl
-- INC does not need an existing spare; it appends precisely one.
example : ReachPos (frameSparse 64 (0:V) (marked (fun _ => 0) 8 0))
    (leftFrame 40 0 (plain (Function.update (fun _ => 0) 8 (1:V)) 1)) := by
  simpa using box_inc (fun _ : Fin 9 => (0:V)) 8 0 0
-- A decrement of one retains the literal extra left bit and exits through40.
example (k : V) : ReachPos (frameSparse 0 (0:V) (marked (fun _ => 1) 0 k))
    (leftFrame 40 1 (plain (Function.update (fun _ => 1) 0 (0:V)) k)) := by
  simpa using box_decp (fun _ : Fin 9 => (1:V)) 0 0 k (by simp)
example (L : V) : runFrom 6 (frameSparse 0 L 0)=leftFrame 40 (2*L+1) 6 := increment_tail L
example (v : Fin 9 → V) (r : Fin 9) (k : V) : marked v r k=
    file (before v r) (4*bitPrefix true (v r) (file (after v r) (repeat3 6 k 0))) := by
  rw [marked,markedBlock_eq]
example : engineRows.length=45 := engine_rows_length
example : KTableCore.tm215 198 false=some (true,false,40) := rfl

#print axioms repeat3_defined
#print axioms scan_right
#print axioms scan_left
#print axioms carry_spares
#print axioms return_spares
#print axioms mark_local
#print axioms decrement_zero_local
#print axioms increment_tail
#print axioms box_mark
#print axioms box_inc
#print axioms box_dec0
#print axioms box_decp
#print axioms engine_rows_checked
#print axioms engine_rows_coverage
end DiophantineConsistency.ArithmeticRegisterBoxes215Checks
