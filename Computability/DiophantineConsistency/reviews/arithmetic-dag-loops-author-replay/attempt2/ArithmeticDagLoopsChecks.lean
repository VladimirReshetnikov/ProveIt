import BusyBeaver.ZFC.ArithmeticDagLoops

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SetTheory.BusyBeaver.ZFC.ArithmeticDagLoopsChecks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticDagRun ArithmeticDagLoops
open ArithmeticControlBisim (Row)
open ArithmeticControlFile (liveValue)
open ArithmeticControlTable (rows controlRun controlRun_zero controlRun_add controlRun_one spec)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

-- Two real controls implement node214, with normal exit at positive control3.
def clearTable : List Row := [⟨2,2,3,2⟩,⟨3,0,1,1⟩]

theorem clear_occurrence :
    Occ DagPerm.dagPerm (rows clearTable) 2 (.node 214) 1 (fun _ => 3) :=
  occ_of_occB _ _ _ _ _ _ (by decide)

-- This is an actual occurrence and run, not a conditional theorem with no occurrence.
theorem actual_clear (x : V) :
    ∃ t : V, controlRun clearTable t (liveValue 1 x)=liveValue 3 (lupd x 1 0) := by
  have h := dagPerm_clear214 (controlRun_zero clearTable) (controlRun_add clearTable)
    (controlRun_one clearTable) (spec clearTable) x
  exact h 2 1 (fun _ => 3) clear_occurrence

-- Zero counters are included, and unrelated physical registers survive.
example (x : V) (hx : lreg x 1=0) :
    ∃ t : V, controlRun clearTable t (liveValue 1 x)=liveValue 3 x := by
  simpa only [←hx, lupd_lreg] using actual_clear x

example (x : V) : lreg (lupd x 1 0) 4=lreg x 4 :=
  lreg_lupd_other x 0 1 4 (by decide)

example (rl : List Row) (x : V) :
    IRun DagPerm.dagPerm (rows rl) (controlRun rl) (.node 197) x .normal
      (lupd (lupd x 5 (lreg x 5+lreg x 4)) 4 0) :=
  dagPerm_transfer197 (controlRun_zero rl) (controlRun_add rl) (controlRun_one rl) (spec rl) x

example (rl : List Row) (x : V) :
    IRun DagPerm.dagPerm (rows rl) (controlRun rl) (.node 192) x .normal
      (lupd (lupd (lupd x 6 (lreg x 6+lreg x 3)) 7 (lreg x 7+lreg x 3)) 3 0) :=
  dagPerm_copy192 (controlRun_zero rl) (controlRun_add rl) (controlRun_one rl) (spec rl) x

#print axioms transfer
#print axioms copy2
#print axioms clear
#print axioms dagPerm_transfer197
#print axioms dagPerm_copy192
#print axioms dagPerm_clear214
#print axioms clear_occurrence
#print axioms actual_clear
end SetTheory.BusyBeaver.ZFC.ArithmeticDagLoopsChecks
