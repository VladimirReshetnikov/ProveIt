import BusyBeaver.ZFC.SitePrefix246

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath SymbolicPrefix246 SitePrefix246

#print axioms SitePrefix246.checkSite_length
#print axioms SitePrefix246.checkSite_operation
#print axioms SitePrefix246.runTo_sound
#print axioms SitePrefix246.runHalt_sound
#print axioms SitePrefix246.check_inc
#print axioms SitePrefix246.check_decnz
#print axioms SitePrefix246.check_break
#print axioms SitePrefix246.check_continue
#print axioms SitePrefix246.check_halt
#print axioms SitePrefix246.check_inc_bound
#print axioms SitePrefix246.check_decnz_bound
#print axioms SitePrefix246.check_node_false

example : SitePrefix246.dispatch = dispatchPrefix246 := rfl

example (Q : List Bool) (e : Edge) (h : checkSite Q e = true) :
    Q.length ≤ minDistance := checkSite_length Q e h

example (Q : List Bool) (e : Edge) (h : checkSite Q e = true) :
    checkOperation Q e = true := checkSite_operation Q e h

example (br : Branch) (Q : List Bool) (wanted : SConfig)
    (he : runTo br Q wanted = true)
    (n : Nat) (vs : List Nat) (hv : Valid br vs) (c : Config 246)
    (hc : Represents n vs (start Q) c) :
    ∃ k : Nat, 0 < k ∧ Represents n vs wanted (machinePrefix246.runFrom c k) :=
  runTo_sound br Q wanted he n vs hv c hc

example (Q : List Bool) (he : runHalt Q = true)
    (n : Nat) (vs : List Nat) (hv : 10 ≤ vs.length) (c : Config 246)
    (hc : Represents n vs (start Q) c) :
    ∃ k : Nat, 0 < k ∧ (machinePrefix246.runFrom c k).state = none :=
  runHalt_sound Q he n vs hv c hc

example (Q : List Bool) (r : Nat) (hr : r < 9)
    (h : checkSite Q (.inc r) = true) :
    runTo none Q (target (incPath Q) (allOnes Q) 0
      (.plain (.increment (physical r hr)))) = true := check_inc Q r hr h

example (Q : List Bool) (r : Nat) (hr : r < 9)
    (h : checkSite Q (.decnz r) = true) :
    runTo (some (physical r hr, true)) Q
      (target (breakPath 1 Q) (allOnes (stripPath false 1 Q)) 0 (.plain .unchanged)) = true ∧
    runTo (some (physical r hr, false)) Q
      (target (incPath Q) (allOnes Q) 1 (.plain (.decrement (physical r hr)))) = true :=
  check_decnz Q r hr h

example (Q : List Bool) (k : Nat) (h : checkSite Q (.brk k) = true) :
    runTo none Q (target (breakPath k Q) (allOnes (stripPath false k Q)) 0
      (.plain .unchanged)) = true := check_break Q k h

example (Q : List Bool) (k : Nat) (h : checkSite Q (.cont k) = true) :
    runTo none Q (target (continuePath k Q) false 0 (.plain .unchanged)) = true :=
  check_continue Q k h

example (Q : List Bool) (h : checkSite Q .halt = true) :
    runHalt Q = true := check_halt Q h

example (Q : List Bool) (r : Nat) (h : checkSite Q (.inc r) = true) :
    r < 9 := check_inc_bound Q r h

example (Q : List Bool) (r : Nat) (h : checkSite Q (.decnz r) = true) :
    r < 9 := check_decnz_bound Q r h

example (Q : List Bool) (r : Nat) :
    checkSite Q (.node r) = false := check_node_false Q r
