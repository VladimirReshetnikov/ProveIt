import BusyBeaver.ZFC.SymbolicRotation244
import BusyBeaver.ZFC.Permutation252Frame

/-!
Fresh Rotation244 port of SiteRouting245.
Only machine/state/module identities and the explicit selector literals change.
All-register, complete-tape and positive-clock hypotheses are retained.
The original Mira-Cult/Jeff Ketchersid/Andrew James Wade and ProveIt lineage
remains attributed. This source is uncompiled at emission; coverage, exact
blank initialization and the final Combined243 calibration remain separate.
-/

namespace SetTheory.BusyBeaver.ZFC.SiteRotation244

open RegisterPath SymbolicRotation244

def dispatch : Fin 244 := dispatchRotation244
def minDistance : Nat := 64
def fuel : Nat := 4000

def physical (r : Nat) (hr : r < 9) : Reg :=
  ⟨Permutation252Frame.physOf r, Permutation252Frame.physOf_lt ⟨r, hr⟩⟩

def allOnes (P : List Bool) : Bool := P.all id

def start (Q : List Bool) : SConfig :=
  ⟨some dispatch, false, [.bit true],
    Q.map Segment.bit ++
      [.run false 1 (minDistance - Q.length), .bit true, .box (.plain .unchanged)]⟩

def target (P : List Bool) (overflow : Bool) (extra : Nat) (x : Box) : SConfig :=
  ⟨some dispatch, false, [.bit true],
    P.map Segment.bit ++
      [.run false 1 (minDistance + (if overflow then 1 else 0) + extra - P.length),
       .bit true, .box x]⟩

def runTo (br : Branch) (Q : List Bool) (wanted : SConfig) : Bool :=
  verifies fuel br (start Q) wanted

def runHalt (Q : List Bool) : Bool := verifiesHalt fuel none (start Q)

def checkOperation (Q : List Bool) : Edge → Bool
  | .node _ => false
  | .inc r =>
      if hr : r < 9 then
        runTo none Q (target (incPath Q) (allOnes Q) 0 (.plain (.increment (physical r hr))))
      else false
  | .decnz r =>
      if hr : r < 9 then
        runTo (some (physical r hr, true)) Q
          (target (breakPath 1 Q) (allOnes (stripPath false 1 Q)) 0 (.plain .unchanged)) &&
        runTo (some (physical r hr, false)) Q
          (target (incPath Q) (allOnes Q) 1 (.plain (.decrement (physical r hr))))
      else false
  | .brk k =>
      runTo none Q (target (breakPath k Q) (allOnes (stripPath false k Q)) 0 (.plain .unchanged))
  | .cont k => runTo none Q (target (continuePath k Q) false 0 (.plain .unchanged))
  | .halt => runHalt Q

/-- The distance bound is checked together with the operation, so every
accepted leaf can be used with the same arbitrary nonnegative gap parameter. -/
def checkSite (Q : List Bool) (e : Edge) : Bool :=
  decide (Q.length ≤ minDistance) && checkOperation Q e

theorem checkSite_length (Q : List Bool) (e : Edge) (h : checkSite Q e = true) :
    Q.length ≤ minDistance := by
  exact of_decide_eq_true (Bool.and_eq_true_iff.mp h).1

theorem checkSite_operation (Q : List Bool) (e : Edge) (h : checkSite Q e = true) :
    checkOperation Q e = true := (Bool.and_eq_true_iff.mp h).2

theorem runTo_sound (br : Branch) (Q : List Bool) (wanted : SConfig)
    (he : runTo br Q wanted = true)
    (n : Nat) (vs : List Nat) (hv : Valid br vs) (c : Config 244)
    (hc : Represents n vs (start Q) c) :
    ∃ k : Nat, 0 < k ∧ Represents n vs wanted (machineRotation244.runFrom c k) :=
  verifies_sound fuel br (start Q) wanted he n vs hv c hc

theorem runHalt_sound (Q : List Bool) (he : runHalt Q = true)
    (n : Nat) (vs : List Nat) (hv : 10 ≤ vs.length) (c : Config 244)
    (hc : Represents n vs (start Q) c) :
    ∃ k : Nat, 0 < k ∧ (machineRotation244.runFrom c k).state = none :=
  verifiesHalt_sound fuel none (start Q) he n vs ⟨hv, trivial⟩ c hc

theorem check_inc (Q : List Bool) (r : Nat) (hr : r < 9)
    (h : checkSite Q (.inc r) = true) :
    runTo none Q (target (incPath Q) (allOnes Q) 0 (.plain (.increment (physical r hr)))) = true := by
  simpa only [checkOperation, dif_pos hr] using checkSite_operation Q (.inc r) h

theorem check_decnz (Q : List Bool) (r : Nat) (hr : r < 9)
    (h : checkSite Q (.decnz r) = true) :
    runTo (some (physical r hr, true)) Q
      (target (breakPath 1 Q) (allOnes (stripPath false 1 Q)) 0 (.plain .unchanged)) = true ∧
    runTo (some (physical r hr, false)) Q
      (target (incPath Q) (allOnes Q) 1 (.plain (.decrement (physical r hr)))) = true := by
  have hc := checkSite_operation Q (.decnz r) h
  simpa only [checkOperation, dif_pos hr, Bool.and_eq_true_iff] using hc

theorem check_break (Q : List Bool) (k : Nat)
    (h : checkSite Q (.brk k) = true) :
    runTo none Q (target (breakPath k Q) (allOnes (stripPath false k Q)) 0 (.plain .unchanged)) = true :=
  checkSite_operation Q (.brk k) h

theorem check_continue (Q : List Bool) (k : Nat)
    (h : checkSite Q (.cont k) = true) :
    runTo none Q (target (continuePath k Q) false 0 (.plain .unchanged)) = true :=
  checkSite_operation Q (.cont k) h

theorem check_halt (Q : List Bool) (h : checkSite Q .halt = true) : runHalt Q = true :=
  checkSite_operation Q .halt h

theorem check_inc_bound (Q : List Bool) (r : Nat) (h : checkSite Q (.inc r) = true) :
    r < 9 := by
  have hc := checkSite_operation Q (.inc r) h
  by_cases hr : r < 9
  · exact hr
  · simp only [checkOperation, dif_neg hr, Bool.false_eq_true] at hc

theorem check_decnz_bound (Q : List Bool) (r : Nat) (h : checkSite Q (.decnz r) = true) :
    r < 9 := by
  have hc := checkSite_operation Q (.decnz r) h
  by_cases hr : r < 9
  · exact hr
  · simp only [checkOperation, dif_neg hr, Bool.false_eq_true] at hc

theorem check_node_false (Q : List Bool) (r : Nat) : checkSite Q (.node r) = false := by
  simp only [checkSite, checkOperation, Bool.and_false]

end SetTheory.BusyBeaver.ZFC.SiteRotation244
