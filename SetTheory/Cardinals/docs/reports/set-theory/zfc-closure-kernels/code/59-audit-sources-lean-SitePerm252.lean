import BusyBeaver.ZFC.SymbolicPerm252
import BusyBeaver.ZFC.Permutation252Frame

/-!
Per-instruction contracts for the literal permutation252 machine.

The site construction is adapted from Mira-Cult and Jeff's
`ZF/m254/coq/tm/Site.v`, upstream commit
297ab8df7e5de329605c3875b4934643b371a5e3, using Wade's path semantics.
The new physical register assignment is checked in Permutation252Frame.
All binary steps here use the sound Lean symbolic executor for the actual
252-state table; no register-operation hypotheses are supplied.

The extra gap parameter is arbitrary. Overflow moves the PC marker one
cell left, increasing its distance from the register header by one. In
particular incPath retains an all-zero path on overflow, as RegisterPath
requires. This module defines and proves soundness of individual checks;
complete decoder coverage and preservation of the dispatch invariant are
separate obligations.
-/

namespace SetTheory.BusyBeaver.ZFC.SitePerm252

open RegisterPath SymbolicPerm252

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def dispatch : Fin 252 := ⟨94, by decide⟩
def minDistance : Nat := 40
def fuel : Nat := 4000

def physical (r : Nat) (hr : r < 9) : Reg :=
  ⟨Permutation252Frame.physOf r, Permutation252Frame.physOf_lt ⟨r, hr⟩⟩

def allOnes (P : List Bool) : Bool := P.all id

def start (Q : List Bool) : SConfig :=
  ⟨some dispatch, false, [.bit true],
    Q.map Segment.bit ++
      [.run false 1 (minDistance - Q.length), .bit true, .box (.plain .unchanged)]⟩

def target (P : List Bool) (overflow : Bool) (x : Box) : SConfig :=
  ⟨some dispatch, false, [.bit true],
    P.map Segment.bit ++
      [.run false 1 (minDistance + (if overflow then 1 else 0) - P.length),
       .bit true, .box x]⟩

def runTo (br : Branch) (Q : List Bool) (wanted : SConfig) : Bool :=
  verifies fuel br (start Q) wanted

def runHalt (Q : List Bool) : Bool := verifiesHalt fuel none (start Q)

def checkOperation (Q : List Bool) : Edge → Bool
  | .node _ => false
  | .inc r =>
      if hr : r < 9 then
        runTo none Q (target (incPath Q) (allOnes Q) (.plain (.increment (physical r hr))))
      else false
  | .decnz r =>
      if hr : r < 9 then
        runTo (some (physical r hr, true)) Q
          (target (breakPath 1 Q) (allOnes (stripPath false 1 Q)) (.plain .unchanged)) &&
        runTo (some (physical r hr, false)) Q
          (target (incPath Q) (allOnes Q) (.plain (.decrement (physical r hr))))
      else false
  | .brk k =>
      runTo none Q (target (breakPath k Q) (allOnes (stripPath false k Q)) (.plain .unchanged))
  | .cont k => runTo none Q (target (continuePath k Q) false (.plain .unchanged))
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
    (n : Nat) (vs : List Nat) (hv : Valid br vs) (c : Config 252)
    (hc : Represents n vs (start Q) c) :
    ∃ k : Nat, 0 < k ∧ Represents n vs wanted (machinePerm252.runFrom c k) :=
  verifies_sound fuel br (start Q) wanted he n vs hv c hc

theorem runHalt_sound (Q : List Bool) (he : runHalt Q = true)
    (n : Nat) (vs : List Nat) (hv : 9 ≤ vs.length) (c : Config 252)
    (hc : Represents n vs (start Q) c) :
    ∃ k : Nat, 0 < k ∧ (machinePerm252.runFrom c k).state = none :=
  verifiesHalt_sound fuel none (start Q) he n vs ⟨hv, trivial⟩ c hc

theorem check_inc (Q : List Bool) (r : Nat) (hr : r < 9)
    (h : checkSite Q (.inc r) = true) :
    runTo none Q (target (incPath Q) (allOnes Q) (.plain (.increment (physical r hr)))) = true := by
  simpa only [checkOperation, dif_pos hr] using checkSite_operation Q (.inc r) h

theorem check_decnz (Q : List Bool) (r : Nat) (hr : r < 9)
    (h : checkSite Q (.decnz r) = true) :
    runTo (some (physical r hr, true)) Q
      (target (breakPath 1 Q) (allOnes (stripPath false 1 Q)) (.plain .unchanged)) = true ∧
    runTo (some (physical r hr, false)) Q
      (target (incPath Q) (allOnes Q) (.plain (.decrement (physical r hr)))) = true := by
  have hc := checkSite_operation Q (.decnz r) h
  simpa only [checkOperation, dif_pos hr, Bool.and_eq_true_iff] using hc

theorem check_break (Q : List Bool) (k : Nat)
    (h : checkSite Q (.brk k) = true) :
    runTo none Q (target (breakPath k Q) (allOnes (stripPath false k Q)) (.plain .unchanged)) = true :=
  checkSite_operation Q (.brk k) h

theorem check_continue (Q : List Bool) (k : Nat)
    (h : checkSite Q (.cont k) = true) :
    runTo none Q (target (continuePath k Q) false (.plain .unchanged)) = true :=
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

#print axioms runTo_sound
#print axioms runHalt_sound
#print axioms check_decnz

end SetTheory.BusyBeaver.ZFC.SitePerm252
