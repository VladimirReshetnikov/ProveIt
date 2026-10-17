import BusyBeaver.ZFC.ArithmeticSitePerm252
set_option autoImplicit false
open SetTheory.BusyBeaver.ZFC
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticMachineRunFromPerm252
open ArithmeticSymbolicBoxesPerm252 (ValidValues)
open ArithmeticSymbolicExecutionPerm252 (value)
open ArithmeticSitePerm252 RegisterPath
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSitePerm252.runTo_sound
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSitePerm252.runHalt_sound
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSitePerm252.accepted_length
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSitePerm252.inc_selector_bound
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSitePerm252.dec_selector_bound
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSitePerm252.check_inc
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSitePerm252.check_decnz_zero
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSitePerm252.check_decnz_positive
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSitePerm252.check_break
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSitePerm252.check_continue
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSitePerm252.check_halt
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSitePerm252.node_rejected

section
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example (br : SymbolicPerm252.Branch) (Q : List Bool) (wanted : SymbolicPerm252.SConfig)
    (he : SitePerm252.runTo br Q wanted = true)
    (values : List V) (hv : ValidValues br values) (count gap : V) :
    ∃ time : V, 0 < time ∧ runFrom time (startValue values count gap Q) = value values count gap wanted :=
  runTo_sound br Q wanted he values hv count gap
example (Q : List Bool) (he : SitePerm252.runHalt Q = true)
    (values : List V) (hlen : values.length = 9) (count gap : V) :
    ∃ time : V, 0 < time ∧ first (runFrom time (startValue values count gap Q)) = 0 :=
  runHalt_sound Q he values hlen count gap
example (Q : List Bool) (edge : Edge) (h : SitePerm252.checkSite Q edge = true) :
    Q.length ≤ SitePerm252.minDistance := accepted_length Q edge h
example (Q : List Bool) (r : Nat) (h : SitePerm252.checkSite Q (.inc r) = true) : r < 9 :=
  inc_selector_bound Q r h
example (Q : List Bool) (r : Nat) (h : SitePerm252.checkSite Q (.decnz r) = true) : r < 9 :=
  dec_selector_bound Q r h
example (Q : List Bool) (r : Nat) (hr : r < 9) (h : SitePerm252.checkSite Q (.inc r) = true)
    (values : List V) (hlen : values.length = 9) (count gap : V) :
    ∃ time : V, 0 < time ∧ runFrom time (startValue values count gap Q) =
      value values count gap (SitePerm252.target (incPath Q) (SitePerm252.allOnes Q)
        (.plain (.increment (SitePerm252.physical r hr)))) :=
  check_inc Q r hr h values hlen count gap
example (Q : List Bool) (r : Nat) (hr : r < 9) (h : SitePerm252.checkSite Q (.decnz r) = true)
    (values : List V) (hlen : values.length = 9)
    (hz : values.getD (SitePerm252.physical r hr).val 0 = 0) (count gap : V) :
    ∃ time : V, 0 < time ∧ runFrom time (startValue values count gap Q) =
      value values count gap (SitePerm252.target (breakPath 1 Q)
        (SitePerm252.allOnes (stripPath false 1 Q)) (.plain .unchanged)) :=
  check_decnz_zero Q r hr h values hlen hz count gap
example (Q : List Bool) (r : Nat) (hr : r < 9) (h : SitePerm252.checkSite Q (.decnz r) = true)
    (values : List V) (hlen : values.length = 9)
    (hn : values.getD (SitePerm252.physical r hr).val 0 ≠ 0) (count gap : V) :
    ∃ time : V, 0 < time ∧ runFrom time (startValue values count gap Q) =
      value values count gap (SitePerm252.target (incPath Q) (SitePerm252.allOnes Q)
        (.plain (.decrement (SitePerm252.physical r hr)))) :=
  check_decnz_positive Q r hr h values hlen hn count gap
example (Q : List Bool) (k : Nat) (h : SitePerm252.checkSite Q (.brk k) = true)
    (values : List V) (hlen : values.length = 9) (count gap : V) :
    ∃ time : V, 0 < time ∧ runFrom time (startValue values count gap Q) =
      value values count gap (SitePerm252.target (breakPath k Q)
        (SitePerm252.allOnes (stripPath false k Q)) (.plain .unchanged)) :=
  check_break Q k h values hlen count gap
example (Q : List Bool) (k : Nat) (h : SitePerm252.checkSite Q (.cont k) = true)
    (values : List V) (hlen : values.length = 9) (count gap : V) :
    ∃ time : V, 0 < time ∧ runFrom time (startValue values count gap Q) =
      value values count gap (SitePerm252.target (continuePath k Q) false (.plain .unchanged)) :=
  check_continue Q k h values hlen count gap
example (Q : List Bool) (h : SitePerm252.checkSite Q .halt = true)
    (values : List V) (hlen : values.length = 9) (count gap : V) :
    ∃ time : V, 0 < time ∧ first (runFrom time (startValue values count gap Q)) = 0 :=
  check_halt Q h values hlen count gap
example (Q : List Bool) (r : Nat) : SitePerm252.checkSite Q (.node r) = false := node_rejected Q r
example (Q : List Bool) (r : Nat) (hr : r < 9) (h : SitePerm252.checkSite Q (.decnz r) = true)
    (values : List V) (hlen : values.length = 9) (count gap : V) :
    ∃ time : V, 0 < time ∧ runFrom time (startValue values count gap Q) =
      value values count gap (if values.getD (SitePerm252.physical r hr).val 0 = 0 then
        SitePerm252.target (breakPath 1 Q) (SitePerm252.allOnes (stripPath false 1 Q)) (.plain .unchanged)
      else SitePerm252.target (incPath Q) (SitePerm252.allOnes Q)
        (.plain (.decrement (SitePerm252.physical r hr)))) := by
  classical
  by_cases hz : values.getD (SitePerm252.physical r hr).val 0 = 0
  · simpa only [if_pos hz] using check_decnz_zero Q r hr h values hlen hz count gap
  · simpa only [if_neg hz] using check_decnz_positive Q r hr h values hlen hz count gap
example (Q : List Bool) (r : Nat) (hr : 9 ≤ r) : SitePerm252.checkSite Q (.inc r) ≠ true := by
  intro h
  exact Nat.not_lt_of_ge hr (inc_selector_bound Q r h)
end
