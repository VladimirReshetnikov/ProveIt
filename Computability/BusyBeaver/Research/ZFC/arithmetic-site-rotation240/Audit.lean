import BusyBeaver.ZFC.ArithmeticSiteRotation240

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RegisterPathClean
open ArithmeticCantor (first)
open ArithmeticMachineRunFromRotation240 (runFrom)
open ArithmeticMachineUniformScansPerm252 (digit)
open ArithmeticSymbolicStepRotation240 (value)
open ArithmeticSymbolicBoxesRotation240 (ValidValues)
open ArithmeticSiteValuesRotation240
open ArithmeticControlFile
open ArithmeticControlFrameDataRotation240 (entryValue)
open ArithmeticControlStepRotation240 (physical)
open ControlCatalogueRotation240
open SymbolicRotation240 (Branch SConfig)
open ArithmeticSiteRotation240

#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSiteRotation240.runTo_sound
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSiteRotation240.runHalt_sound
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSiteRotation240.check_inc
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSiteRotation240.check_decnz_zero
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSiteRotation240.check_decnz_positive
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSiteRotation240.check_break
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSiteRotation240.check_continue
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSiteRotation240.check_halt
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSiteRotation240.source_follow
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSiteRotation240.source_inc
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSiteRotation240.source_decnz_zero
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSiteRotation240.source_decnz_positive
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSiteRotation240.source_break
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSiteRotation240.source_continue
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSiteRotation240.source_halt

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (br : Branch) (Q : List Bool) (wanted : SConfig)
    (he : SiteRotation240.runTo br Q wanted = true) (values : List V)
    (hv : ValidValues br values) (extra gap : V) :
    ∃ time : V, 0 < time ∧ runFrom time (startValue values extra gap Q) =
      value values extra gap wanted := runTo_sound br Q wanted he values hv extra gap
example (Q : List Bool) (he : SiteRotation240.runHalt Q = true)
    (values : List V) (hlen : values.length = 9) (extra gap : V) :
    ∃ time : V, 0 < time ∧ first (runFrom time (startValue values extra gap Q)) = 0 :=
  runHalt_sound Q he values hlen extra gap
example (Q : List Bool) (r : Nat) (hr : r < 9)
    (h : SiteRotation240.checkSite Q (.inc r) = true)
    (values : List V) (hlen : values.length = 9) (extra gap : V) :
    ∃ time : V, 0 < time ∧ runFrom time (startValue values extra gap Q) =
      targetValue values extra gap (incPath Q) (SiteRotation240.allOnes Q) 0
        (.increment (SiteRotation240.physical r hr)) := check_inc Q r hr h values hlen extra gap
example (Q : List Bool) (r : Nat) (hr : r < 9)
    (h : SiteRotation240.checkSite Q (.decnz r) = true) (values : List V)
    (hlen : values.length = 9) (hz : values.getD (SiteRotation240.physical r hr).val 0 = 0)
    (extra gap : V) :
    ∃ time : V, 0 < time ∧ runFrom time (startValue values extra gap Q) =
      targetValue values extra gap (breakPath 1 Q)
        (SiteRotation240.allOnes (stripPath false 1 Q)) 0 .unchanged :=
  check_decnz_zero Q r hr h values hlen hz extra gap
example (Q : List Bool) (r : Nat) (hr : r < 9)
    (h : SiteRotation240.checkSite Q (.decnz r) = true) (values : List V)
    (hlen : values.length = 9) (hn : values.getD (SiteRotation240.physical r hr).val 0 ≠ 0)
    (extra gap : V) :
    ∃ time : V, 0 < time ∧ runFrom time (startValue values extra gap Q) =
      targetValue values extra gap (incPath Q) (SiteRotation240.allOnes Q) 1
        (.decrement (SiteRotation240.physical r hr)) :=
  check_decnz_positive Q r hr h values hlen hn extra gap
example (Q : List Bool) (k : Nat) (h : SiteRotation240.checkSite Q (.brk k) = true)
    (values : List V) (hlen : values.length = 9) (extra gap : V) :
    ∃ time : V, 0 < time ∧ runFrom time (startValue values extra gap Q) =
      targetValue values extra gap (breakPath k Q)
        (SiteRotation240.allOnes (stripPath false k Q)) 0 .unchanged :=
  check_break Q k h values hlen extra gap
example (Q : List Bool) (k : Nat) (h : SiteRotation240.checkSite Q (.cont k) = true)
    (values : List V) (hlen : values.length = 9) (extra gap : V) :
    ∃ time : V, 0 < time ∧ runFrom time (startValue values extra gap Q) =
      targetValue values extra gap (continuePath k Q) false 0 .unchanged :=
  check_continue Q k h values hlen extra gap
example (Q : List Bool) (h : SiteRotation240.checkSite Q .halt = true)
    (values : List V) (hlen : values.length = 9) (extra gap : V) :
    ∃ time : V, 0 < time ∧ first (runFrom time (startValue values extra gap Q)) = 0 :=
  check_halt Q h values hlen extra gap
example (i : Control) :
    follow SourceRotation240.program (.node SourceRotation240.program.root)
      (source i).1 = some (source i).2 := source_follow i
example (i : Control) (r : Nat) (he : (source i).2 = .inc r) (file extra gap : V) :
    ∃ time : V, 0 < time ∧ runFrom time (entryValue (number i : V) file extra gap) =
      entryValue (nextControl i false : V)
        (writeValue ((physical i).val : V) (regValue file (physical i)+1) file)
        (extra+1) (gap+digit (SiteRotation240.allOnes (source i).1)) :=
  source_inc i r he file extra gap
example (i : Control) (r : Nat) (he : (source i).2 = .decnz r) (file extra gap : V)
    (hz : regValue file (physical i) = 0) :
    ∃ time : V, 0 < time ∧ runFrom time (entryValue (number i : V) file extra gap) =
      entryValue (nextControl i false : V) file extra
        (gap+digit (SiteRotation240.allOnes (stripPath false 1 (source i).1))) :=
  source_decnz_zero i r he file extra gap hz
example (i : Control) (r : Nat) (he : (source i).2 = .decnz r) (file extra gap : V)
    (hn : regValue file (physical i) ≠ 0) :
    ∃ time : V, 0 < time ∧ runFrom time (entryValue (number i : V) file extra gap) =
      entryValue (nextControl i true : V)
        (writeValue ((physical i).val : V) (regValue file (physical i)-1) file)
        extra (gap+digit (SiteRotation240.allOnes (source i).1)+1) :=
  source_decnz_positive i r he file extra gap hn
example (i : Control) (k : Nat) (he : (source i).2 = .brk k) (file extra gap : V) :
    ∃ time : V, 0 < time ∧ runFrom time (entryValue (number i : V) file extra gap) =
      entryValue (nextControl i false : V) file extra
        (gap+digit (SiteRotation240.allOnes (stripPath false k (source i).1))) :=
  source_break i k he file extra gap
example (i : Control) (k : Nat) (he : (source i).2 = .cont k) (file extra gap : V) :
    ∃ time : V, 0 < time ∧ runFrom time (entryValue (number i : V) file extra gap) =
      entryValue (nextControl i false : V) file extra gap := source_continue i k he file extra gap
example (i : Control) (he : (source i).2 = .halt) (file extra gap : V) :
    ∃ time : V, 0 < time ∧ first (runFrom time
      (entryValue (number i : V) file extra gap)) = 0 := source_halt i he file extra gap
