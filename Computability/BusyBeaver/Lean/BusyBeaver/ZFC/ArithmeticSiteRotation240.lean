import BusyBeaver.ZFC.ArithmeticSiteValuesRotation240
import BusyBeaver.ZFC.ArithmeticSymbolicBoxRuntimeRotation240
import BusyBeaver.ZFC.ArithmeticControlStepRotation240

set_option autoImplicit false

/-!
All-model arithmetic endpoints of the actual Rotation240 site checker.
Every box-runtime premise has been discharged by concrete machine lemmas.
Accepted finite certificates give positive internal execution times and exact
whole-tape endpoints for arbitrary internal files, extra spares and gaps.
Closed coverage supplies acceptance for every actual catalogue source.

The final six source theorems use the same physical selector and nextControl
as ArithmeticControlStepRotation240. Increment adds one spare; positive
decrement adds one padding cell while preserving the spare count. This is
the local dynamic bridge, not first-exit, global internal iteration or a PA
endpoint. Mira-Cult, Jeff Ketchersid, Andrew James Wade and ProveIt retain
the underlying source/program/simulation attribution.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticSiteRotation240

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open RegisterPath RegisterPathClean
open ArithmeticCantor (first)
open ArithmeticMachineRunFromRotation240 (runFrom)
open ArithmeticMachineUniformScansPerm252 (digit)
open ArithmeticSymbolicStepRotation240 (value)
open ArithmeticSymbolicBoxesRotation240 (ValidValues)
open ArithmeticSiteValuesRotation240
open ArithmeticControlFile
open ArithmeticControlFrameDataRotation240 (physicalValues physicalValues_length
  physicalValues_getD entryValue)
open ArithmeticControlStepRotation240 (physical)
open ControlCatalogueRotation240
open SymbolicRotation240 (Branch SConfig)

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem runTo_sound (br : Branch) (Q : List Bool) (wanted : SConfig)
    (he : SiteRotation240.runTo br Q wanted = true)
    (values : List V) (hv : ValidValues br values) (extra gap : V) :
    ∃ time : V, 0 < time ∧ runFrom time (startValue values extra gap Q) =
      value values extra gap wanted :=
  ArithmeticSymbolicBoxRuntimeRotation240.verifies_sound SiteRotation240.fuel br
    (SiteRotation240.start Q) wanted he values hv extra gap

theorem runHalt_sound (Q : List Bool) (he : SiteRotation240.runHalt Q = true)
    (values : List V) (hlen : values.length = 9) (extra gap : V) :
    ∃ time : V, 0 < time ∧ first (runFrom time (startValue values extra gap Q)) = 0 :=
  ArithmeticSymbolicBoxRuntimeRotation240.verifiesHalt_sound SiteRotation240.fuel none
    (SiteRotation240.start Q) he values ⟨hlen,trivial⟩ extra gap

theorem check_inc (Q : List Bool) (r : Nat) (hr : r < 9)
    (h : SiteRotation240.checkSite Q (.inc r) = true)
    (values : List V) (hlen : values.length = 9) (extra gap : V) :
    ∃ time : V, 0 < time ∧ runFrom time (startValue values extra gap Q) =
      targetValue values extra gap (incPath Q) (SiteRotation240.allOnes Q) 0
        (.increment (SiteRotation240.physical r hr)) :=
  runTo_sound none Q _ (SiteRotation240.check_inc Q r hr h) values ⟨hlen,trivial⟩ extra gap

theorem check_decnz_zero (Q : List Bool) (r : Nat) (hr : r < 9)
    (h : SiteRotation240.checkSite Q (.decnz r) = true)
    (values : List V) (hlen : values.length = 9)
    (hz : values.getD (SiteRotation240.physical r hr).val 0 = 0) (extra gap : V) :
    ∃ time : V, 0 < time ∧ runFrom time (startValue values extra gap Q) =
      targetValue values extra gap (breakPath 1 Q)
        (SiteRotation240.allOnes (stripPath false 1 Q)) 0 .unchanged :=
  runTo_sound (some (SiteRotation240.physical r hr,true)) Q _
    (SiteRotation240.check_decnz Q r hr h).1 values ⟨hlen,hz⟩ extra gap

theorem check_decnz_positive (Q : List Bool) (r : Nat) (hr : r < 9)
    (h : SiteRotation240.checkSite Q (.decnz r) = true)
    (values : List V) (hlen : values.length = 9)
    (hn : values.getD (SiteRotation240.physical r hr).val 0 ≠ 0) (extra gap : V) :
    ∃ time : V, 0 < time ∧ runFrom time (startValue values extra gap Q) =
      targetValue values extra gap (incPath Q) (SiteRotation240.allOnes Q) 1
        (.decrement (SiteRotation240.physical r hr)) :=
  runTo_sound (some (SiteRotation240.physical r hr,false)) Q _
    (SiteRotation240.check_decnz Q r hr h).2 values ⟨hlen,hn⟩ extra gap

theorem check_break (Q : List Bool) (k : Nat)
    (h : SiteRotation240.checkSite Q (.brk k) = true)
    (values : List V) (hlen : values.length = 9) (extra gap : V) :
    ∃ time : V, 0 < time ∧ runFrom time (startValue values extra gap Q) =
      targetValue values extra gap (breakPath k Q)
        (SiteRotation240.allOnes (stripPath false k Q)) 0 .unchanged :=
  runTo_sound none Q _ (SiteRotation240.check_break Q k h) values ⟨hlen,trivial⟩ extra gap

theorem check_continue (Q : List Bool) (k : Nat)
    (h : SiteRotation240.checkSite Q (.cont k) = true)
    (values : List V) (hlen : values.length = 9) (extra gap : V) :
    ∃ time : V, 0 < time ∧ runFrom time (startValue values extra gap Q) =
      targetValue values extra gap (continuePath k Q) false 0 .unchanged :=
  runTo_sound none Q _ (SiteRotation240.check_continue Q k h) values ⟨hlen,trivial⟩ extra gap

theorem check_halt (Q : List Bool) (h : SiteRotation240.checkSite Q .halt = true)
    (values : List V) (hlen : values.length = 9) (extra gap : V) :
    ∃ time : V, 0 < time ∧ first (runFrom time (startValue values extra gap Q)) = 0 :=
  runHalt_sound Q (SiteRotation240.check_halt Q h) values hlen extra gap

theorem source_follow (i : Control) :
    follow SourceRotation240.program (.node SourceRotation240.program.root)
      (source i).1 = some (source i).2 := by
  simpa only [consume,List.take_left] using
    walk_follow_consume SourceRotation240.program (source i).1 (source i).2
      (source i).1.length (source_walk i)

private theorem physical_inc (i : Control) (r : Nat) (hr : r < 9)
    (he : (source i).2 = .inc r) : SiteRotation240.physical r hr = physical i := by
  apply Fin.ext
  simp only [SiteRotation240.physical,ArithmeticControlStepRotation240.physical,
    he,ArithmeticControlTable.registerOf]

private theorem physical_decnz (i : Control) (r : Nat) (hr : r < 9)
    (he : (source i).2 = .decnz r) : SiteRotation240.physical r hr = physical i := by
  apply Fin.ext
  simp only [SiteRotation240.physical,ArithmeticControlStepRotation240.physical,
    he,ArithmeticControlTable.registerOf]

/-- Exact physical increment, including its appended value-one spare. -/
theorem source_inc (i : Control) (r : Nat) (he : (source i).2 = .inc r)
    (file extra gap : V) :
    ∃ time : V, 0 < time ∧ runFrom time (entryValue (number i : V) file extra gap) =
      entryValue (nextControl i false : V)
        (writeValue ((physical i).val : V) (regValue file (physical i)+1) file)
        (extra+1) (gap+digit (SiteRotation240.allOnes (source i).1)) := by
  have hs : SiteRotation240.checkSite (source i).1 (.inc r) = true := by
    simpa only [he] using source_accepted i
  have hr := SiteRotation240.check_inc_bound _ _ hs
  have hp := physical_inc i r hr he
  obtain ⟨time,ht,hv⟩ := check_inc _ r hr hs (physicalValues file)
    (physicalValues_length file) extra gap
  rw [start_source] at hv
  have hc := ArithmeticDispatchRebaseRotation240.clean_inc (source i).1 r
    (by simpa only [he] using source_follow i)
  have hh := target_next_entry i false (SiteRotation240.allOnes (source i).1) 0
    file _ extra gap (.increment (SiteRotation240.physical r hr))
    (by rw [hp]; exact effect_increment file (physical i))
    (by rw [he]; intro h; cases h)
    (by simpa only [he,ArithmeticControlTable.outgoingPathOf] using hc)
  refine ⟨time,ht,hv.trans ?_⟩
  simpa only [he,ArithmeticControlTable.outgoingPathOf,effectExtra,Nat.cast_zero,add_zero] using hh

theorem source_decnz_zero (i : Control) (r : Nat) (he : (source i).2 = .decnz r)
    (file extra gap : V) (hz : regValue file (physical i) = 0) :
    ∃ time : V, 0 < time ∧ runFrom time (entryValue (number i : V) file extra gap) =
      entryValue (nextControl i false : V) file extra
        (gap+digit (SiteRotation240.allOnes (stripPath false 1 (source i).1))) := by
  have hs : SiteRotation240.checkSite (source i).1 (.decnz r) = true := by
    simpa only [he] using source_accepted i
  have hr := SiteRotation240.check_decnz_bound _ _ hs
  have hp := physical_decnz i r hr he
  have hz' : (physicalValues file).getD (SiteRotation240.physical r hr).val 0 = 0 := by
    simpa only [physicalValues_getD,hp] using hz
  obtain ⟨time,ht,hv⟩ := check_decnz_zero _ r hr hs (physicalValues file)
    (physicalValues_length file) hz' extra gap
  rw [start_source] at hv
  have hc := ArithmeticDispatchRebaseRotation240.clean_decnz_zero (source i).1 r
    (by simpa only [he] using source_follow i)
  have hh := target_next_entry i false
    (SiteRotation240.allOnes (stripPath false 1 (source i).1)) 0 file file extra gap .unchanged
    rfl (by rw [he]; intro h; cases h)
    (by simpa only [he,ArithmeticControlTable.outgoingPathOf,Bool.false_eq_true,if_false] using hc)
  refine ⟨time,ht,hv.trans ?_⟩
  simpa only [he,ArithmeticControlTable.outgoingPathOf,Bool.false_eq_true,if_false,
    effectExtra,Nat.cast_zero,add_zero] using hh

/-- Positive decrement changes one field and adds padding, never a spare. -/
theorem source_decnz_positive (i : Control) (r : Nat) (he : (source i).2 = .decnz r)
    (file extra gap : V) (hn : regValue file (physical i) ≠ 0) :
    ∃ time : V, 0 < time ∧ runFrom time (entryValue (number i : V) file extra gap) =
      entryValue (nextControl i true : V)
        (writeValue ((physical i).val : V) (regValue file (physical i)-1) file)
        extra (gap+digit (SiteRotation240.allOnes (source i).1)+1) := by
  have hs : SiteRotation240.checkSite (source i).1 (.decnz r) = true := by
    simpa only [he] using source_accepted i
  have hr := SiteRotation240.check_decnz_bound _ _ hs
  have hp := physical_decnz i r hr he
  have hn' : (physicalValues file).getD (SiteRotation240.physical r hr).val 0 ≠ 0 := by
    simpa only [physicalValues_getD,hp] using hn
  obtain ⟨time,ht,hv⟩ := check_decnz_positive _ r hr hs (physicalValues file)
    (physicalValues_length file) hn' extra gap
  rw [start_source] at hv
  have hc := ArithmeticDispatchRebaseRotation240.clean_decnz_positive (source i).1 r
    (by simpa only [he] using source_follow i)
  have hh := target_next_entry i true (SiteRotation240.allOnes (source i).1) 1
    file _ extra gap (.decrement (SiteRotation240.physical r hr))
    (by rw [hp]; exact effect_decrement file (physical i))
    (by rw [he]; intro h; cases h)
    (by simpa only [he,ArithmeticControlTable.outgoingPathOf,if_true] using hc)
  refine ⟨time,ht,hv.trans ?_⟩
  simpa only [he,ArithmeticControlTable.outgoingPathOf,if_true,effectExtra,Nat.cast_one] using hh

theorem source_break (i : Control) (k : Nat) (he : (source i).2 = .brk k)
    (file extra gap : V) :
    ∃ time : V, 0 < time ∧ runFrom time (entryValue (number i : V) file extra gap) =
      entryValue (nextControl i false : V) file extra
        (gap+digit (SiteRotation240.allOnes (stripPath false k (source i).1))) := by
  have hs : SiteRotation240.checkSite (source i).1 (.brk k) = true := by
    simpa only [he] using source_accepted i
  obtain ⟨time,ht,hv⟩ := check_break _ k hs (physicalValues file)
    (physicalValues_length file) extra gap
  rw [start_source] at hv
  have hc := ArithmeticDispatchRebaseRotation240.clean_break (source i).1 k
    (by simpa only [he] using source_follow i)
  have hh := target_next_entry i false
    (SiteRotation240.allOnes (stripPath false k (source i).1)) 0 file file extra gap .unchanged
    rfl (by rw [he]; intro h; cases h)
    (by simpa only [he,ArithmeticControlTable.outgoingPathOf] using hc)
  refine ⟨time,ht,hv.trans ?_⟩
  simpa only [he,ArithmeticControlTable.outgoingPathOf,effectExtra,Nat.cast_zero,add_zero] using hh

theorem source_continue (i : Control) (k : Nat) (he : (source i).2 = .cont k)
    (file extra gap : V) :
    ∃ time : V, 0 < time ∧ runFrom time (entryValue (number i : V) file extra gap) =
      entryValue (nextControl i false : V) file extra gap := by
  have hs : SiteRotation240.checkSite (source i).1 (.cont k) = true := by
    simpa only [he] using source_accepted i
  obtain ⟨time,ht,hv⟩ := check_continue _ k hs (physicalValues file)
    (physicalValues_length file) extra gap
  rw [start_source] at hv
  have hc := ArithmeticDispatchRebaseRotation240.clean_continue (source i).1 k
    (by simpa only [he] using source_follow i)
  have hh := target_next_entry i false false 0 file file extra gap .unchanged
    rfl (by rw [he]; intro h; cases h)
    (by simpa only [he,ArithmeticControlTable.outgoingPathOf] using hc)
  refine ⟨time,ht,hv.trans ?_⟩
  simpa only [he,ArithmeticControlTable.outgoingPathOf,effectExtra,Nat.cast_zero,
    digit,Bool.false_eq_true,if_false,add_zero] using hh

theorem source_halt (i : Control) (he : (source i).2 = .halt) (file extra gap : V) :
    ∃ time : V, 0 < time ∧ first (runFrom time
      (entryValue (number i : V) file extra gap)) = 0 := by
  obtain ⟨time,ht,hv⟩ := check_halt (source i).1
    (by simpa only [he] using source_accepted i)
    (physicalValues file) (physicalValues_length file) extra gap
  rw [start_source] at hv
  exact ⟨time,ht,hv⟩

end SetTheory.BusyBeaver.ZFC.ArithmeticSiteRotation240
