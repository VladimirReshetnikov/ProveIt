import BusyBeaver.ZFC.ArithmeticControlFrame254

set_option autoImplicit false

/-!
Calibration of the represented finite-control step against its actual source
instruction cases. Concrete binary relation composition follows these exact
column equations; no iterator or internal L2/scheduler equivalence is assumed.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticControlSimulation254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticControlData254 ArithmeticControlStep254
open ArithmeticControlFrame254 FiniteControlTable254 RegisterPath
open ArithmeticMachineRunFromPerm252 ArithmeticMachineUniformScansPerm252
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem next_inc (i : Control) (r : Nat) (he : (source i).2=.inc r) (branch : V) :
    nextValue (number i : V) branch=
      (number (resolveControl (incPath (source i).1)) : V) := by
  rw [next_at]
  simp only [successorNumber,he,outgoingPath,ite_self]

private theorem next_decnz_zero (i : Control) (r : Nat) (he : (source i).2=.decnz r) :
    nextValue (number i : V) 0=
      (number (resolveControl (breakPath 1 (source i).1)) : V) := by
  rw [next_at]
  simp only [if_true,successorNumber,he,outgoingPath,Bool.false_eq_true,if_false]

private theorem next_decnz_positive (i : Control) (r : Nat) (he : (source i).2=.decnz r)
    (branch : V) (hb : branch≠0) : nextValue (number i : V) branch=
      (number (resolveControl (incPath (source i).1)) : V) := by
  rw [next_at,if_neg hb]
  simp only [successorNumber,he,outgoingPath,if_true]

private theorem next_break (i : Control) (k : Nat) (he : (source i).2=.brk k) (branch : V) :
    nextValue (number i : V) branch=
      (number (resolveControl (breakPath k (source i).1)) : V) := by
  rw [next_at]
  simp only [successorNumber,he,outgoingPath,ite_self]

private theorem next_continue (i : Control) (k : Nat) (he : (source i).2=.cont k) (branch : V) :
    nextValue (number i : V) branch=
      (number (resolveControl (continuePath k (source i).1)) : V) := by
  rw [next_at]
  simp only [successorNumber,he,outgoingPath,ite_self]

/-- Exact coded increment, with the old physical selector and no spare update
inside the logical register file. -/
theorem step_inc (i : Control) (r : Nat) (he : (source i).2=.inc r) (file : V) :
    stepValue (liveValue (number i : V) file)=
      liveValue (number (resolveControl (incPath (source i).1)) : V)
        (writeValue ((Permutation252Frame.physOf r : Nat) : V)
          ((physicalValues file).getD (Permutation252Frame.physOf r) 0+1) file) := by
  have hs : SitePerm252.checkSite (source i).1 (.inc r)=true := by
    simpa only [he] using source_accepted i
  have hr := SitePerm252.check_inc_bound _ _ hs
  let p := SitePerm252.physical r hr
  have hop : opcodeValue (number i : V)=1 := by
    simpa [sourceOpcode,he,edgeOpcode] using opcodeValue_at (V := V) i
  have hindex : registerKeyValue (number i : V)=((Permutation252Frame.physOf r : Nat) : V) := by
    simp only [registerKey_at,sourceRegister,he]
  have hselected : selectedValue file ((Permutation252Frame.physOf r : Nat) : V)=
      (physicalValues file).getD (Permutation252Frame.physOf r) 0 :=
    (selected_at file p).trans (physicalValues_getD file p).symm
  rw [step_live,transition_inc _ _ hop,hindex,hselected,next_inc i r he]

theorem step_decnz_zero (i : Control) (r : Nat) (he : (source i).2=.decnz r) (file : V)
    (hz : (physicalValues file).getD (Permutation252Frame.physOf r) 0=0) :
    stepValue (liveValue (number i : V) file)=
      liveValue (number (resolveControl (breakPath 1 (source i).1)) : V) file := by
  have hs : SitePerm252.checkSite (source i).1 (.decnz r)=true := by
    simpa only [he] using source_accepted i
  have hr := SitePerm252.check_decnz_bound _ _ hs
  let p := SitePerm252.physical r hr
  have hop : opcodeValue (number i : V)=2 := by
    simpa [sourceOpcode,he,edgeOpcode] using opcodeValue_at (V := V) i
  have hindex : registerKeyValue (number i : V)=((Permutation252Frame.physOf r : Nat) : V) := by
    simp only [registerKey_at,sourceRegister,he]
  have hselected : selectedValue file ((Permutation252Frame.physOf r : Nat) : V)=
      (physicalValues file).getD (Permutation252Frame.physOf r) 0 :=
    (selected_at file p).trans (physicalValues_getD file p).symm
  have hzero : regValue file p=0 := by
    rw [←physicalValues_getD file p]
    exact hz
  have hw : writeValue ((Permutation252Frame.physOf r : Nat) : V) 0 file=file := by
    have h := write_same file p
    rw [hzero] at h
    exact h
  rw [step_live,transition_decnz _ _ hop,hindex,hselected,hz,next_decnz_zero i r he]
  simpa only [zero_tsub] using congrArg
    (liveValue (number (resolveControl (breakPath 1 (source i).1)) : V)) hw

theorem step_decnz_positive (i : Control) (r : Nat) (he : (source i).2=.decnz r) (file : V)
    (hn : (physicalValues file).getD (Permutation252Frame.physOf r) 0≠0) :
    stepValue (liveValue (number i : V) file)=
      liveValue (number (resolveControl (incPath (source i).1)) : V)
        (writeValue ((Permutation252Frame.physOf r : Nat) : V)
          ((physicalValues file).getD (Permutation252Frame.physOf r) 0-1) file) := by
  have hs : SitePerm252.checkSite (source i).1 (.decnz r)=true := by
    simpa only [he] using source_accepted i
  have hr := SitePerm252.check_decnz_bound _ _ hs
  let p := SitePerm252.physical r hr
  have hop : opcodeValue (number i : V)=2 := by
    simpa [sourceOpcode,he,edgeOpcode] using opcodeValue_at (V := V) i
  have hindex : registerKeyValue (number i : V)=((Permutation252Frame.physOf r : Nat) : V) := by
    simp only [registerKey_at,sourceRegister,he]
  have hselected : selectedValue file ((Permutation252Frame.physOf r : Nat) : V)=
      (physicalValues file).getD (Permutation252Frame.physOf r) 0 :=
    (selected_at file p).trans (physicalValues_getD file p).symm
  rw [step_live,transition_decnz _ _ hop,hindex,hselected,next_decnz_positive i r he _ hn]

theorem step_break (i : Control) (k : Nat) (he : (source i).2=.brk k) (file : V) :
    stepValue (liveValue (number i : V) file)=
      liveValue (number (resolveControl (breakPath k (source i).1)) : V) file := by
  have hop : opcodeValue (number i : V)=3 := by
    simpa [sourceOpcode,he,edgeOpcode] using opcodeValue_at (V := V) i
  rw [step_live,transition_noop _ _ hop,next_break i k he]

theorem step_continue (i : Control) (k : Nat) (he : (source i).2=.cont k) (file : V) :
    stepValue (liveValue (number i : V) file)=
      liveValue (number (resolveControl (continuePath k (source i).1)) : V) file := by
  have hop : opcodeValue (number i : V)=3 := by
    simpa [sourceOpcode,he,edgeOpcode] using opcodeValue_at (V := V) i
  rw [step_live,transition_noop _ _ hop,next_continue i k he]

theorem step_halt (i : Control) (he : (source i).2=.halt) (file : V) :
    stepValue (liveValue (number i : V) file)=0 := by
  have hop : opcodeValue (number i : V)=4 := by
    simpa [sourceOpcode,he,edgeOpcode] using opcodeValue_at (V := V) i
  rw [step_live,transition_halt _ _ hop]

/-- Every numbered live control, including halt, is a valid related entry. -/
theorem related_entry (i : Control) (file count gap : V) :
    Related (liveValue (number i : V) file) (entryValue (number i : V) file count gap) := by
  refine ⟨live_ne_zero _ _,?_,count,gap,?_⟩
  · rw [control_live]
    exact (opcodeValue_nonzero_iff _).mpr ⟨i,rfl⟩
  · simp only [control_live,fileCode_live]


theorem step_nonzero (i : Control) (file : V) (hh : (source i).2≠.halt) :
    stepValue (liveValue (number i : V) file)≠0 := by
  cases he : (source i).2 with
  | node r => exact False.elim (source_not_node i r he)
  | inc r => rw [step_inc i r he]; exact live_ne_zero _ _
  | decnz r =>
      by_cases hz : (physicalValues file).getD (Permutation252Frame.physOf r) 0=0
      · rw [step_decnz_zero i r he file hz]; exact live_ne_zero _ _
      · rw [step_decnz_positive i r he file hz]; exact live_ne_zero _ _
  | brk k => rw [step_break i k he]; exact live_ne_zero _ _
  | cont k => rw [step_continue i k he]; exact live_ne_zero _ _
  | halt => exact False.elim (hh he)

/-- Concrete simulation of each live coded step by a positive actual binary
clock. Validity of the next numbered control comes from the resolver's Fin6460
range, not an unproved invariant or a bounded arithmetic-register hypothesis. -/
theorem related_step (logical binary : V) (h : Related logical binary)
    (hn : stepValue logical≠0) :
    ∃ time : V, 0<time ∧ Related (stepValue logical) (runFrom time binary) := by
  obtain ⟨hl,hop,count,gap,hb⟩ := h
  obtain ⟨i,hq⟩ := (opcodeValue_nonzero_iff (controlValue logical)).mp hop
  let file := fileCodeValue logical
  have heql : logical=liveValue (number i : V) file := by
    simpa only [hq] using (live_decode logical hl).symm
  have hb' : binary=entryValue (number i : V) file count gap := by
    simpa only [hq] using hb
  cases he : (source i).2 with
  | node r => exact False.elim (source_not_node i r he)
  | inc r =>
      obtain ⟨time,ht,hr⟩ := source_inc i r he file count gap
      refine ⟨time,ht,?_⟩
      rw [heql,step_inc i r he,hb',hr]
      exact related_entry _ _ _ _
  | decnz r =>
      by_cases hz : (physicalValues file).getD (Permutation252Frame.physOf r) 0=0
      · obtain ⟨time,ht,hr⟩ := source_decnz_zero i r he file count gap hz
        refine ⟨time,ht,?_⟩
        rw [heql,step_decnz_zero i r he file hz,hb',hr]
        exact related_entry _ _ _ _
      · obtain ⟨time,ht,hr⟩ := source_decnz_positive i r he file count gap hz
        refine ⟨time,ht,?_⟩
        rw [heql,step_decnz_positive i r he file hz,hb',hr]
        exact related_entry _ _ _ _
  | brk k =>
      obtain ⟨time,ht,hr⟩ := source_break i k he file count gap
      refine ⟨time,ht,?_⟩
      rw [heql,step_break i k he,hb',hr]
      exact related_entry _ _ _ _
  | cont k =>
      obtain ⟨time,ht,hr⟩ := source_continue i k he file count gap
      refine ⟨time,ht,?_⟩
      rw [heql,step_continue i k he,hb',hr]
      exact related_entry _ _ _ _
  | halt => exact False.elim (hn (by rw [heql,step_halt i he]))

/-- A coded halt from a valid related entry is the actual halt opcode; the
invalid-control default cannot enter this conclusion. The final binary action
is exactly the one retained by the existing source_halt site proof. -/
theorem related_halt (logical binary : V) (h : Related logical binary)
    (hz : stepValue logical=0) :
    ∃ time : V, 0<time ∧ first (runFrom time binary)=0 := by
  obtain ⟨hl,hop,count,gap,hb⟩ := h
  obtain ⟨i,hq⟩ := (opcodeValue_nonzero_iff (controlValue logical)).mp hop
  let file := fileCodeValue logical
  have heql : logical=liveValue (number i : V) file := by
    simpa only [hq] using (live_decode logical hl).symm
  have hb' : binary=entryValue (number i : V) file count gap := by
    simpa only [hq] using hb
  have hh : (source i).2=.halt := by
    by_contra hnot
    apply step_nonzero i file hnot
    rw [←heql]
    exact hz
  obtain ⟨time,ht,hr⟩ := source_halt i hh file count gap
  exact ⟨time,ht,by simpa only [hb'] using hr⟩

end SetTheory.BusyBeaver.ZFC.ArithmeticControlSimulation254
