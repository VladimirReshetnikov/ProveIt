import BusyBeaver.ZFC.ArithmeticSiteBootPerm252
import BusyBeaver.ZFC.SitesPerm252
import BusyBeaver.ZFC.RuntimeInstancePerm252

set_option autoImplicit false

/-!
Compose one actual accepted instruction with the next actual decoder entry.
Only the finite native program/path syntax is external. Register values, spare
count, gap and positive binary clocks are arbitrary IΣ1-model elements.
The complete target tape is rebased, rather than merely relabeled as a start.
Existing checked actual-site coverage is imported; no guard/chunk is replayed.
No represented variable-PC run or global runtime theorem is asserted.
Mira-Cult, Jeff and Wade retain their machine/framework attribution.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticDispatchRebasePerm252
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticMachineUniformScansPerm252 ArithmeticMachineRunFromPerm252
open ArithmeticSymbolicTapePerm252 ArithmeticSymbolicBoxesPerm252
open ArithmeticSymbolicExecutionPerm252 (value)
open ArithmeticSitePerm252 (startValue)
open ArithmeticSiteBootPerm252 (bitsPrefix bitsPrefix_append bitPrefix_replicate)
open RegisterPath RegisterPathClean
open SymbolicPerm252 (Effect Segment)
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The entire finite PC region up to the common marker/header budget. -/
def padded (P : List Bool) (budget : Nat) : List Bool :=
  P ++ List.replicate (budget-P.length) false

def budget (overflow : Bool) : Nat := 40+overflow.toNat

noncomputable def effectValues (values : List V) : Effect → List V
  | .unchanged => values
  | .increment r => writeAt values r.val (values.getD r.val 0+1)
  | .decrement r => writeAt values r.val (values.getD r.val 0-1)

def effectCount (count : V) : Effect → V
  | .decrement _ => count+1
  | _ => count

lemma effectValues_length (values : List V) (effect : Effect) :
    (effectValues values effect).length = values.length := by
  cases effect <;> simp only [effectValues,writeAt_length]

lemma box_rebase (values : List V) (count suffix : V) (effect : Effect) :
    boxPrefix values count (.plain effect) suffix =
      boxPrefix (effectValues values effect) (effectCount count effect) (.plain .unchanged) suffix := by
  cases effect <;> rfl

lemma map_bits_prefix (gap : V) (boxes : SymbolicPerm252.Box → V → V)
    (P : List Bool) (suffix : V) :
    tapePrefix gap boxes (P.map Segment.bit) suffix = bitsPrefix P suffix := by
  induction P with
  | nil => rfl
  | cons b P ih => simp only [List.map_cons,tapePrefix,segmentPrefix,bitsPrefix,ih]

lemma target_format (values : List V) (count gap : V) (P : List Bool)
    (overflow : Bool) (effect : Effect) :
    value values count gap (SitePerm252.target P overflow (.plain effect)) =
      frame 95 1 (bitsPrefix P
        (bitPrefix false (gap+((budget overflow-P.length : Nat) : V))
          (2*boxPrefix values count (.plain effect) 0+1))) := by
  have hb : (if overflow then 1 else 0 : Nat) = overflow.toNat := by cases overflow <;> rfl
  simp only [value,configValue,SitePerm252.target,SitePerm252.dispatch,
    SitePerm252.minDistance,ArithmeticMachinePerm252.stateCode,if_false,
    tapePrefix_append,map_bits_prefix,tapePrefix,segmentPrefix,affine,digit,
    Bool.false_eq_true,if_true,mul_zero,zero_add,Nat.cast_ofNat,Nat.cast_one,
    one_mul,show (94+1 : Nat) = 95 by rfl,hb,budget]

lemma start_format (values : List V) (count gap : V) (P : List Bool) :
    startValue values count gap P =
      frame 95 1 (bitsPrefix P
        (bitPrefix false (gap+((40-P.length : Nat) : V))
          (2*boxPrefix values count (.plain .unchanged) 0+1))) := by
  have hs : SitePerm252.start P = SitePerm252.target P false (.plain .unchanged) := rfl
  rw [startValue,hs,target_format]
  rfl

lemma padded_prefix (P : List Bool) (N : Nat) (gap header : V) :
    bitsPrefix P (bitPrefix false (gap+((N-P.length : Nat) : V)) header) =
      bitsPrefix (padded P N) (bitPrefix false gap header) := by
  rw [padded,bitsPrefix_append,←bitPrefix_replicate,←bitPrefix_add]
  rw [add_comm gap]

/-- Exact arithmetic tape equality: the finite padding premise accounts for
shorter or zero-extended next consumed paths, and no tape cell is discarded. -/
theorem target_rebase (values : List V) (count gap : V) (P Q : List Bool)
    (overflow : Bool) (effect : Effect) (hQ : Q.length ≤ 40)
    (hp : padded P (budget overflow) = padded Q (budget overflow)) :
    value values count gap (SitePerm252.target P overflow (.plain effect)) =
      startValue (effectValues values effect) (effectCount count effect)
        (gap+digit overflow) Q := by
  have hn : budget overflow-Q.length = overflow.toNat+(40-Q.length) := by
    cases overflow <;> simp only [budget,Bool.toNat_false,Bool.toNat_true] <;> omega
  have hc : (overflow.toNat : V) = digit (V := V) overflow := by
    cases overflow <;> simp [digit]
  rw [target_format,box_rebase,padded_prefix,hp,←padded_prefix,start_format,hn,
    Nat.cast_add,hc]
  congr 3
  ring

/-- Actual closed coverage supplies the next accepted consumed path. Clean
converts its zero suffix into the literal finite padding equality. -/
theorem next_checked (P : List Bool) (overflow : Bool) (hP : P.length ≤ 40)
    (hc : Clean Prog254.program P) :
    ∃ e d, walk Prog254.program (Prog254.program.nnodes+1) Prog254.program.root P 0 = some (e,d) ∧
      follow Prog254.program (.node Prog254.program.root) (consume P d) = some e ∧
      SitePerm252.checkSite (consume P d) e = true ∧
      (consume P d).length ≤ 40 ∧
      padded P (budget overflow) = padded (consume P d) (budget overflow) := by
  obtain ⟨e,d,hw⟩ := SitesPerm252.actual_walk_exists P
  have hs := SitesPerm252.actual_walk_checked P e d hw
  have hd : d ≤ 40 := by
    simpa only [consume_length,SitePerm252.minDistance] using SitePerm252.checkSite_length _ _ hs
  have hb : 40 ≤ budget overflow := by cases overflow <;> simp [budget]
  have hz := RuntimeInstancePerm252.clean_suffix Prog254.program P e d hc hw
  have hp := gap_consume P (budget overflow-P.length) d (by omega) hz
  have hh : P.length+(budget overflow-P.length) = budget overflow := by omega
  refine ⟨e,d,hw,walk_follow_consume Prog254.program P e d hw,
    hs,by simpa only [consume_length] using hd,?_⟩
  simpa only [padded,consume_length,hh] using hp

/-- A positive checked binary segment reaches a newly accepted canonical
entry, including all internal register and spare updates. -/
theorem reenter (Q P : List Bool) (overflow : Bool) (effect : Effect)
    (values : List V) (count gap time : V)
    (ht : 0 < time)
    (hr : runFrom time (startValue values count gap Q) =
      value values count gap (SitePerm252.target P overflow (.plain effect)))
    (hP : P.length ≤ 40) (hc : Clean Prog254.program P) :
    ∃ e d, SitePerm252.checkSite (consume P d) e = true ∧
      follow Prog254.program (.node Prog254.program.root) (consume P d) = some e ∧
      0 < time ∧ runFrom time (startValue values count gap Q) =
        startValue (effectValues values effect) (effectCount count effect)
          (gap+digit overflow) (consume P d) := by
  obtain ⟨e,d,_,hf,hs,hd,hpad⟩ := next_checked P overflow hP hc
  exact ⟨e,d,hs,hf,ht,hr.trans (target_rebase values count gap P (consume P d) overflow effect hd hpad)⟩

/-- The outgoing clean predicate depends only on the actual branch's path.
A dummy external Nat register file selects that branch without constraining
or converting any arithmetic-model register value. -/
lemma clean_inc (Q : List Bool) (r : Nat)
    (hf : follow Prog254.program (.node Prog254.program.root) Q = some (.inc r)) :
    Clean Prog254.program (incPath Q) :=
  execute_clean Prog254.program (.inc r) Q (fun _ => 0)
    ⟨incPath Q,update (fun _ => 0) r 1⟩ hf rfl

lemma clean_decnz_zero (Q : List Bool) (r : Nat)
    (hf : follow Prog254.program (.node Prog254.program.root) Q = some (.decnz r)) :
    Clean Prog254.program (breakPath 1 Q) :=
  execute_clean Prog254.program (.decnz r) Q (fun _ => 0)
    ⟨breakPath 1 Q,fun _ => 0⟩ hf rfl

lemma clean_decnz_positive (Q : List Bool) (r : Nat)
    (hf : follow Prog254.program (.node Prog254.program.root) Q = some (.decnz r)) :
    Clean Prog254.program (incPath Q) :=
  execute_clean Prog254.program (.decnz r) Q (fun _ => 1)
    ⟨incPath Q,update (fun _ => 1) r 0⟩ hf rfl

/-- One actual increment, including decoder recanonicalization and next-site
acceptance. The physical selector is the existing literal permutation. -/
theorem increment_reenters (Q : List Bool) (r : Nat) (hr : r < 9)
    (hf : follow Prog254.program (.node Prog254.program.root) Q = some (.inc r))
    (hs : SitePerm252.checkSite Q (.inc r) = true)
    (values : List V) (hlen : values.length = 9) (count gap : V) :
    ∃ time : V, 0 < time ∧ ∃ e d,
      SitePerm252.checkSite (consume (incPath Q) d) e = true ∧
      follow Prog254.program (.node Prog254.program.root) (consume (incPath Q) d) = some e ∧
      runFrom time (startValue values count gap Q) =
        startValue (effectValues values (.increment (SitePerm252.physical r hr))) count
          (gap+digit (SitePerm252.allOnes Q)) (consume (incPath Q) d) := by
  obtain ⟨time,ht,hv⟩ := ArithmeticSitePerm252.check_inc Q r hr hs values hlen count gap
  have hQ : Q.length ≤ 40 := SitePerm252.checkSite_length Q (.inc r) hs
  have hP : (incPath Q).length ≤ 40 := by rw [InstructionPerm252.incPath_length]; exact hQ
  obtain ⟨e,d,hc,hf',_,he⟩ := reenter Q (incPath Q) (SitePerm252.allOnes Q)
    (.increment (SitePerm252.physical r hr)) values count gap time ht hv hP (clean_inc Q r hf)
  exact ⟨time,ht,e,d,hc,hf',he⟩

/-- The zero branch has no spare-count increment. -/
theorem zero_reenters (Q : List Bool) (r : Nat) (hr : r < 9)
    (hf : follow Prog254.program (.node Prog254.program.root) Q = some (.decnz r))
    (hs : SitePerm252.checkSite Q (.decnz r) = true)
    (values : List V) (hlen : values.length = 9)
    (hz : values.getD (SitePerm252.physical r hr).val 0 = 0) (count gap : V) :
    ∃ time : V, 0 < time ∧ ∃ e d,
      SitePerm252.checkSite (consume (breakPath 1 Q) d) e = true ∧
      follow Prog254.program (.node Prog254.program.root) (consume (breakPath 1 Q) d) = some e ∧
      runFrom time (startValue values count gap Q) =
        startValue values count (gap+digit (SitePerm252.allOnes (stripPath false 1 Q)))
          (consume (breakPath 1 Q) d) := by
  obtain ⟨time,ht,hv⟩ := ArithmeticSitePerm252.check_decnz_zero Q r hr hs values hlen hz count gap
  have hQ : Q.length ≤ 40 := SitePerm252.checkSite_length Q (.decnz r) hs
  have hP : (breakPath 1 Q).length ≤ 40 := le_trans (InstructionPerm252.breakPath_length 1 Q) hQ
  obtain ⟨e,d,hc,hf',_,he⟩ := reenter Q (breakPath 1 Q)
    (SitePerm252.allOnes (stripPath false 1 Q)) .unchanged values count gap time ht hv hP
    (clean_decnz_zero Q r hf)
  exact ⟨time,ht,e,d,hc,hf',he⟩

/-- The positive branch appends exactly one zero spare, then canonicalizes PC. -/
theorem positive_reenters (Q : List Bool) (r : Nat) (hr : r < 9)
    (hf : follow Prog254.program (.node Prog254.program.root) Q = some (.decnz r))
    (hs : SitePerm252.checkSite Q (.decnz r) = true)
    (values : List V) (hlen : values.length = 9)
    (hn : values.getD (SitePerm252.physical r hr).val 0 ≠ 0) (count gap : V) :
    ∃ time : V, 0 < time ∧ ∃ e d,
      SitePerm252.checkSite (consume (incPath Q) d) e = true ∧
      follow Prog254.program (.node Prog254.program.root) (consume (incPath Q) d) = some e ∧
      runFrom time (startValue values count gap Q) =
        startValue (effectValues values (.decrement (SitePerm252.physical r hr))) (count+1)
          (gap+digit (SitePerm252.allOnes Q)) (consume (incPath Q) d) := by
  obtain ⟨time,ht,hv⟩ := ArithmeticSitePerm252.check_decnz_positive Q r hr hs values hlen hn count gap
  have hQ : Q.length ≤ 40 := SitePerm252.checkSite_length Q (.decnz r) hs
  have hP : (incPath Q).length ≤ 40 := by rw [InstructionPerm252.incPath_length]; exact hQ
  obtain ⟨e,d,hc,hf',_,he⟩ := reenter Q (incPath Q) (SitePerm252.allOnes Q)
    (.decrement (SitePerm252.physical r hr)) values count gap time ht hv hP
    (clean_decnz_positive Q r hf)
  exact ⟨time,ht,e,d,hc,hf',he⟩

lemma clean_break (Q : List Bool) (k : Nat)
    (hf : follow Prog254.program (.node Prog254.program.root) Q = some (.brk k)) :
    Clean Prog254.program (breakPath k Q) :=
  execute_clean Prog254.program (.brk k) Q (fun _ => 0)
    ⟨breakPath k Q,fun _ => 0⟩ hf rfl

lemma clean_continue (Q : List Bool) (k : Nat)
    (hf : follow Prog254.program (.node Prog254.program.root) Q = some (.cont k)) :
    Clean Prog254.program (continuePath k Q) :=
  execute_clean Prog254.program (.cont k) Q (fun _ => 0)
    ⟨continuePath k Q,fun _ => 0⟩ hf rfl

/-- Actual break consumes the appropriate suffix and preserves every register. -/
theorem break_reenters (Q : List Bool) (k : Nat)
    (hf : follow Prog254.program (.node Prog254.program.root) Q = some (.brk k))
    (hs : SitePerm252.checkSite Q (.brk k) = true)
    (values : List V) (hlen : values.length = 9) (count gap : V) :
    ∃ time : V, 0 < time ∧ ∃ e d,
      SitePerm252.checkSite (consume (breakPath k Q) d) e = true ∧
      follow Prog254.program (.node Prog254.program.root) (consume (breakPath k Q) d) = some e ∧
      runFrom time (startValue values count gap Q) =
        startValue values count (gap+digit (SitePerm252.allOnes (stripPath false k Q)))
          (consume (breakPath k Q) d) := by
  obtain ⟨time,ht,hv⟩ := ArithmeticSitePerm252.check_break Q k hs values hlen count gap
  have hQ : Q.length ≤ 40 := SitePerm252.checkSite_length Q (.brk k) hs
  have hP : (breakPath k Q).length ≤ 40 := le_trans (InstructionPerm252.breakPath_length k Q) hQ
  obtain ⟨e,d,hc,hf',_,he⟩ := reenter Q (breakPath k Q)
    (SitePerm252.allOnes (stripPath false k Q)) .unchanged values count gap time ht hv hP
    (clean_break Q k hf)
  exact ⟨time,ht,e,d,hc,hf',he⟩

/-- Continue never overflows, so the canonical gap is unchanged. -/
theorem continue_reenters (Q : List Bool) (k : Nat)
    (hf : follow Prog254.program (.node Prog254.program.root) Q = some (.cont k))
    (hs : SitePerm252.checkSite Q (.cont k) = true)
    (values : List V) (hlen : values.length = 9) (count gap : V) :
    ∃ time : V, 0 < time ∧ ∃ e d,
      SitePerm252.checkSite (consume (continuePath k Q) d) e = true ∧
      follow Prog254.program (.node Prog254.program.root) (consume (continuePath k Q) d) = some e ∧
      runFrom time (startValue values count gap Q) =
        startValue values count gap (consume (continuePath k Q) d) := by
  obtain ⟨time,ht,hv⟩ := ArithmeticSitePerm252.check_continue Q k hs values hlen count gap
  have hQ : Q.length ≤ 40 := SitePerm252.checkSite_length Q (.cont k) hs
  have hP : (continuePath k Q).length ≤ 40 :=
    le_trans (InstructionPerm252.continuePath_length k Q) hQ
  obtain ⟨e,d,hc,hf',_,he⟩ := reenter Q (continuePath k Q) false .unchanged values count gap time ht hv hP
    (clean_continue Q k hf)
  refine ⟨time,ht,e,d,hc,hf',?_⟩
  simpa only [effectValues,effectCount,digit,Bool.false_eq_true,if_false,add_zero] using he

/-- Initial blank PC bits may already be consumed by the literal decoder.
Recanonicalization changes no numeric configuration and consumes no clock. -/
theorem initial_entry (values : List V) (count gap : V) :
    ∃ e d, SitePerm252.checkSite (consume [] d) e = true ∧
      follow Prog254.program (.node Prog254.program.root) (consume [] d) = some e ∧
      startValue values count gap [] = startValue values count gap (consume [] d) := by
  obtain ⟨e,d,_,hf,hs,hd,hpad⟩ := next_checked [] false (by simp) (clean_nil Prog254.program)
  have he := target_rebase values count gap [] (consume [] d) false .unchanged hd hpad
  have ht : SitePerm252.target [] false (.plain .unchanged) = SitePerm252.start [] := rfl
  refine ⟨e,d,hs,hf,?_⟩
  simpa only [ht,startValue,effectValues,effectCount,digit,Bool.false_eq_true,if_false,add_zero] using he

/-- The existing exact blank prefix reaches the actual first accepted leaf
at the same clock82552, without replaying the bootstrap or any site check. -/
theorem internal_boot_entry :
    ∃ e d, SitePerm252.checkSite (consume [] d) e = true ∧
      follow Prog254.program (.node Prog254.program.root) (consume [] d) = some e ∧
      ArithmeticMachineRunPerm252.run (82552 : V) =
        startValue (List.replicate 9 (0 : V)) 56 0 (consume [] d) := by
  obtain ⟨e,d,hs,hf,he⟩ := initial_entry (List.replicate 9 (0 : V)) 56 0
  exact ⟨e,d,hs,hf,(ArithmeticSiteBootPerm252.internal_boot_start (V := V)).trans he⟩

end SetTheory.BusyBeaver.ZFC.ArithmeticDispatchRebasePerm252
