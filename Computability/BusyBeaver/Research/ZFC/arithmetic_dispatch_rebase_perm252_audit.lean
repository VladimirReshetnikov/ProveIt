import BusyBeaver.ZFC.ArithmeticDispatchRebasePerm252
set_option autoImplicit false
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC
open ArithmeticMachineUniformScansPerm252 ArithmeticMachineRunFromPerm252
open ArithmeticSymbolicTapePerm252 ArithmeticSymbolicBoxesPerm252
open ArithmeticSymbolicExecutionPerm252 (value)
open ArithmeticSitePerm252 (startValue)
open ArithmeticSiteBootPerm252 (bitsPrefix bitsPrefix_append bitPrefix_replicate)
open ArithmeticDispatchRebasePerm252 RegisterPath RegisterPathClean
open SymbolicPerm252 (Effect Segment)
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticDispatchRebasePerm252.effectValues_length
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticDispatchRebasePerm252.box_rebase
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticDispatchRebasePerm252.map_bits_prefix
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticDispatchRebasePerm252.target_format
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticDispatchRebasePerm252.start_format
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticDispatchRebasePerm252.padded_prefix
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticDispatchRebasePerm252.target_rebase
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticDispatchRebasePerm252.next_checked
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticDispatchRebasePerm252.reenter
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticDispatchRebasePerm252.increment_reenters
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticDispatchRebasePerm252.zero_reenters
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticDispatchRebasePerm252.positive_reenters
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticDispatchRebasePerm252.break_reenters
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticDispatchRebasePerm252.continue_reenters
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticDispatchRebasePerm252.initial_entry
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticDispatchRebasePerm252.internal_boot_entry
section
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example (values : List V) (effect : Effect) :
    (effectValues values effect).length = values.length := by
  exact effectValues_length values effect
example (values : List V) (count suffix : V) (effect : Effect) :
    boxPrefix values count (.plain effect) suffix =
      boxPrefix (effectValues values effect) (effectCount count effect) (.plain .unchanged) suffix := by
  exact box_rebase values count suffix effect
example (gap : V) (boxes : SymbolicPerm252.Box → V → V)
    (P : List Bool) (suffix : V) :
    tapePrefix gap boxes (P.map Segment.bit) suffix = bitsPrefix P suffix := by
  exact map_bits_prefix gap boxes P suffix
example (values : List V) (count gap : V) (P : List Bool)
    (overflow : Bool) (effect : Effect) :
    value values count gap (SitePerm252.target P overflow (.plain effect)) =
      frame 95 1 (bitsPrefix P
        (bitPrefix false (gap+((budget overflow-P.length : Nat) : V))
          (2*boxPrefix values count (.plain effect) 0+1))) := by
  exact target_format values count gap P overflow effect
example (values : List V) (count gap : V) (P : List Bool) :
    startValue values count gap P =
      frame 95 1 (bitsPrefix P
        (bitPrefix false (gap+((40-P.length : Nat) : V))
          (2*boxPrefix values count (.plain .unchanged) 0+1))) := by
  exact start_format values count gap P
example (P : List Bool) (N : Nat) (gap header : V) :
    bitsPrefix P (bitPrefix false (gap+((N-P.length : Nat) : V)) header) =
      bitsPrefix (padded P N) (bitPrefix false gap header) := by
  exact padded_prefix P N gap header
example (values : List V) (count gap : V) (P Q : List Bool)
    (overflow : Bool) (effect : Effect) (hQ : Q.length ≤ 40)
    (hp : padded P (budget overflow) = padded Q (budget overflow)) :
    value values count gap (SitePerm252.target P overflow (.plain effect)) =
      startValue (effectValues values effect) (effectCount count effect)
        (gap+digit overflow) Q := by
  exact target_rebase values count gap P Q overflow effect hQ hp
example (P : List Bool) (overflow : Bool) (hP : P.length ≤ 40)
    (hc : Clean Prog254.program P) :
    ∃ e d, walk Prog254.program (Prog254.program.nnodes+1) Prog254.program.root P 0 = some (e,d) ∧
      follow Prog254.program (.node Prog254.program.root) (consume P d) = some e ∧
      SitePerm252.checkSite (consume P d) e = true ∧
      (consume P d).length ≤ 40 ∧
      padded P (budget overflow) = padded (consume P d) (budget overflow) := by
  exact next_checked P overflow hP hc
example (Q P : List Bool) (overflow : Bool) (effect : Effect)
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
  exact reenter Q P overflow effect values count gap time ht hr hP hc
example (Q : List Bool) (r : Nat) (hr : r < 9)
    (hf : follow Prog254.program (.node Prog254.program.root) Q = some (.inc r))
    (hs : SitePerm252.checkSite Q (.inc r) = true)
    (values : List V) (hlen : values.length = 9) (count gap : V) :
    ∃ time : V, 0 < time ∧ ∃ e d,
      SitePerm252.checkSite (consume (incPath Q) d) e = true ∧
      follow Prog254.program (.node Prog254.program.root) (consume (incPath Q) d) = some e ∧
      runFrom time (startValue values count gap Q) =
        startValue (effectValues values (.increment (SitePerm252.physical r hr))) count
          (gap+digit (SitePerm252.allOnes Q)) (consume (incPath Q) d) := by
  exact increment_reenters Q r hr hf hs values hlen count gap
example (Q : List Bool) (r : Nat) (hr : r < 9)
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
  exact zero_reenters Q r hr hf hs values hlen hz count gap
example (Q : List Bool) (r : Nat) (hr : r < 9)
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
  exact positive_reenters Q r hr hf hs values hlen hn count gap
example (Q : List Bool) (k : Nat)
    (hf : follow Prog254.program (.node Prog254.program.root) Q = some (.brk k))
    (hs : SitePerm252.checkSite Q (.brk k) = true)
    (values : List V) (hlen : values.length = 9) (count gap : V) :
    ∃ time : V, 0 < time ∧ ∃ e d,
      SitePerm252.checkSite (consume (breakPath k Q) d) e = true ∧
      follow Prog254.program (.node Prog254.program.root) (consume (breakPath k Q) d) = some e ∧
      runFrom time (startValue values count gap Q) =
        startValue values count (gap+digit (SitePerm252.allOnes (stripPath false k Q)))
          (consume (breakPath k Q) d) := by
  exact break_reenters Q k hf hs values hlen count gap
example (Q : List Bool) (k : Nat)
    (hf : follow Prog254.program (.node Prog254.program.root) Q = some (.cont k))
    (hs : SitePerm252.checkSite Q (.cont k) = true)
    (values : List V) (hlen : values.length = 9) (count gap : V) :
    ∃ time : V, 0 < time ∧ ∃ e d,
      SitePerm252.checkSite (consume (continuePath k Q) d) e = true ∧
      follow Prog254.program (.node Prog254.program.root) (consume (continuePath k Q) d) = some e ∧
      runFrom time (startValue values count gap Q) =
        startValue values count gap (consume (continuePath k Q) d) := by
  exact continue_reenters Q k hf hs values hlen count gap
example (values : List V) (count gap : V) (P Q : List Bool)
    (hQ : Q.length ≤ 40) (hp : padded P (budget false) = padded Q (budget false)) :
    value values count gap (SitePerm252.target P false (.plain .unchanged)) =
      startValue values count gap Q := by
  simpa only [effectValues,effectCount,digit,Bool.false_eq_true,if_false,add_zero] using
    target_rebase values count gap P Q false .unchanged hQ hp
example (values : List V) (count gap : V) (P Q : List Bool) (r : SymbolicPerm252.Reg)
    (hQ : Q.length ≤ 40) (hp : padded P (budget true) = padded Q (budget true)) :
    value values count gap (SitePerm252.target P true (.plain (.decrement r))) =
      startValue (effectValues values (.decrement r)) (count+1) (gap+1) Q := by
  simpa only [effectCount,digit,if_true] using
    target_rebase values count gap P Q true (.decrement r) hQ hp
example (values : List V) (count gap : V) :
    ∃ e d, SitePerm252.checkSite (consume [] d) e = true ∧
      follow Prog254.program (.node Prog254.program.root) (consume [] d) = some e ∧
      startValue values count gap [] = startValue values count gap (consume [] d) :=
  initial_entry values count gap
example : ∃ e d, SitePerm252.checkSite (consume [] d) e = true ∧
    follow Prog254.program (.node Prog254.program.root) (consume [] d) = some e ∧
    ArithmeticMachineRunPerm252.run (82552 : V) =
      startValue (List.replicate 9 (0 : V)) 56 0 (consume [] d) := internal_boot_entry

end
