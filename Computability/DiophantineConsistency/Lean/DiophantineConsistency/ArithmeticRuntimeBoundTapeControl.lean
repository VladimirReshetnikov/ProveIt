import DiophantineConsistency.ArithmeticRuntimeBoundTapeSymbolic
import DiophantineConsistency.ArithmeticControlFrame215

/-! # Clock-bounded sites and canonical entries of the p215 control table

Bounded twins of `ArithmeticSite215` and the entry lemmas of
`ArithmeticControlFrame215`. Every actual source site runs the certified
symbolic executor for `KSim.FUEL = 4000` abstract steps from a start
configuration of weights `confA = 1`, `confC ≤ 66`, so one register-machine
instruction costs at most

  `siteB gap v k = 4000 * (gap + boxW v k + 4085)`

decimal215 steps, linear in the gap, the register values and the spare count.
`entry_stepB` also records how the entry parameters grow: at most one more
spare, at most two more gap cells, and every register at most one larger.
Proof bodies follow the accepted originals; no existing statement is changed. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
namespace DiophantineConsistency.ArithmeticRuntimeBoundTapeControl
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open RegisterPath RegisterPathClean RMBisim SiteCoverage ControlCatalogue
open ArithmeticCantor ArithmeticControlFile ArithmeticControlTable ArithmeticControl215Table
open ArithmeticMachineTape215 ArithmeticRegisterBoxes215 ArithmeticSymbolicCore215
open ArithmeticRuntimeBoundTape ArithmeticRuntimeBoundTapeBoxes ArithmeticRuntimeBoundTapeSymbolic
open ArithmeticControlFrame215
open ArithmeticSite215 (startValue targetValue checked_inc checked_decnz)
open KRuntimeCore (BoxSt Branch SConf Seg)

theorem wA_bits (Q : List Bool) : wA (Q.map Seg.bit) = 0 := by
  induction Q with
  | nil => rfl
  | cons b Q ih => simp only [List.map_cons, wA_cons, segA, ih]
theorem wC_bits (Q : List Bool) : wC (Q.map Seg.bit) = Q.length := by
  induction Q with
  | nil => rfl
  | cons b Q ih => simp only [List.map_cons, wC_cons, segC, ih, List.length_cons]; omega

theorem start_weights (Q : List Bool) (hQ : Q.length ≤ 64) :
    confA (KSim.start Q) = 1 ∧ confC (KSim.start Q) ≤ 66 := by
  simp only [KSim.start, KSim.D0, confA_mk, confC_mk, wA_cons, wC_cons, wA_append, wC_append,
    wA_nil, wC_nil, segA, segC]
  rw [wA_bits, wC_bits]
  omega

section Internal
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The clock bound of one source site, i.e. of one register-machine instruction. -/
noncomputable def siteB (gap : V) (v : Fin 9 → V) (k : V) : V := 4000*(gap + boxW v k + 4085)

theorem execB_start (gap : V) (v : Fin 9 → V) (k : V) (Q : List Bool) (hQ : Q.length ≤ 64) :
    execB gap v k KSim.FUEL (KSim.start Q) ≤ siteB gap v k := by
  obtain ⟨hA, hC⟩ := start_weights Q hQ
  have hc : ((confC (KSim.start Q) : Nat) : V) ≤ 66 := by
    simpa only [Nat.cast_ofNat] using Nat.mono_cast (α := V) hC
  unfold execB cost siteB
  rw [hA, show KSim.FUEL = 4000 from rfl]
  calc ((4000:Nat):V)*(((1:Nat):V)*gap + ((confC (KSim.start Q) : Nat) : V) + boxW v k + 19 +
          ((4000:Nat):V))
      = 4000*(gap + ((confC (KSim.start Q) : Nat) : V) + boxW v k + 4019) := by push_cast; ring
    _ ≤ 4000*(gap + 66 + boxW v k + 4019) :=
        mul_le_mul_of_nonneg_left (_root_.add_le_add (_root_.add_le_add
          (_root_.add_le_add le_rfl hc) le_rfl) le_rfl) (Arithmetic.zero_le _)
    _ = 4000*(gap + boxW v k + 4085) := by ring

theorem runTo_actualB (gap : V) (v : Fin 9 → V) (k : V) (hk : 0<k)
    {br : Branch} (hv : BranchValid br v) {Q : List Bool} {target : SConf} (hQ : Q.length ≤ 64)
    (h : KSim.runTo KTableCore.tm215 br Q target=true) :
    ReachPosB (startValue gap v k Q) (interpret gap v k target) (siteB gap v k) := by
  unfold KSim.runTo at h
  cases he : KHomeReady.exec KTableCore.tm215 br (fun s => KRuntimeCore.sMatches s target)
      KSim.FUEL (KSim.start Q) false with
  | none => simp only [he,Option.isSome_none,Bool.false_eq_true] at h
  | some s => exact (exec_matches_actualB gap v k hk hv he).mono (execB_start gap v k Q hQ)

theorem runHalt_actualB (gap : V) (v : Fin 9 → V) (k : V) (hk : 0<k)
    {Q : List Bool} (hQ : Q.length ≤ 64) (h : KSim.runHalt KTableCore.tm215 Q=true) :
    ∃ clock : V, 0<clock ∧ clock ≤ siteB gap v k ∧ first (runFrom clock (startValue gap v k Q))=0 := by
  unfold KSim.runHalt at h
  cases he : KHomeReady.exec KTableCore.tm215 none KSim.isHalt KSim.FUEL (KSim.start Q) false with
  | none => simp only [he,Option.isSome_none,Bool.false_eq_true] at h
  | some s =>
    obtain ⟨hh,clock,hc,hcB,hr⟩ := exec_actualB gap v k hk (br:=none) trivial he
    refine ⟨clock,hc,le_trans hcB (execB_start gap v k Q hQ),?_⟩
    rw [startValue,hr]
    exact ArithmeticSite215.halt_interpret gap v k hh

theorem leaf_length {Q : List Bool} {e : Edge} (h : LeafAt KSource215.t215 Q e) : Q.length ≤ 64 := by
  have := ArithmeticSite215.source_length h; omega

theorem source_incB (gap : V) (v : Fin 9 → V) (k : V) (hk : 0<k)
    {Q : List Bool} {r : Nat} (h : LeafAt KSource215.t215 Q (.inc r)) :
    ReachPosB (startValue gap v k Q)
      (targetValue gap v k (incPath Q) (KSim.allOnes Q) (.plain (.inc (KSim.physOf r))))
      (siteB gap v k) :=
  runTo_actualB gap v k hk (br:=none) trivial (leaf_length h)
    (checked_inc (ArithmeticSite215.source_checked h)).2.2
theorem source_decnz_zeroB (gap : V) (v : Fin 9 → V) (k : V) (hk : 0<k)
    {Q : List Bool} {r : Nat} (h : LeafAt KSource215.t215 Q (.decnz r))
    (hz : getValue v (KSim.physOf r)=0) :
    ReachPosB (startValue gap v k Q)
      (targetValue gap v k (breakPath 1 Q) (KSim.allOnes (stripPath false 1 Q)) (.plain .none))
      (siteB gap v k) :=
  runTo_actualB gap v k hk (br:=some (KSim.physOf r,true)) hz (leaf_length h)
    (checked_decnz (ArithmeticSite215.source_checked h)).2.2.1
theorem source_decnz_positiveB (gap : V) (v : Fin 9 → V) (k : V) (hk : 0<k)
    {Q : List Bool} {r : Nat} (h : LeafAt KSource215.t215 Q (.decnz r))
    (hn : getValue v (KSim.physOf r)≠0) :
    ReachPosB (startValue gap v k Q)
      (targetValue gap v k (incPath Q) (KSim.allOnes Q) (.plain (.dec (KSim.physOf r))))
      (siteB gap v k) :=
  runTo_actualB gap v k hk (br:=some (KSim.physOf r,false)) hn (leaf_length h)
    (checked_decnz (ArithmeticSite215.source_checked h)).2.2.2
theorem source_breakB (gap : V) (v : Fin 9 → V) (k : V) (hk : 0<k)
    {Q : List Bool} {j : Nat} (h : LeafAt KSource215.t215 Q (.brk j)) :
    ReachPosB (startValue gap v k Q)
      (targetValue gap v k (breakPath j Q) (KSim.allOnes (stripPath false j Q)) (.plain .none))
      (siteB gap v k) := by
  have hc := ArithmeticSite215.source_checked h
  simp only [KSim.checkEdge,Bool.and_eq_true_iff,decide_eq_true_eq] at hc
  exact runTo_actualB gap v k hk (br:=none) trivial (leaf_length h) hc.2
theorem source_continueB (gap : V) (v : Fin 9 → V) (k : V) (hk : 0<k)
    {Q : List Bool} {j : Nat} (h : LeafAt KSource215.t215 Q (.cont j)) :
    ReachPosB (startValue gap v k Q)
      (targetValue gap v k (continuePath j Q) false (.plain .none)) (siteB gap v k) := by
  have hc := ArithmeticSite215.source_checked h
  simp only [KSim.checkEdge,Bool.and_eq_true_iff,decide_eq_true_eq] at hc
  exact runTo_actualB gap v k hk (br:=none) trivial (leaf_length h) hc.2
theorem source_haltB (gap : V) (v : Fin 9 → V) (k : V) (hk : 0<k)
    {Q : List Bool} (h : LeafAt KSource215.t215 Q .halt) :
    ∃ clock : V, 0<clock ∧ clock ≤ siteB gap v k ∧ first (runFrom clock (startValue gap v k Q))=0 := by
  have hc := ArithmeticSite215.source_checked h
  simp only [KSim.checkEdge,Bool.and_eq_true_iff,decide_eq_true_eq] at hc
  exact runHalt_actualB gap v k hk (leaf_length h) hc.2

/-! ## Canonical entries -/

theorem entry_incB (i : Control) (r : Nat) (he:(source i).2=.inc r) (f k gap : V) (hk:0<k) :
    ReachPosB (entryValue (number i:V) f k gap)
      (entryValue (nextControl i false:V) (write (physical i) (regValue f (physical i)+1) f)
        (k+1) (gap+digit (KSim.allOnes (source i).1))) (siteB gap (regValue f) k) := by
  have hl:LeafAt KSource215.t215 (source i).1 (.inc r) := he ▸ source_leaf i
  obtain ⟨t,ht,htB,hv⟩:=source_incB gap (regValue f) k hk hl
  rw [start_source,physical_inc i r he,ArithmeticSite215.increment_target,←values_write,plain_target] at hv
  have hh:=target_next_entry i false (KSim.allOnes (source i).1) 0
    (write (physical i) (regValue f (physical i)+1) f) (k+1) gap (by rw [he]; intro h; cases h)
  exact ⟨t,ht,htB,hv.trans (by simpa only [he,outgoingPathOf,Nat.cast_zero,add_zero] using hh)⟩
theorem entry_decnz_zeroB (i : Control) (r : Nat) (he:(source i).2=.decnz r) (f k gap : V)
    (hk:0<k) (hz:regValue f (physical i)=0) :
    ReachPosB (entryValue (number i:V) f k gap)
      (entryValue (nextControl i false:V) f k
        (gap+digit (KSim.allOnes (stripPath false 1 (source i).1)))) (siteB gap (regValue f) k) := by
  have hl:LeafAt KSource215.t215 (source i).1 (.decnz r) := he ▸ source_leaf i
  have hz':getValue (regValue f) (KSim.physOf r)=0 := by
    rw [physical_decnz i r he]
    simpa only [getValue,dif_pos (physical i).isLt] using hz
  obtain ⟨t,ht,htB,hv⟩:=source_decnz_zeroB gap (regValue f) k hk hl hz'
  rw [start_source,plain_target] at hv
  have hh:=target_next_entry i false (KSim.allOnes (stripPath false 1 (source i).1)) 0 f k gap
    (by rw [he]; intro h; cases h)
  exact ⟨t,ht,htB,hv.trans (by simpa only [he,outgoingPathOf,Bool.false_eq_true,if_false,
    Nat.cast_zero,add_zero] using hh)⟩
theorem entry_decnz_positiveB (i : Control) (r : Nat) (he:(source i).2=.decnz r) (f k gap : V)
    (hk:0<k) (hn:regValue f (physical i)≠0) :
    ReachPosB (entryValue (number i:V) f k gap)
      (entryValue (nextControl i true:V) (write (physical i) (regValue f (physical i)-1) f)
        k (gap+digit (KSim.allOnes (source i).1)+1)) (siteB gap (regValue f) k) := by
  have hl:LeafAt KSource215.t215 (source i).1 (.decnz r) := he ▸ source_leaf i
  have hn':getValue (regValue f) (KSim.physOf r)≠0 := by
    rw [physical_decnz i r he]
    simpa only [getValue,dif_pos (physical i).isLt] using hn
  obtain ⟨t,ht,htB,hv⟩:=source_decnz_positiveB gap (regValue f) k hk hl hn'
  rw [start_source,physical_decnz i r he,ArithmeticSite215.decrement_target,←values_write] at hv
  have hh:=target_next_entry i true (KSim.allOnes (source i).1) 1
    (write (physical i) (regValue f (physical i)-1) f) k gap (by rw [he]; intro h; cases h)
  refine ⟨t,ht,htB,hv.trans ?_⟩
  simpa only [he,outgoingPathOf,if_true,pathTarget,budget,Nat.cast_one,
    show ∀ b:Bool,(if b then 1 else 0:Nat)=b.toNat by intro b; cases b <;> rfl] using hh
theorem entry_breakB (i : Control) (j : Nat) (he:(source i).2=.brk j) (f k gap : V) (hk:0<k) :
    ReachPosB (entryValue (number i:V) f k gap)
      (entryValue (nextControl i false:V) f k (gap+digit (KSim.allOnes (stripPath false j (source i).1))))
      (siteB gap (regValue f) k) := by
  have hl:LeafAt KSource215.t215 (source i).1 (.brk j) := he ▸ source_leaf i
  obtain ⟨t,ht,htB,hv⟩:=source_breakB gap (regValue f) k hk hl
  rw [start_source,plain_target] at hv
  have hh:=target_next_entry i false (KSim.allOnes (stripPath false j (source i).1)) 0 f k gap
    (by rw [he]; intro h; cases h)
  exact ⟨t,ht,htB,hv.trans (by simpa only [he,outgoingPathOf,Nat.cast_zero,add_zero] using hh)⟩
theorem entry_continueB (i : Control) (j : Nat) (he:(source i).2=.cont j) (f k gap : V) (hk:0<k) :
    ReachPosB (entryValue (number i:V) f k gap) (entryValue (nextControl i false:V) f k gap)
      (siteB gap (regValue f) k) := by
  have hl:LeafAt KSource215.t215 (source i).1 (.cont j) := he ▸ source_leaf i
  obtain ⟨t,ht,htB,hv⟩:=source_continueB gap (regValue f) k hk hl
  rw [start_source,plain_target] at hv
  have hh:=target_next_entry i false false 0 f k gap (by rw [he]; intro h; cases h)
  exact ⟨t,ht,htB,hv.trans (by simpa only [he,outgoingPathOf,digit_false,Nat.cast_zero,add_zero] using hh)⟩

theorem digit_le_one (b : Bool) : digit (V:=V) b ≤ 1 := by cases b <;> simp
theorem gap_digit (gap : V) (b : Bool) : gap+digit b ≤ gap+2 :=
  _root_.add_le_add le_rfl (le_trans (digit_le_one b) one_le_two)
theorem gap_digit_one (gap : V) (b : Bool) : gap+digit b+1 ≤ gap+2 := by
  rw [add_assoc]
  exact _root_.add_le_add le_rfl (le_trans (_root_.add_le_add (digit_le_one b) le_rfl)
    (le_of_eq one_add_one_eq_two))
theorem regs_write_le (f : V) (p : Fin 9) (val : V) (hv : val ≤ regValue f p + 1) (q : Fin 9) :
    regValue (write p val f) q ≤ regValue f q + 1 := by
  by_cases h : p = q
  · subst q; rw [reg_write_same]; exact hv
  · rw [reg_write_other p q val f h]; exact le_self_add

/-- `entry_step` with the site clock bound and the growth of the entry parameters. -/
theorem entry_stepB (i : Control) (f k gap : V) (hk:0<k)
    (hn:stepValue table215 (liveValue (number i:V) f)≠0) :
    ∃ j:Control,∃ f' k' gap':V,0<k' ∧
      stepValue table215 (liveValue (number i:V) f)=liveValue (number j:V) f' ∧
      ReachPosB (entryValue (number i:V) f k gap) (entryValue (number j:V) f' k' gap')
        (siteB gap (regValue f) k) ∧
      k' ≤ k+1 ∧ gap' ≤ gap+2 ∧ ∀ p, regValue f' p ≤ regValue f p + 1 := by
  have finish : ∀ (positive:Bool) (f' k' gap':V), (source i).2≠.halt → 0<k' →
      stepValue table215 (liveValue (number i:V) f)=liveValue (nextControl i positive:V) f' →
      ReachPosB (entryValue (number i:V) f k gap) (entryValue (nextControl i positive:V) f' k' gap')
        (siteB gap (regValue f) k) →
      k' ≤ k+1 → gap' ≤ gap+2 → (∀ p, regValue f' p ≤ regValue f p + 1) →
      ∃ j:Control,∃ f' k' gap':V,0<k' ∧
        stepValue table215 (liveValue (number i:V) f)=liveValue (number j:V) f' ∧
        ReachPosB (entryValue (number i:V) f k gap) (entryValue (number j:V) f' k' gap')
          (siteB gap (regValue f) k) ∧
        k' ≤ k+1 ∧ gap' ≤ gap+2 ∧ ∀ p, regValue f' p ≤ regValue f p + 1 := by
    intro positive f' k' gap' hh hk' hs hr h1 h2 h3
    rw [next_number i positive hh] at hs hr
    exact ⟨_,f',k',gap',hk',hs,hr,h1,h2,h3⟩
  have hf : ∀ p, regValue f p ≤ regValue f p + 1 := fun p => le_self_add
  cases he:(source i).2 with
  | node r => exact False.elim (source_not_node i r he)
  | inc r =>
      exact finish false _ (k+1) _ (by rw [he]; intro h; cases h)
        (lt_of_lt_of_le hk (by simp)) (step_inc i r he f) (entry_incB i r he f k gap hk)
        le_rfl (gap_digit gap _) (regs_write_le f _ _ le_rfl)
  | decnz r =>
      by_cases hz:regValue f (physical i)=0
      · exact finish false f k _ (by rw [he]; intro h; cases h) hk
          (step_decnz_zero i r he f hz) (entry_decnz_zeroB i r he f k gap hk hz)
          le_self_add (gap_digit gap _) hf
      · exact finish true _ k _ (by rw [he]; intro h; cases h) hk
          (step_decnz_positive i r he f hz) (entry_decnz_positiveB i r he f k gap hk hz)
          le_self_add (gap_digit_one gap _) (regs_write_le f _ _ (le_trans tsub_le_self le_self_add))
  | brk j =>
      exact finish false f k _ (by rw [he]; intro h; cases h) hk
        (step_break i j he f) (entry_breakB i j he f k gap hk)
        le_self_add (gap_digit gap _) hf
  | cont j =>
      exact finish false f k gap (by rw [he]; intro h; cases h) hk
        (step_continue i j he f) (entry_continueB i j he f k gap hk)
        le_self_add le_self_add hf
  | halt => exact False.elim (hn (step_halt i he f))

theorem entry_haltB (i : Control) (f k gap : V) (hk:0<k)
    (hz:stepValue table215 (liveValue (number i:V) f)=0) :
    ∃ t:V,0<t ∧ t ≤ siteB gap (regValue f) k ∧ first (runFrom t (entryValue (number i:V) f k gap))=0 := by
  have he:(source i).2=.halt := by
    by_contra hn
    exact step_nonzero i f hn hz
  have hl:LeafAt KSource215.t215 (source i).1 .halt := he ▸ source_leaf i
  simpa only [start_source] using source_haltB gap (regValue f) k hk hl

end Internal
end DiophantineConsistency.ArithmeticRuntimeBoundTapeControl
