import DiophantineConsistency.ArithmeticUnaryRecursion
import DiophantineConsistency.ArithmeticMachineRun215
import BusyBeaver.ZFC.KBoot215
import Foundation.FirstOrder.Arithmetic.Definability.Absoluteness

/-! The actual decimal215 tape evaluator at sparse K labels. The fixed boot
uses the thirteen existing checked chunks; continuation clocks are arbitrary
internal IΣ1 elements. No site-executor or control/tape calibration is assumed. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace DiophantineConsistency.ArithmeticMachineTape215
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticMachinePerm252 ArithmeticMachineGraphPerm252
open ArithmeticMachineStepPerm252 (applyValue genericStepValue)
attribute [local irreducible] DecimalMachine215.machine

/-- Unsupported sparse labels share the absent default; only the live image
and literal terminal230 will be used to identify physical machine states. -/
def decodeSparse (q : Nat) : Option (Fin 215) :=
  (List.finRange 215).find? fun i => decide (DecimalMachine215.sparseExpand i.val=q)

def sparseCode (q : Nat) : Nat := stateCode (decodeSparse q)

theorem decode_expansion : ∀ i : Fin 215,
    decodeSparse (DecimalMachine215.sparseExpand i.val)=some i := by decide +kernel

theorem decode_initial : decodeSparse 0=some 0 := by decide +kernel
theorem decode_dispatch : decodeSparse 84=some 23 := by decide +kernel
theorem decode_terminal : decodeSparse 230=none := by decide +kernel
theorem decode_hole : decodeSparse 79=none := by decide +kernel

theorem sparseCode_initial : sparseCode 0=1 := by rw [sparseCode,decode_initial]; rfl
theorem sparseCode_dispatch : sparseCode 84=24 := by rw [sparseCode,decode_dispatch]; rfl
theorem sparseCode_terminal : sparseCode 230=0 := by rw [sparseCode,decode_terminal]; rfl

theorem expansion_of_decode {q : Nat} {i : Fin 215} (h : decodeSparse q=some i) :
    DecimalMachine215.sparseExpand i.val=q :=
  of_decide_eq_true (List.find?_some (p:=fun j : Fin 215 => decide (DecimalMachine215.sparseExpand j.val=q)) h)

theorem sparseCode_lab (i : Option (Fin 215)) :
    sparseCode (KDenseBridge.lab DecimalMachine215.sparseExpand 230 i)=stateCode i := by
  cases i with
  | none => exact sparseCode_terminal
  | some i => simp only [KDenseBridge.lab,sparseCode,decode_expansion]

private theorem rows_supported : ∀ q : Fin 226, ∀ bit : Bool,
    (KTableCore.tm215 q.val bit).isSome=(decodeSparse q.val).isSome := by decide +kernel

/-- Every successful actual sparse row has a live source, including both
read bits. No claim about arbitrary unsupported sparse labels is needed. -/
theorem actual_row {q q' : Nat} {bit write move : Bool}
    (h : KTableCore.tm215 q bit=some (write,move,q')) :
    ∃ i : Fin 215, decodeSparse q=some i ∧
      (DecimalMachine215.machine.transition i bit).write=write ∧
      decide ((DecimalMachine215.machine.transition i bit).move=.right)=move ∧
      stateCode (DecimalMachine215.machine.transition i bit).next=sparseCode q' := by
  have hq : q<226 := by
    by_contra hn
    have hz : KTableCore.table215[q]?=none := List.getElem?_eq_none (by
      rw [KBoot215.table215_length]; omega)
    simp [KTableCore.tm215,KTableCore.tmOf,hz] at h
  have hs := rows_supported ⟨q,hq⟩ bit
  rw [h] at hs
  cases hd : decodeSparse q with
  | none => simp [hd] at hs
  | some i =>
    have he := expansion_of_decode hd
    have hc := DecimalMachine215.commutes i bit
    rw [he,h] at hc
    have ht := Option.some.inj hc.symm
    refine ⟨i,rfl,congrArg Prod.fst ht,congrArg (fun x => x.2.1) ht,?_⟩
    have htarget : KDenseBridge.lab DecimalMachine215.sparseExpand 230
        (DecimalMachine215.machine.transition i bit).next=q' := congrArg (fun x => x.2.2) ht
    rw [←htarget]
    exact (sparseCode_lab _).symm

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def frameSparse (q : Nat) (left right : V) : V :=
  cantor (sparseCode q : V) (cantor left right)

private lemma lookup_zero (rows : List (Nat×Nat)) (start : Nat) (bit : V) :
    lookupValue rows start 0 bit=0 := by
  induction rows generalizing start with
  | nil => rfl
  | cons row rows ih =>
    have hk : (0:V)≠ORingStructure.numeral (start+1) := by
      rw [numeral_eq_natCast]
      exact ne_of_lt ((Nat.cast_pos (α:=V)).mpr (Nat.succ_pos start))
    simpa only [lookupValue,if_neg hk] using ih (start+1)

theorem step_halted (config : V) (h : first config=0) :
    ArithmeticMachineStep215.stepValue config=config := by
  simp only [ArithmeticMachineStep215.stepValue,genericStepValue,h,
    ArithmeticMachineGraph215.actionLookup,lookup_zero,if_true]

private theorem lookup_cast (q bit : Nat) :
    ArithmeticMachineGraph215.actionLookup (q:V) (bit:V)=
      (ArithmeticMachineGraph215.actionLookup q bit : Nat) := by
  have h := DefinedFunction.shigmaOne_absolute_func V
    (f:=fun v : Fin 2 → Nat => ArithmeticMachineGraph215.actionLookup (v 0) (v 1))
    (f':=fun v : Fin 2 → V => ArithmeticMachineGraph215.actionLookup (v 0) (v 1))
    (φ:=ArithmeticMachineGraph215.actionLookupDef.ofZero 𝚺₁)
    (ArithmeticMachineGraph215.actionLookup_defined (V:=Nat)).of_zero
    (ArithmeticMachineGraph215.actionLookup_defined (V:=V)).of_zero ![q,bit]
  simpa only [Function.comp_apply,Matrix.cons_val_zero,Matrix.cons_val_one] using h.symm

private theorem apply_action (q left right : V) (write move : Bool) :
    applyValue (1+4*q+2*(if move then 1 else 0)+(write.toNat:V)) left right =
      if move then cantor q (cantor (2*left+write.toNat) (right/2))
      else cantor q (cantor (left/2) (left%2+2*(write.toNat+2*(right/2)))) := by
  have even_div (x : V) : (2*x)/2=x := by simp
  have even_mod (x : V) : (2*x)%2=0 := by simp [mul_comm]
  have odd_div (x : V) : (2*x+1)/2=x := div_mul_add' x 2 (by simp)
  have odd_mod (x : V) : (2*x+1)%2=1 := by
    simpa only [mul_comm] using mod_mul_add_of_lt x 2 (by simp : (1:V)<2)
  cases move <;> cases write
  all_goals simp only [Bool.false_eq_true,if_false,if_true,Bool.toNat_false,Bool.toNat_true,
    Nat.cast_zero,Nat.cast_one,mul_zero,mul_one,add_zero]
  · have hp : (1+4*q)-1=4*q := by rw [add_comm]; simp
    have hs : (4*q)/4=q := by simp
    have hh : (4*q)/2=2*q := by rw [show (4*q:V)=2*(2*q) by ring,even_div]
    have hw : (4*q)%2=0 := by rw [show (4*q:V)=2*(2*q) by ring,even_mod]
    simp [applyValue,hp,hs,hh,hw,even_mod]
  · have hp : (1+4*q+1)-1=4*q+1 := by simp; ring
    have hs : (4*q+1)/4=q := div_mul_add' q 4 (by simp)
    have hh : (4*q+1)/2=2*q := by rw [show (4*q+1:V)=2*(2*q)+1 by ring,odd_div]
    have hw : (4*q+1)%2=1 := by rw [show (4*q+1:V)=2*(2*q)+1 by ring,odd_mod]
    simp [applyValue,hp,hs,hh,hw,even_mod]
  · have hp : (1+4*q+2)-1=4*q+2 := by rw [show (1+4*q+2:V)=(4*q+2)+1 by ring]; simp
    have hs : (4*q+2)/4=q := div_mul_add' q 4 (by
      simpa only [Nat.cast_ofNat] using (Nat.cast_lt (α:=V)).mpr (by decide : (2:Nat)<4))
    have hh : (4*q+2)/2=2*q+1 := by rw [show (4*q+2:V)=2*(2*q+1) by ring,even_div]
    have hw : (4*q+2)%2=0 := by rw [show (4*q+2:V)=2*(2*q+1) by ring,even_mod]
    simp [applyValue,hp,hs,hh,hw,odd_mod]
  · have hp : (1+4*q+2+1)-1=4*q+3 := by simp; ring
    have hs : (4*q+3)/4=q := div_mul_add' q 4 (by
      simpa only [Nat.cast_ofNat] using (Nat.cast_lt (α:=V)).mpr (by decide : (3:Nat)<4))
    have hh : (4*q+3)/2=2*q+1 := by rw [show (4*q+3:V)=2*(2*q+1)+1 by ring,odd_div]
    have hw : (4*q+3)%2=1 := by rw [show (4*q+3:V)=2*(2*q+1)+1 by ring,odd_mod]
    simp [applyValue,hp,hs,hh,hw,odd_mod]

/-- Literal sparse rows execute on arbitrary internal tape halves. Entering
terminal230 retains the write and move while its arithmetic state becomes0. -/
theorem sparse_step {q q' : Nat} {bit write move : Bool}
    (h : KTableCore.tm215 q bit=some (write,move,q')) (left right : V)
    (hr : right%2=(bit.toNat:V)) :
    ArithmeticMachineStep215.stepValue (frameSparse q left right)=
      if move then frameSparse q' (2*left+write.toNat) (right/2)
      else frameSparse q' (left/2) (left%2+2*(write.toNat+2*(right/2))) := by
  obtain ⟨i,hi,hw,hm,hn⟩ := actual_row h
  have hc : sparseCode q=i.val+1 := by rw [sparseCode,hi]; rfl
  have hl := lookup_cast (V:=V) (i.val+1) bit.toNat
  rw [ArithmeticMachineGraph215.actionLookup_nat,
      ArithmeticMachineGraph215.literal_lookup_actual] at hl
  have hpos : (actionNumber (DecimalMachine215.machine.transition i bit):V)≠0 := by
    exact ne_of_gt ((Nat.cast_pos (α:=V)).mpr (ArithmeticMachineStepPerm252.actionNumber_positive _))
  have ha : (actionNumber (DecimalMachine215.machine.transition i bit):V)=
      1+4*(sparseCode q':V)+2*(if move then 1 else 0)+(write.toNat:V) := by
    unfold actionNumber
    rw [hn,hw]
    cases hmv : (DecimalMachine215.machine.transition i bit).move <;>
      simp [hmv] at hm <;> subst move <;> simp [Nat.cast_add,Nat.cast_mul]
  simp only [frameSparse,ArithmeticMachineStep215.stepValue,genericStepValue,
    first_cantor,second_cantor,hc,hr,hl,if_neg hpos]
  rw [ha,apply_action]

/-- Fixed graph iterating the already accepted actual decimal step. -/
def zeroDef : 𝚺₁.Semisentence 2 := .mkSigma “out initial. out=initial”
def succDef : 𝚺₁.Semisentence 4 := .mkSigma
  “out previous index initial. !ArithmeticMachineStep215.stepDef out previous”
def blueprint : PR.Blueprint 1 where
  zero := zeroDef
  succ := succDef
noncomputable def construction : PR.Construction V blueprint where
  zero p := p 0
  succ _ _ previous := ArithmeticMachineStep215.stepValue previous
  zero_defined := .mk fun e => by simp [blueprint,zeroDef]
  succ_defined := .mk fun e => by simp [blueprint,succDef]
noncomputable def runFrom (time initial : V) : V := construction.result ![initial] time
def runFromDef : 𝚺₁.Semisentence 3 := blueprint.resultDef
def runFromDeltaDef : 𝚫₁.Semisentence 3 := blueprint.resultDeltaDef
instance runFrom_defined : 𝚺₁-Function₂[V] runFrom via runFromDef :=
  ArithmeticUnaryRecursion.result_defined blueprint construction

instance runFrom_defined_delta : 𝚫₁-Function₂[V] runFrom via runFromDeltaDef :=
  runFrom_defined.graph_delta
instance runFrom_definable : 𝚺₁-Function₂[V] runFrom := runFrom_defined.to_definable

@[simp] theorem runFrom_zero (initial : V) : runFrom 0 initial=initial := by simp [runFrom,construction]
@[simp] theorem runFrom_succ (time initial : V) :
    runFrom (time+1) initial=ArithmeticMachineStep215.stepValue (runFrom time initial) := by
  simp [runFrom,PR.Construction.result_succ,construction]
theorem runFrom_add (s t initial : V) : runFrom (s+t) initial=runFrom t (runFrom s initial) := by
  induction t using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ t ih => rw [←add_assoc,runFrom_succ,runFrom_succ,ih]
theorem runFrom_halted (t initial : V) (h : first initial=0) : runFrom t initial=initial := by
  induction t using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ t ih => rw [runFrom_succ,ih,step_halted initial h]
theorem runFrom_blank (t : V) : runFrom t 1=ArithmeticMachineRun215.run t := by
  induction t using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ t ih => rw [runFrom_succ,ArithmeticMachineRun215.run_succ,ih]
theorem runFrom_total (t initial : V) : ∃! out, runFromDef.val.Evalb ![out,t,initial] := by simp

private theorem frameSparse_nat (q left right : Nat) :
    frameSparse q left right=Code254.P (sparseCode q) (Code254.P left right) := by
  simp only [frameSparse,cantor_nat,natCast_nat]

def encodeList (s : KBoot.LConf) : Nat :=
  Code254.P (sparseCode s.1) (Code254.P (bitsCode s.2.1) (bitsCode s.2.2))

private theorem encodeList_frame (q : Nat) (left right : List Bool) :
    encodeList (q,left,right)=frameSparse q (bitsCode left) (bitsCode right) :=
  (frameSparse_nat _ _ _).symm

theorem lstep_transport {s s' : KBoot.LConf}
    (h : KBoot.lstep KTableCore.tm215 s=some s') :
    ArithmeticMachineStep215.stepValue (encodeList s)=encodeList s' := by
  obtain ⟨q,left,right⟩ := s
  cases ht : KTableCore.tm215 q (right.headD false) with
  | none => simp only [KBoot.lstep,ht] at h; cases h
  | some action =>
    obtain ⟨write,move,q'⟩ := action
    have hs := sparse_step ht (bitsCode left) (bitsCode right) (by
      rw [←numeral_two_eq_two]
      simp only [Nat.numeral_eq,HMod.hMod,natCast_nat]
      rw [ArithmeticHistory254.foundation_rem_nat]
      simpa only [←List.headD_eq_head?_getD,List.headD_eq_getD] using bitsCode_head right)
    cases move <;> simp only [KBoot.lstep,ht,Option.some.injEq] at h <;> subst s'
    all_goals
      rw [←numeral_two_eq_two] at hs
      simp only [Nat.numeral_eq,Bool.false_eq_true,if_false,if_true,natCast_nat,HDiv.hDiv,HMod.hMod] at hs
      simp only [ArithmeticHistory254.foundation_div_nat,ArithmeticHistory254.foundation_rem_nat,
        bitsCode_tail,bitsCode_head] at hs
      simpa only [encodeList_frame,bitsCode,←List.headD_eq_head?_getD,
        List.headD_eq_getD,Nat.add_comm] using hs

theorem lblock_transport (d : Nat) {s s' : KBoot.LConf}
    (h : KBoot.lblock (KBoot.fastOf KBoot215.tt215) d s=some s') :
    runFrom (2^d : Nat) (encodeList s)=encodeList s' := by
  induction d generalizing s s' with
  | zero =>
    have he : KBoot.fastOf KBoot215.tt215=KTableCore.tm215 := funext fun q => funext (KBoot215.fast215 q)
    have hh : KBoot.lstep KTableCore.tm215 s=some s' := by simpa only [KBoot.lblock,he] using h
    change runFrom (0+1:Nat) (encodeList s)=encodeList s'
    rw [runFrom_succ,runFrom_zero]
    exact lstep_transport hh
  | succ d ih =>
    simp only [KBoot.lblock] at h
    cases hs : KBoot.lblock (KBoot.fastOf KBoot215.tt215) d s with
    | none => simp [hs] at h
    | some mid =>
      rw [hs] at h
      rw [Nat.pow_succ,Nat.mul_two,runFrom_add,ih hs]
      exact ih h

/-- Literal full boot code in the accepted decimal state numbering. -/
def bootCode : Nat := Code254.P 24 (Code254.P 1 (bitsCode KBoot215.bootRight))

theorem bootCode_frame : bootCode=cantor 24 (cantor 1 (bitsCode KBoot215.bootRight)) := by
  simp only [bootCode,cantor_nat]

private theorem bitsCode_append_zeros (xs : List Bool) (n : Nat) :
    bitsCode (xs++List.replicate n false)=bitsCode xs := by
  induction xs with
  | nil => induction n <;> simp_all [bitsCode,List.replicate_succ]
  | cons b xs ih => simp only [List.cons_append,bitsCode,ih]

/-- The exact clock is retained from all thirteen already checked blocks. -/
theorem standard_boot : ArithmeticMachineRun215.run (95714:Nat)=bootCode := by
  have h1 := lblock_transport 14 KBoot215.block1
  have h2 := lblock_transport 14 KBoot215.block2
  have h3 := lblock_transport 14 KBoot215.block3
  have h4 := lblock_transport 14 KBoot215.block4
  have h5 := lblock_transport 14 KBoot215.block5
  have h6 := lblock_transport 13 KBoot215.block6
  have h7 := lblock_transport 12 KBoot215.block7
  have h8 := lblock_transport 10 KBoot215.block8
  have h9 := lblock_transport 8 KBoot215.block9
  have h10 := lblock_transport 7 KBoot215.block10
  have h11 := lblock_transport 6 KBoot215.block11
  have h12 := lblock_transport 5 KBoot215.block12
  have h13 := lblock_transport 1 KBoot215.block13
  have hi : encodeList (0,[],[])=1 := by
    simp only [encodeList,sparseCode_initial,bitsCode]
    rfl
  rw [←runFrom_blank,←hi]
  change runFrom ((((((((((((2^14+2^14)+2^14)+2^14)+2^14)+2^13)+2^12)+2^10)+2^8)+2^7)+2^6)+2^5)+2^1)
    (encodeList (0,[],[]))=bootCode
  rw [runFrom_add,runFrom_add,runFrom_add,runFrom_add,runFrom_add,runFrom_add,
    runFrom_add,runFrom_add,runFrom_add,runFrom_add,runFrom_add,runFrom_add,
    h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13]
  simp only [encodeList,KBoot215.cp_state,KBoot215.cp_left,KBoot215.cp_right,
    bitsCode_append_zeros,bitsCode,Bool.toNat_true,mul_zero,add_zero,sparseCode_dispatch,bootCode]

/-- One fixed finite prefix transported through the same Σ1 run graph. -/
theorem internal_boot : ArithmeticMachineRun215.run (95714:V)=(bootCode:V) := by
  have h := DefinedFunction.shigmaOne_absolute_func V
    (ArithmeticMachineRun215.run_defined (V:=Nat))
    (ArithmeticMachineRun215.run_defined (V:=V)) ![95714]
  simpa only [Function.comp_apply,Matrix.cons_val_zero,Nat.cast_ofNat,standard_boot] using h.symm

private theorem cast_cantor (a b : Nat) :
    ((cantor a b:Nat):V)=cantor (a:V) (b:V) := by
  have h := DefinedFunction.shigmaOne_absolute_func V
    (f:=fun v : Fin 2 → Nat => cantor (v 0) (v 1))
    (f':=fun v : Fin 2 → V => cantor (v 0) (v 1))
    (φ:=ArithmeticCantor.pairDef.ofZero 𝚺₁)
    (cantor_defined (V:=Nat)).of_zero (cantor_defined (V:=V)).of_zero ![a,b]
  simpa only [Function.comp_apply,Matrix.cons_val_zero,Matrix.cons_val_one] using h

theorem bootCode_state : first (bootCode:V)=24 := by
  rw [bootCode_frame,cast_cantor,first_cantor]
  simp only [Nat.cast_ofNat]

theorem continuation (t : V) :
    ArithmeticMachineRun215.run (95714+t)=runFrom t (bootCode:V) := by
  rw [←runFrom_blank,runFrom_add,runFrom_blank,internal_boot]

/-- A blank-run halt cannot occur before the live boot. -/
theorem boot_halts_le_of_blank (t : V) (ht : first (ArithmeticMachineRun215.run t) = 0) :
    ∃ t' ≤ t, first (runFrom t' (bootCode : V)) = 0 := by
  have hle : (95714 : V) ≤ t := by
    by_contra hn
    have hlt : t < 95714 := lt_of_not_ge hn
    have he : t + (95714 - t) = 95714 := add_tsub_cancel_of_le (le_of_lt hlt)
    have hz : first (ArithmeticMachineRun215.run (95714 : V)) = 0 := by
      rw [← runFrom_blank, ← he, runFrom_add, runFrom_blank, runFrom_halted _ _ ht]
      exact ht
    rw [internal_boot, bootCode_state] at hz
    exact (by simp : (24 : V) ≠ 0) hz
  refine ⟨t - 95714, tsub_le_self, ?_⟩
  simpa only [← continuation, add_tsub_cancel_of_le hle] using ht


/-- Both witnesses may be nonstandard. A halt before the checked live boot
would persist to code24, so no early-halt case is discarded. -/
theorem blank_halts_iff_boot :
    (∃ t : V, first (ArithmeticMachineRun215.run t)=0) ↔
      ∃ t : V, first (runFrom t (bootCode:V))=0 := by
  constructor
  · rintro ⟨t,ht⟩
    obtain ⟨t', _, h⟩ := boot_halts_le_of_blank t ht
    exact ⟨t', h⟩
  · rintro ⟨t,ht⟩
    exact ⟨95714+t,by rwa [continuation]⟩
end DiophantineConsistency.ArithmeticMachineTape215
