import BusyBeaver.ZFC.ArithmeticCommandTick254

/-!
One fixed Sigma1 step graph of the actual six-register Enum254 scheduler.
The entire live state is 1+P(pl,P(np,working)); zero is absorbing halt.
An exhausted pointer pl=0 starts raw candidate np and increments np. An
active pointer executes raw pl-1 and preserves np. Arbitrary IOpen-model
inputs are covered; no standardness or accepted-proof premise is used.
The Nat adapter matches actual Enum254.enumStep. No internal run, candidate
reach theorem, binary simulation or consistency translation is asserted here.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticEnumeratorStep254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticCommandStep254 ArithmeticCommandWord254
open ArithmeticCommandTick254
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]

noncomputable def liveValue (pl np work : V) : V := cantor pl (cantor np work) + 1

def liveDef : 𝚺₁.Semisentence 4 := .mkSigma
  “out pl np work. ∃ tail, !ArithmeticCantor.pairDef tail np work ∧
    ∃ pair, !ArithmeticCantor.pairDef pair pl tail ∧ out = pair + 1”
instance live_defined : 𝚺₁-Function₃[V] liveValue via liveDef :=
  .mk fun e => by simp [liveDef, liveValue]

noncomputable def pointer (config : V) : V := first (config - 1)
noncomputable def candidate (config : V) : V := first (second (config - 1))
noncomputable def working (config : V) : V := second (second (config - 1))

def pointerDef : 𝚺₁.Semisentence 2 := .mkSigma
  “out config. ∃ pred, !subDef pred config 1 ∧ !firstDef out pred”
def candidateDef : 𝚺₁.Semisentence 2 := .mkSigma
  “out config. ∃ pred, !subDef pred config 1 ∧
    ∃ tail, !secondDef tail pred ∧ !firstDef out tail”
def workingDef : 𝚺₁.Semisentence 2 := .mkSigma
  “out config. ∃ pred, !subDef pred config 1 ∧
    ∃ tail, !secondDef tail pred ∧ !secondDef out tail”
instance pointer_defined : 𝚺₁-Function₁[V] pointer via pointerDef :=
  .mk fun e => by simp [pointerDef, pointer]
instance candidate_defined : 𝚺₁-Function₁[V] candidate via candidateDef :=
  .mk fun e => by simp [candidateDef, candidate]
instance working_defined : 𝚺₁-Function₁[V] working via workingDef :=
  .mk fun e => by simp [workingDef, working]

@[simp] theorem live_ne_zero (pl np w : V) : liveValue pl np w ≠ 0 := by
  simp [liveValue]
@[simp] theorem pointer_live (pl np w : V) : pointer (liveValue pl np w) = pl := by
  simp [pointer, liveValue]
@[simp] theorem candidate_live (pl np w : V) : candidate (liveValue pl np w) = np := by
  simp [candidate, liveValue]
@[simp] theorem working_live (pl np w : V) : working (liveValue pl np w) = w := by
  simp [working, liveValue]

theorem live_decode (config : V) (hc : config ≠ 0) :
    liveValue (pointer config) (candidate config) (working config) = config := by
  simp only [liveValue, pointer, candidate, working, cantor_projections]
  exact ArithmeticCommandTick254.pred_add_one config hc

/-- Execute one raw command while installing the specified next candidate. -/
noncomputable def advanceValue (raw np w : V) : V :=
  if stepValue raw w = 0 then 0
  else liveValue (tailValue raw) np (stepValue raw w - 1)

def advanceDef : 𝚺₁.Semisentence 4 := .mkSigma
  “out raw np w. ∃ result, !ArithmeticCommandStep254.stepDef result raw w ∧
    ((result = 0 ∧ out = 0) ∨
     (result ≠ 0 ∧ ∃ rest, !tailDef rest raw ∧
       ∃ state, !subDef state result 1 ∧ !liveDef out rest np state))”
instance advance_defined : 𝚺₁-Function₃[V] advanceValue via advanceDef := .mk fun e => by
  classical
  by_cases hr : stepValue (e 1) (e 3) = 0 <;>
    simp [advanceDef, advanceValue, hr]

noncomputable def step (config : V) : V :=
  if config = 0 then 0
  else if pointer config = 0 then
    advanceValue (candidate config) (candidate config + 1) (working config)
  else advanceValue (pointer config - 1) (candidate config) (working config)

def stepDef : 𝚺₁.Semisentence 2 := .mkSigma
  “out config. (config = 0 ∧ out = 0) ∨
    (config ≠ 0 ∧ ∃ pl, !pointerDef pl config ∧
      ∃ np, !candidateDef np config ∧ ∃ w, !workingDef w config ∧
      ((pl = 0 ∧ !advanceDef out np (np + 1) w) ∨
       (pl ≠ 0 ∧ ∃ raw, !subDef raw pl 1 ∧ !advanceDef out raw np w)))”
instance step_defined : 𝚺₁-Function₁[V] step via stepDef := .mk fun e => by
  classical
  by_cases hc : e 1 = 0
  · simp [stepDef, step, hc]
  · by_cases hp : pointer (e 1) = 0 <;> simp [stepDef, step, hc, hp]
instance step_defined_delta : 𝚫₁-Function₁[V] step via stepDef.graphDelta :=
  step_defined.graph_delta
instance step_definable : 𝚺₁-Function₁[V] step := step_defined.to_definable

@[simp] theorem step_zero : step (0 : V) = 0 := by simp [step]

theorem step_live (pl np w : V) :
    step (liveValue pl np w) =
      if pl = 0 then advanceValue np (np + 1) w
      else advanceValue (pl - 1) np w := by
  simp [step]

theorem step_boundary (np w : V) :
    step (liveValue 0 np w) = advanceValue np (np + 1) w := by simp [step]

theorem step_active (pl np w : V) (hp : pl ≠ 0) :
    step (liveValue pl np w) = advanceValue (pl - 1) np w := by simp [step, hp]

lemma advance_nonzero (raw np w : V) (h : advanceValue raw np w ≠ 0) :
    advanceValue raw np w = liveValue (tailValue raw) np (stepValue raw w - 1) := by
  by_cases hr : stepValue raw w = 0
  · exact False.elim (h (by simp [advanceValue, hr]))
  · simp [advanceValue, hr]

/-- This decrease applies only inside a candidate; boundaries intentionally
start another candidate rather than becoming absorbing completed states. -/
theorem step_active_decreases (pl np w : V) (hp : pl ≠ 0) :
    step (liveValue pl np w) = 0 ∨
      (pointer (step (liveValue pl np w)) + 1 ≤ pl ∧
       candidate (step (liveValue pl np w)) = np) := by
  rw [step_active pl np w hp]
  by_cases hz : advanceValue (pl - 1) np w = 0
  · exact Or.inl hz
  · right
    rw [advance_nonzero _ _ _ hz, pointer_live, candidate_live]
    constructor
    · calc
        tailValue (pl - 1) + 1 ≤ (pl - 1) + 1 := _root_.add_le_add (tailValue_le _) le_rfl
        _ = pl := ArithmeticCommandTick254.pred_add_one pl hp
    · rfl

theorem step_total (config : V) : ∃! out, stepDef.val.Evalb ![out,config] := by simp

/-! Exact ordinary-Nat comparison with the literal scheduler. -/
private theorem foundation_sub_nat (a b : Nat) : Arithmetic.sub a b = a - b := by
  symm
  apply (Arithmetic.sub_existsUnique a b).unique
  · constructor
    · intro h
      have h' : b = a ∨ b < a := Arithmetic.le_def.mp h
      clear h
      omega
    · intro h
      omega
  · exact Classical.choose!_spec (Arithmetic.sub_existsUnique a b)

private theorem foundation_pred_nat (a : Nat) :
    @HSub.hSub Nat Nat Nat (@instHSub Nat instSub_foundation) a 1 = a - 1 :=
  foundation_sub_nat a 1

noncomputable def encodeSt (s : Enum254.St) : Nat :=
  liveValue s.pl s.np (encodeW (Enum254.toW s))
noncomputable def encodeResult : Option Enum254.St → Nat
  | none => 0
  | some s => encodeSt s

lemma command_unpacked_nat (raw : Nat) (w : Enum254.W) :
    stepValue raw (encodeW w) =
      ArithmeticCommandStep254.encodeResult (Enum254.cstep (EnumStackBarrier254.unpack raw).1 w) := by
  have he := stepValue_pack_nat (EnumStackBarrier254.unpack raw).1
    (EnumStackBarrier254.unpack raw).2 w
  rw [EnumStackBarrier254.pack_unpack] at he
  exact he

lemma advance_execAt_nat (raw np : Nat) (s : Enum254.St) :
    advanceValue raw np (encodeW (Enum254.toW s)) =
      encodeResult (Enum254.execAt raw np s) := by
  rw [advanceValue, command_unpacked_nat, tailValue_nat, EnumStackBarrier254.execAt_unpack]
  cases he : Enum254.cstep (EnumStackBarrier254.unpack raw).1 (Enum254.toW s) with
  | none => simp [ArithmeticCommandStep254.encodeResult, encodeResult]
  | some w =>
    simp only [ArithmeticCommandStep254.encodeResult, foundation_pred_nat,
      Nat.add_sub_cancel, add_eq_zero, _root_.one_ne_zero, and_false, if_false,
      encodeResult, encodeSt, Enum254.toW, CommandWord254.tail]

/-- Every ordinary scheduler state is compared, including dirty registers
and pl=0, np=0 where raw candidate0 is genuinely executed. -/
theorem step_encode_nat (s : Enum254.St) :
    step (encodeSt s) = encodeResult (Enum254.enumStep s) := by
  rw [encodeSt, step_live]
  by_cases hp : s.pl = 0
  · simpa only [Enum254.enumStep, Enum254.fetch, hp, if_true] using
      advance_execAt_nat s.np (s.np + 1) s
  · simpa only [Enum254.enumStep, Enum254.fetch, hp, if_false, foundation_pred_nat] using
      advance_execAt_nat (s.pl - 1) s.np s

end SetTheory.BusyBeaver.ZFC.ArithmeticEnumeratorStep254
