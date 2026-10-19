import BusyBeaver.ZFC.ArithmeticSymbolicStepRotation240

set_option autoImplicit false

/-!
Exact erasure and all-model arithmetic soundness for successful executions of
SymbolicRotation240. The standard finite syntax/fuel and target predicate are
external; register values, extra spares, gap and composed clocks are internal.
The four BoxRuntime fields are explicit hypotheses, not discharged here. The
actual checker and its moved flag are used unchanged, and target normalization
is justified by the checked whole-tape numeric interpretation.

The proof follows ArithmeticSymbolicExecutionPerm252 with current240 states,
positive-decrement tape shift, and explicit box obligations. No first-exit,
internal-variable checker graph, whole machine simulation or PA endpoint claim.
Mira-Cult, Jeff Ketchersid, Andrew James Wade and ProveIt retain attribution.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicExecutionRotation240
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticMachineUniformScansPerm252
open ArithmeticMachineRunFromRotation240
open ArithmeticSymbolicTapeRotation240
open ArithmeticSymbolicBoxesRotation240 (boxPrefix ValidValues)
open ArithmeticSymbolicStepRotation240
open SymbolicRotation240 (Branch Reg Box Effect Segment SConfig)

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Move equality-indexed casts from function results into their proof
arguments. Erasing a proof record then removes those arguments entirely. -/
private theorem rec_apply {A : Sort*} {a b : A} (h : a = b)
    {P : A → Sort*} {C : Sort*} (f : P a → C) (p : P b) :
    (h ▸ f) p = f (h.symm ▸ p) := by
  cases h
  rfl

private theorem map_option_cases {A B C : Type*} (erase : B → C)
    (x : Option A) (f : x = none → Option B) (g : ∀ a, x = some a → Option B) :
    (Option.rec (motive := fun y => x = y → Option B) f g x rfl).map erase =
      Option.rec (motive := fun y => x = y → Option C)
        (fun h => (f h).map erase) (fun a h => (g a h).map erase) x rfl := by
  cases x <;> rfl

private theorem map_move_cases {B C : Type*} (erase : B → C)
    (x : Move) (f : x = .left → Option B) (g : x = .right → Option B) :
    (Move.rec (motive := fun y => x = y → Option B) f g x rfl).map erase =
      Move.rec (motive := fun y => x = y → Option C)
        (fun h => (f h).map erase) (fun h => (g h).map erase) x rfl := by
  cases x <;> rfl

private theorem boxChecked_erasure (runtime : BoxRuntime (V := V)) (br : Branch) (q : Fin 240) (x : Box) (l : List Segment) :
    (boxChecked (V := V) runtime br q x l).map (fun out => (out.target,out.moved)) =
      (SymbolicRotation240.boxChecked br q x l).map (fun out => (out.target,out.moved)) := by
  cases x with
  | plain effect =>
    cases effect with
    | unchanged =>
      dsimp only [boxChecked,SymbolicRotation240.boxChecked]
      simp only [map_option_cases,rec_apply]
      rfl
    | increment r => rfl
    | decrement r => rfl
  | marked r =>
    by_cases hi : q = Rotation240Boxes.seek
    · subst q
      rfl
    · by_cases hd : q = Rotation240Boxes.carry
      · subst q
        cases br with
        | none => rfl
        | some pair =>
          rcases pair with ⟨r',zero⟩
          by_cases hr : r = r'
          · subst r'
            cases zero <;>
              dsimp only [boxChecked,SymbolicRotation240.boxChecked] <;>
              simp only [dif_neg hi] <;> rfl
          · simp [boxChecked,SymbolicRotation240.boxChecked,hr]
      · simp [boxChecked,SymbolicRotation240.boxChecked,hi,hd]

/-- Exact computational linkage to the actual checker. Finite control cases
are needed because map does not definitionally distribute over the decision
branches and the two structures have different proof fields. -/
theorem sstep_eq (runtime : BoxRuntime (V := V)) (br : Branch) (s : SConfig) :
    sstep (V := V) runtime br s = SymbolicRotation240.sstep br s := by
  unfold sstep SymbolicRotation240.sstep
  rcases s with ⟨state,onLeft,l,r⟩
  cases state with
  | none => rfl
  | some q =>
    cases onLeft with
    | true =>
      cases l with
      | nil => rfl
      | cons x l =>
        cases x with
        | bit b => rfl
        | box x => rfl
        | run b a c =>
          by_cases hm : (FastTableRotation240.fastMachine.transition q b).move = .left <;>
          by_cases hn : (FastTableRotation240.fastMachine.transition q b).next = some q <;>
          cases c <;> cases a <;>
            simp [checkedStep,SymbolicRotation240.checkedStep,hm,hn,
              peelLeftChecked,SymbolicRotation240.peelLeftChecked]
    | false =>
      cases r with
      | nil => rfl
      | cons x r =>
        cases x with
        | bit b =>
          dsimp only [checkedStep,SymbolicRotation240.checkedStep]
          simp only [map_move_cases,rec_apply]
          rfl
        | run b a c =>
          by_cases hm : (FastTableRotation240.fastMachine.transition q b).move = .right <;>
          by_cases hn : (FastTableRotation240.fastMachine.transition q b).next = some q <;>
          cases c <;> cases a <;>
            simp [checkedStep,SymbolicRotation240.checkedStep,hm,hn,
              peelRightChecked,SymbolicRotation240.peelRightChecked]
        | box x =>
          cases r with
          | cons y r => rfl
          | nil =>
            have hb := boxChecked_erasure (V := V) runtime br q x l
            dsimp only [checkedStep,SymbolicRotation240.checkedStep]
            simp only [map_option_cases,rec_apply]
            cases ho : boxChecked (V := V) runtime br q x l with
            | none =>
              cases hn : SymbolicRotation240.boxChecked br q x l with
              | some out => simp [ho,hn] at hb
              | none =>
                by_cases hm : (FastTableRotation240.fastMachine.transition q false).move = .left <;>
                by_cases hw : (FastTableRotation240.fastMachine.transition q false).write = false <;>
                  simp [hm,hw]
            | some out =>
              cases hn : SymbolicRotation240.boxChecked br q x l with
              | none => simp [ho,hn] at hb
              | some out' =>
                simpa [ho,hn] using hb

theorem sstep_sound (runtime : BoxRuntime (V := V)) (br : Branch) (s t : SConfig) (m : Bool)
    (hs : sstep (V := V) runtime br s = some (t, m)) : StepSound (V := V) br s t m := by
  unfold sstep at hs
  cases hc : checkedStep (V := V) runtime br s with
  | none => simp [hc] at hs
  | some out =>
    simp only [hc, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
    rcases hs with ⟨ht, hm⟩
    simpa only [ht, hm] using out.sound

/-- Every successful step of the ACTUAL native finite checker has its stated
all-model arithmetic meaning. -/
theorem actual_sstep_sound (runtime : BoxRuntime (V := V)) (br : Branch) (s t : SConfig) (m : Bool)
    (hs : SymbolicRotation240.sstep br s = some (t,m)) : StepSound (V := V) br s t m := by
  apply sstep_sound runtime br s t m
  rw [sstep_eq]
  exact hs

/-- External finite-fuel induction composes internal clocks. -/
theorem exec_sound (runtime : BoxRuntime (V := V)) (fuel : Nat) (br : Branch) (target : SConfig → Bool)
    (s t : SConfig) (moved : Bool)
    (he : SymbolicRotation240.exec fuel br target s moved = some t) :
    target t = true ∧ StepSound (V := V) br s t (!moved) := by
  induction fuel generalizing s moved with
  | zero => simp [SymbolicRotation240.exec] at he
  | succ fuel ih =>
    simp only [SymbolicRotation240.exec] at he
    split at he
    next halt =>
      have ht : moved = true ∧ target s = true := Bool.and_eq_true_iff.mp halt
      cases he
      refine ⟨ht.2,?_⟩
      intro values _ extra gap
      exact ⟨0,by simp,by simp [ht.1]⟩
    next _ =>
      cases hs : SymbolicRotation240.sstep br s with
      | none => simp [hs] at he
      | some pair =>
        rcases pair with ⟨u,m⟩
        simp only [hs] at he
        obtain ⟨ht,hh⟩ := ih u (moved || m) he
        refine ⟨ht,?_⟩
        intro values hv extra gap
        obtain ⟨k,hk,hp⟩ := actual_sstep_sound runtime br s u m hs values hv extra gap
        obtain ⟨j,hj,hq⟩ := hh values hv extra gap
        refine ⟨k+j,?_,?_⟩
        · rw [runFrom_add,hk,hj]
        · intro hmove
          cases moved <;> cases m
          · exact lt_of_lt_of_le (hq rfl) (by simp)
          · exact lt_of_lt_of_le (hp rfl) (by simp)
          · simp at hmove
          · simp at hmove

theorem exec_to_matches (runtime : BoxRuntime (V := V)) (fuel : Nat) (br : Branch) (s wanted reached : SConfig)
    (he : SymbolicRotation240.exec fuel br (fun t => SymbolicRotation240.isMatch t wanted)
      s false = some reached)
    (values : List V) (hv : ValidValues br values) (extra gap : V) :
    ∃ time : V, 0 < time ∧ runFrom time (value values extra gap s) =
      value values extra gap wanted := by
  obtain ⟨hm,hs⟩ := exec_sound (V := V) runtime fuel br (fun t => SymbolicRotation240.isMatch t wanted)
    s reached false he
  obtain ⟨time,ht,hp⟩ := hs values hv extra gap
  have hvv : value values extra gap reached = value values extra gap wanted :=
    isMatch_value gap (boxPrefix values extra) reached wanted hm
  exact ⟨time,hp rfl,ht.trans hvv⟩

lemma value_state (values : List V) (extra gap : V) (s : SConfig) :
    first (value values extra gap s) = stateValue s.state := by
  rcases s with ⟨q,onLeft,l,r⟩
  cases onLeft <;> simp [value,configValue,frame,leftFrame,stateValue]

theorem exec_to_halt (runtime : BoxRuntime (V := V)) (fuel : Nat) (br : Branch) (s reached : SConfig)
    (he : SymbolicRotation240.exec fuel br (fun t => decide (t.state = none))
      s false = some reached)
    (values : List V) (hv : ValidValues br values) (extra gap : V) :
    ∃ time : V, 0 < time ∧ first (runFrom time (value values extra gap s)) = 0 := by
  obtain ⟨hm,hs⟩ := exec_sound (V := V) runtime fuel br (fun t => decide (t.state = none)) s reached false he
  obtain ⟨time,ht,hp⟩ := hs values hv extra gap
  have hsnone : reached.state = none := of_decide_eq_true hm
  refine ⟨time,hp rfl,?_⟩
  rw [ht,value_state,hsnone]
  simp [stateValue,ArithmeticMachinePerm252.stateCode]

/-- Existing Boolean certificate acceptance, with no new certificate format. -/
theorem verifies_sound (runtime : BoxRuntime (V := V)) (fuel : Nat) (br : Branch) (s wanted : SConfig)
    (he : SymbolicRotation240.verifies fuel br s wanted = true)
    (values : List V) (hv : ValidValues br values) (extra gap : V) :
    ∃ time : V, 0 < time ∧ runFrom time (value values extra gap s) =
      value values extra gap wanted := by
  cases hx : SymbolicRotation240.exec fuel br (fun t => SymbolicRotation240.isMatch t wanted) s false with
  | none => simp [SymbolicRotation240.verifies,hx] at he
  | some reached => exact exec_to_matches runtime fuel br s wanted reached hx values hv extra gap

theorem verifiesHalt_sound (runtime : BoxRuntime (V := V)) (fuel : Nat) (br : Branch) (s : SConfig)
    (he : SymbolicRotation240.verifiesHalt fuel br s = true)
    (values : List V) (hv : ValidValues br values) (extra gap : V) :
    ∃ time : V, 0 < time ∧ first (runFrom time (value values extra gap s)) = 0 := by
  cases hx : SymbolicRotation240.exec fuel br (fun t => decide (t.state = none)) s false with
  | none => simp [SymbolicRotation240.verifiesHalt,hx] at he
  | some reached => exact exec_to_halt runtime fuel br s reached hx values hv extra gap

end SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicExecutionRotation240
