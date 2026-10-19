import BusyBeaver.ZFC.ArithmeticRegisterCarryRotation240
import BusyBeaver.ZFC.ArithmeticOneRegisterBlocksRotation240

set_option autoImplicit false

/-!
Carry and rollback across an arbitrary internal number of value-one spares,
and across a finite physical register prefix followed by those spares.
The spare count, every register value and both complete numeric tape halves
are arbitrary elements of an IΣ1 model. The finite list is a meta-level list;
the physical-file clients use exactly nine entries. Internally long spares
are handled by arithmetic induction, not by a Nat/list specialization.

This extends the checked Rotation240 carry block and oneBlocks algebra.
It supplies endpoint equalities only: no first-exit, end pulse, selected
register update, dispatch simulation or consistency theorem is asserted.
Mira-Cult, Jeff Ketchersid, Andrew James Wade and ProveIt retain attribution.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticCarryTraversalRotation240

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticMachineUniformScansPerm252
open ArithmeticMachineRunFromRotation240
open ArithmeticRegisterForwardPerm252 (registerBlock reverseBlock)
open ArithmeticRegisterCarryRotation240
open ArithmeticOneRegisterBlocksRotation240

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! Repeated nearest-first carried block 101, encoded by 8*x+5. -/
private def carriedZeroDef : 𝚺₁.Semisentence 2 := .mkSigma
  “out suffix. out = suffix”
private def carriedSuccDef : 𝚺₁.Semisentence 4 := .mkSigma
  “out previous index suffix. out = 8*previous+5”
private def carriedBlueprint : PR.Blueprint 1 where
  zero := carriedZeroDef
  succ := carriedSuccDef

private noncomputable def carriedConstruction : PR.Construction V carriedBlueprint where
  zero parameters := parameters 0
  succ _ _ previous := 8*previous+5
  zero_defined := .mk fun e => by simp [carriedBlueprint, carriedZeroDef]
  succ_defined := .mk fun e => by simp [carriedBlueprint, carriedSuccDef, numeral_eq_natCast]

noncomputable def carriedSpares (count suffix : V) : V :=
  carriedConstruction.result ![suffix] count

def carriedSparesDef : 𝚺₁.Semisentence 3 := carriedBlueprint.resultDef
def carriedSparesDeltaDef : 𝚫₁.Semisentence 3 := carriedBlueprint.resultDeltaDef

instance carriedSpares_defined : 𝚺₁-Function₂[V] carriedSpares via carriedSparesDef :=
  .mk fun e => by
    have he : (fun i : Fin 1 => e i.succ.succ) = ![e 2] := by
      funext i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      rfl
    have h := (carriedConstruction (V := V)).result_defined.df e
    change carriedBlueprint.resultDef.val.Evalb e ↔
      e 0 = carriedConstruction.result (fun i : Fin 1 => e i.succ.succ) (e 1) at h
    rw [he] at h
    change carriedBlueprint.resultDef.val.Evalb e ↔
      e 0 = carriedConstruction.result ![e 2] (e 1)
    exact h

instance carriedSpares_defined_delta :
    𝚫₁-Function₂[V] carriedSpares via carriedSparesDeltaDef :=
  carriedSpares_defined.graph_delta
instance carriedSpares_definable : 𝚺₁-Function₂[V] carriedSpares :=
  carriedSpares_defined.to_definable

@[simp] theorem carriedSpares_zero (suffix : V) : carriedSpares 0 suffix = suffix := by
  simp [carriedSpares, carriedConstruction]

@[simp] theorem carriedSpares_succ (count suffix : V) :
    carriedSpares (count+1) suffix = 8*carriedSpares count suffix+5 := by
  simp [carriedSpares, PR.Construction.result_succ, carriedConstruction]

theorem carriedSpares_one (suffix : V) : carriedSpares 1 suffix = 8*suffix+5 := by
  simpa only [zero_add, carriedSpares_zero] using carriedSpares_succ (0 : V) suffix

theorem carriedSpares_add (leftCount rightCount suffix : V) :
    carriedSpares (leftCount+rightCount) suffix =
      carriedSpares rightCount (carriedSpares leftCount suffix) := by
  induction rightCount using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ rightCount ih =>
    rw [←add_assoc, carriedSpares_succ, carriedSpares_succ, ih]

theorem carriedSpares_push (count suffix : V) :
    carriedSpares count (8*suffix+5) = carriedSpares (count+1) suffix := by
  calc
    carriedSpares count (8*suffix+5) = carriedSpares count (carriedSpares 1 suffix) := by
      rw [carriedSpares_one]
    _ = carriedSpares (1+count) suffix := (carriedSpares_add 1 count suffix).symm
    _ = carriedSpares (count+1) suffix := by rw [add_comm]

private theorem truePrefix_one (suffix : V) :
    bitPrefix true (1 : V) suffix = 2*suffix+1 := by
  simpa only [zero_add, bitPrefix_zero, digit, if_true] using
    bitPrefix_succ true (0 : V) suffix

theorem registerBlock_one (suffix : V) : registerBlock (1 : V) suffix = 8*suffix+6 := by
  rw [registerBlock_expanded, truePrefix_one]
  ring

theorem carryReverseBlock_one (left : V) :
    carryReverseBlock (1 : V) left = 8*left+5 := by
  unfold carryReverseBlock
  rw [truePrefix_one]
  ring

private instance carriedSpares_delta : 𝚫₁-Function₂[V] carriedSpares :=
  carriedSpares_defined_delta.to_definable
private instance oneBlocks_delta : 𝚫₁-Function₂[V] oneBlocks :=
  oneBlocks_defined_delta.to_definable
private instance runFrom_delta : 𝚫₁-Function₂[V] runFrom :=
  runFrom_defined_delta.to_definable
private instance frame_delta : 𝚫₁-Function₃[V] frame :=
  frame_defined.graph_delta.to_definable
private instance leftFrame_delta : 𝚫₁-Function₃[V] leftFrame := by
  unfold leftFrame
  definability

private def CarrySpares (count : V) : Prop := ∀ left right : V,
  runFrom (3*count) (frame (carryState : V) left (oneBlocks count right)) =
    frame (carryState : V) (carriedSpares count left) right
private instance carrySpares_definable : 𝚷₁-Predicate (CarrySpares (V := V)) := by
  unfold CarrySpares
  definability

private def RollbackSpares (count : V) : Prop := ∀ left right : V,
  runFrom (3*count) (leftFrame (rollbackState : V) (carriedSpares count left) right) =
    leftFrame (rollbackState : V) left (oneBlocks count right)
private instance rollbackSpares_definable : 𝚷₁-Predicate (RollbackSpares (V := V)) := by
  unfold RollbackSpares
  definability

/-- All internal spare counts; the induction quantifies both changing tape halves. -/
theorem carry_spares (count left right : V) :
    runFrom (3*count) (frame (carryState : V) left (oneBlocks count right)) =
      frame (carryState : V) (carriedSpares count left) right := by
  have allCounts : ∀ count : V, CarrySpares count := by
    intro count
    induction count using ISigma1.pi1_succ_induction
    · exact carrySpares_definable
    case zero =>
      intro left right
      simp only [mul_zero, runFrom_zero, oneBlocks_zero, carriedSpares_zero]
    case succ count ih =>
      intro left right
      conv_lhs => arg 1; rw [show (3*(count+1) : V) = (1+2)+3*count by ring]
      rw [show oneBlocks (count+1) right = registerBlock 1 (oneBlocks count right) by
        rw [oneBlocks_succ, registerBlock_one],
        runFrom_add, carry_block, carryReverseBlock_one, ih, carriedSpares_push]
  exact allCounts count left right

/-- Roll back all carried spares and restore their complete original encoding. -/
theorem rollback_spares (count left right : V) :
    runFrom (3*count)
        (leftFrame (rollbackState : V) (carriedSpares count left) right) =
      leftFrame (rollbackState : V) left (oneBlocks count right) := by
  have allCounts : ∀ count : V, RollbackSpares count := by
    intro count
    induction count using ISigma1.pi1_succ_induction
    · exact rollbackSpares_definable
    case zero =>
      intro left right
      simp only [mul_zero, runFrom_zero, oneBlocks_zero, carriedSpares_zero]
    case succ count ih =>
      intro left right
      conv_lhs => arg 1; rw [show (3*(count+1) : V) = (1+2)+3*count by ring]
      rw [show carriedSpares (count+1) left =
          carryReverseBlock 1 (carriedSpares count left) by
        rw [carriedSpares_succ, carryReverseBlock_one],
        runFrom_add, rollback_block, registerBlock_one, ih, oneBlocks_push]
  exact allCounts count left right

/-! Finite physical prefixes, each value still an arbitrary internal value. -/
noncomputable def fileTape : List V → V → V
  | [], suffix => suffix
  | value :: values, suffix => registerBlock value (fileTape values suffix)

noncomputable def fileClock : List V → V
  | [] => 0
  | value :: values => (value+2)+fileClock values

noncomputable def carriedFile : List V → V → V
  | [], left => left
  | value :: values, left => carriedFile values (carryReverseBlock value left)

theorem carry_file (values : List V) (left right : V) :
    runFrom (fileClock values) (frame (carryState : V) left (fileTape values right)) =
      frame (carryState : V) (carriedFile values left) right := by
  induction values generalizing left with
  | nil => simp only [fileClock, fileTape, carriedFile, runFrom_zero]
  | cons value values ih =>
    simp only [fileClock, fileTape, carriedFile]
    rw [runFrom_add, carry_block, ih]

theorem rollback_file (values : List V) (left right : V) :
    runFrom (fileClock values)
        (leftFrame (rollbackState : V) (carriedFile values left) right) =
      leftFrame (rollbackState : V) left (fileTape values right) := by
  induction values generalizing left right with
  | nil => simp only [fileClock, fileTape, carriedFile, runFrom_zero]
  | cons value values ih =>
    simp only [fileClock, fileTape, carriedFile]
    conv_lhs => arg 1; rw [add_comm]
    rw [runFrom_add, ih, rollback_block]

theorem carry_file_spares (values : List V) (count left right : V) :
    runFrom (fileClock values+3*count)
        (frame (carryState : V) left (fileTape values (oneBlocks count right))) =
      frame (carryState : V) (carriedSpares count (carriedFile values left)) right := by
  rw [runFrom_add, carry_file, carry_spares]

theorem rollback_file_spares (values : List V) (count left right : V) :
    runFrom (3*count+fileClock values)
        (leftFrame (rollbackState : V)
          (carriedSpares count (carriedFile values left)) right) =
      leftFrame (rollbackState : V) left (fileTape values (oneBlocks count right)) := by
  rw [runFrom_add, rollback_spares, rollback_file]

/-- The file has exactly the nine physical slots; no logical permutation is assumed. -/
theorem carry_physical_file_spares (file : Fin 9 → V) (count left right : V) :
    runFrom (fileClock (List.ofFn file)+3*count)
        (frame (carryState : V) left (fileTape (List.ofFn file) (oneBlocks count right))) =
      frame (carryState : V) (carriedSpares count (carriedFile (List.ofFn file) left)) right :=
  carry_file_spares (List.ofFn file) count left right

theorem rollback_physical_file_spares (file : Fin 9 → V) (count left right : V) :
    runFrom (3*count+fileClock (List.ofFn file))
        (leftFrame (rollbackState : V)
          (carriedSpares count (carriedFile (List.ofFn file) left)) right) =
      leftFrame (rollbackState : V) left (fileTape (List.ofFn file) (oneBlocks count right)) :=
  rollback_file_spares (List.ofFn file) count left right

end SetTheory.BusyBeaver.ZFC.ArithmeticCarryTraversalRotation240
