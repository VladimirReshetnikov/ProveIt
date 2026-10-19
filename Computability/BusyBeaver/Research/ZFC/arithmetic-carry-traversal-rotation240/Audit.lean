import BusyBeaver.ZFC.ArithmeticCarryTraversalRotation240

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open ArithmeticMachineUniformScansPerm252 ArithmeticMachineRunFromRotation240
open ArithmeticRegisterForwardPerm252 (registerBlock)
open ArithmeticRegisterCarryRotation240 ArithmeticOneRegisterBlocksRotation240
open ArithmeticCarryTraversalRotation240

#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCarryTraversalRotation240.carriedSpares_defined_delta
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCarryTraversalRotation240.carriedSpares_zero
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCarryTraversalRotation240.carriedSpares_succ
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCarryTraversalRotation240.carriedSpares_add
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCarryTraversalRotation240.carriedSpares_push
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCarryTraversalRotation240.registerBlock_one
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCarryTraversalRotation240.carryReverseBlock_one
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCarryTraversalRotation240.carry_spares
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCarryTraversalRotation240.rollback_spares
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCarryTraversalRotation240.carry_file
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCarryTraversalRotation240.rollback_file
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCarryTraversalRotation240.carry_file_spares
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCarryTraversalRotation240.rollback_file_spares
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCarryTraversalRotation240.carry_physical_file_spares
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCarryTraversalRotation240.rollback_physical_file_spares

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (e : Fin 3 → V) :
    carriedSparesDeltaDef.val.Evalb e ↔ e 0 = carriedSpares (e 1) (e 2) :=
  carriedSpares_defined_delta.df e
example (suffix : V) : carriedSpares 0 suffix = suffix := carriedSpares_zero suffix
example (count suffix : V) :
    carriedSpares (count+1) suffix = 8*carriedSpares count suffix+5 :=
  carriedSpares_succ count suffix
example (first second suffix : V) :
    carriedSpares (first+second) suffix = carriedSpares second (carriedSpares first suffix) :=
  carriedSpares_add first second suffix
example (count suffix : V) :
    carriedSpares count (8*suffix+5) = carriedSpares (count+1) suffix :=
  carriedSpares_push count suffix
example (suffix : V) : registerBlock (1 : V) suffix = 8*suffix+6 := registerBlock_one suffix
example (left : V) : carryReverseBlock (1 : V) left = 8*left+5 := carryReverseBlock_one left

example (count left right : V) :
    runFrom (3*count) (frame (carryState : V) left (oneBlocks count right)) =
      frame (carryState : V) (carriedSpares count left) right :=
  carry_spares count left right
example (count left right : V) :
    runFrom (3*count) (leftFrame (rollbackState : V) (carriedSpares count left) right) =
      leftFrame (rollbackState : V) left (oneBlocks count right) :=
  rollback_spares count left right
example (values : List V) (left right : V) :
    runFrom (fileClock values) (frame (carryState : V) left (fileTape values right)) =
      frame (carryState : V) (carriedFile values left) right :=
  carry_file values left right
example (values : List V) (left right : V) :
    runFrom (fileClock values)
        (leftFrame (rollbackState : V) (carriedFile values left) right) =
      leftFrame (rollbackState : V) left (fileTape values right) :=
  rollback_file values left right
example (values : List V) (count left right : V) :
    runFrom (fileClock values+3*count)
        (frame (carryState : V) left (fileTape values (oneBlocks count right))) =
      frame (carryState : V) (carriedSpares count (carriedFile values left)) right :=
  carry_file_spares values count left right
example (values : List V) (count left right : V) :
    runFrom (3*count+fileClock values)
        (leftFrame (rollbackState : V) (carriedSpares count (carriedFile values left)) right) =
      leftFrame (rollbackState : V) left (fileTape values (oneBlocks count right)) :=
  rollback_file_spares values count left right
example (file : Fin 9 → V) (count left right : V) :
    runFrom (fileClock (List.ofFn file)+3*count)
        (frame (carryState : V) left (fileTape (List.ofFn file) (oneBlocks count right))) =
      frame (carryState : V) (carriedSpares count (carriedFile (List.ofFn file) left)) right :=
  carry_physical_file_spares file count left right
example (file : Fin 9 → V) (count left right : V) :
    runFrom (3*count+fileClock (List.ofFn file))
        (leftFrame (rollbackState : V)
          (carriedSpares count (carriedFile (List.ofFn file) left)) right) =
      leftFrame (rollbackState : V) left (fileTape (List.ofFn file) (oneBlocks count right)) :=
  rollback_physical_file_spares file count left right

-- The new tape function is represented internally, not merely on standard naturals.
example (e : Fin 3 → V) :
    carriedSparesDef.val.Evalb e ↔ e 0 = carriedSpares (e 1) (e 2) :=
  carriedSpares_defined.df e
-- The current baseline spare count may have any additional internal amount.
example (file : Fin 9 → V) (extra left right : V) :
    runFrom (fileClock (List.ofFn file)+3*(167+extra))
        (frame (carryState : V) left
          (fileTape (List.ofFn file) (oneBlocks (167+extra) right))) =
      frame (carryState : V)
        (carriedSpares (167+extra) (carriedFile (List.ofFn file) left)) right :=
  carry_physical_file_spares file (167+extra) left right
