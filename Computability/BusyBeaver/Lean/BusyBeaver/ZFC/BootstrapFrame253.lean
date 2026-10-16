import BusyBeaver.ZFC.Boot253
import BusyBeaver.ZFC.Prefix330

/-!
The proved binary bootstrap frame realizes the proved register endpoint.

The layout is the dispatch invariant of Jeff's verification of Mira-Cult's
machine, using Wade's framework, `ZF/m254/coq/tm/Sim.v`, lines 81–85.
The specific prefix and spare suffix follow mira-emmy's public PR20 head
0d544f2a2e3c18f12278441a74b7879f31cbe856,
`ZF/m253/coq/tm/{Sim,Boot253,Check253}.v`. In that source, old proof label
96 is compact state 33; old start label 5 is compact state 0. This module
uses the actual compact state throughout, without assuming a relabeling
of the different 254-state table.

Only the first nine physical blocks encode the logical registers, under
the published permutation. Additional blocks are independent spare data;
they need not be zero even when every logical register >=9 is zero. The
general frame permits an arbitrary finite spare suffix and retains the
entire tape, including exterior zeros. It is a representation predicate;
preservation by arbitrary instructions is not proved here.

The final theorem combines existing Core312975 and RM330 certificates.
No bootstrap execution is recomputed. There is no first-arrival, general
runtime simulation, proof enumeration, or consistency-equivalence claim.
-/

namespace SetTheory.BusyBeaver.ZFC.BootstrapFrame253

open RegisterPath FiniteZipper

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

def primaryValues (R : Registers) : List Nat := Prefix330.physicalOrder.map R

/-- Source `sepsR`: every block is 0 followed by value+1 ones. -/
def registerBits (values : List Nat) : List Bool := Boot253.registerBits253 values

/-- The two padding lengths record finite exterior blanks; their completion
is still all zeros. The right list starts at the first PC cell. -/
def dispatchZip {states : Nat} (dispatch : Fin states) (head : Int)
    (leftPadding rightPadding : Nat) (logical : Configuration)
    (gap : Nat) (spares : List Nat) : ZipConfig states :=
  { state := some dispatch, head := head,
    left := true :: List.replicate leftPadding false,
    right := logical.path ++ List.replicate gap false ++ [true] ++
      registerBits (primaryValues logical.registers ++ spares) ++
      List.replicate rightPadding false }

/-- The complete infinite logical vector has zero outside its nine registers. -/
def LogicalTailZero (R : Registers) : Prop := ∀ i : Nat, R (9 + i) = 0

/-- A whole-tape dispatch representation, with arbitrary spare data.
The lower bound is on PC length plus gap, rather than the gap alone. -/
def DispatchFrame {states : Nat} (dispatch : Fin states) (binary : Config states)
    (logical : Configuration) (gap : Nat) (spares : List Nat) : Prop :=
  40 ≤ logical.path.length + gap ∧ LogicalTailZero logical.registers ∧
    ∃ leftPadding rightPadding : Nat,
      ZipRep binary (dispatchZip dispatch binary.head leftPadding rightPadding logical gap spares)

def dispatch253 : Fin 253 := ⟨33, by decide⟩

/-- Exact public ext158; its nonzero entries are independent of logical registers. -/
def spares158 : List Nat :=
  [0, 0, 1, 0, 0, 0, 0, 0, 1] ++ List.replicate 149 0

theorem spares158_length : spares158.length = 158 := by decide

theorem spares158_nonzero_indices :
    (List.range 158).filter (fun i => spares158[i]?.getD 0 != 0) = [2, 8] := by decide

theorem target_primary_values :
    primaryValues (decode Prefix330.finiteTarget).registers = [0, 2, 0, 0, 0, 0, 5, 0, 0] :=
  Prefix330.target_physical_registers

/-- Equality of finite zipper data only; it does not rerun the binary machine. -/
theorem target_zip :
    dispatchZip dispatch253 (-17) 10 1 (decode Prefix330.finiteTarget) 37 spares158 =
      Boot253.bootTarget253 := by decide

/-- The concrete representation keeps the absolute head and both exterior pads. -/
theorem boot_exact_dispatch_zip :
    ZipRep (machine253.run 312975)
      (dispatchZip dispatch253 (-17) 10 1 (decode Prefix330.finiteTarget) 37 spares158) := by
  rw [target_zip]
  exact Boot253.fullBootstrap253

/-- Every actual Core tape cell realizes the RM endpoint's dispatch layout. -/
theorem boot_dispatch_frame :
    DispatchFrame dispatch253 (machine253.run 312975)
      (decode Prefix330.finiteTarget) 37 spares158 := by
  refine ⟨by decide, Prefix330.prefix330_registers_tail, 10, 1, ?_⟩
  rw [Boot253.fullBootstrap253_head]
  exact boot_exact_dispatch_zip

theorem boot_marker : Tape.read (machine253.run 312975).tape (-18) = true := by
  rw [Boot253.fullBootstrap253_tape]
  decide

theorem boot_header : Tape.read (machine253.run 312975).tape 23 = true := by
  rw [Boot253.fullBootstrap253_tape]
  decide

/-- The two actual finite computations have the stated whole-tape relation. -/
theorem bootstrap_matches_rm330 :
    run Prog254.program 330 Prog254.initial = some (decode Prefix330.finiteTarget) ∧
    DispatchFrame dispatch253 (machine253.run 312975)
      (decode Prefix330.finiteTarget) 37 spares158 :=
  ⟨Prefix330.prefix330, boot_dispatch_frame⟩

end SetTheory.BusyBeaver.ZFC.BootstrapFrame253
