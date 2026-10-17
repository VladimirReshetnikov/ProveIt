import BusyBeaver.ZFC.DirtyProgram254
import BusyBeaver.ZFC.NumericCode254

/-!
Proof-carrying initial formula data for the attributed 254 register program.

The dirty-start interface from intake 153, source 35 allows arbitrary numerical
control data but requires derivable top/cache formulas and a derivable stack.
This small, deliberately incomplete certificate language constructs such data.
It is an initializer search interface, not a new binary-machine theorem.
The stack uses the original unshifted Cantor pair, not proof-list coding.
-/

namespace SetTheory.BusyBeaver.ZFC.SeedInvariant254

open Code254

inductive Formula where
  | truth
  | all (i : Nat) (p : Formula)
  | identity (a : Nat)
  | weaken (a : Nat) (p : Formula)
  | exfalso (a : Nat)
  | eqRefl (i : Nat)
  deriving Repr

def Formula.code : Formula → Nat
  | .truth => 0
  | .all i p => wal i p.code
  | .identity a => wim a a
  | .weaken a p => wim a p.code
  | .exfalso a => wim F a
  | .eqRefl i => weq i i

theorem eq_refl_code (i : Nat) : C254 (weq i i) := by
  have h : Tarski.Thm (fun _ => False) (Tarski.NF.eq i i) :=
    Tarski.eq_refl (Tarski.classical (fun _ => False)) i
  exact NumericCode254.c254_of_named (fun _ h => h.elim) h

theorem Formula.sound (p : Formula) : C254 p.code := by
  induction p with
  | truth => exact C254.truth
  | all i p ih => exact C254.gen i ih
  | identity a => exact Kalmar.self_imp c254_classical a
  | weaken a p ih => exact C254.mp ih (c254_k p.code a)
  | exfalso a => exact c254_efq a
  | eqRefl i => exact eq_refl_code i

def stackCode : List Formula → Nat
  | [] => 0
  | p :: ps => P p.code (stackCode ps)

theorem stack_good (ps : List Formula) : Enum254.Good (stackCode ps) := by
  induction ps with
  | nil => exact Enum254.good_zero
  | cons p ps ih => exact Enum254.good_cons p.sound ih

/-- A completely explicit family of safe starts. None of the six numerical
fields is bounded, reset or assumed to encode a proof. -/
def state (N A D X Y L : Nat) (top cache : Formula) (stack : List Formula) : L2.AS :=
  ⟨N, top.code, stackCode stack, A, D, cache.code, X, Y, L⟩

theorem state_safe (N A D X Y L : Nat) (top cache : Formula) (stack : List Formula) :
    DirtyProgram254.Safe (state N A D X Y L top cache stack) :=
  ⟨top.sound, cache.sound, stack_good stack⟩

theorem program_halts_iff (N A D X Y L : Nat)
    (top cache : Formula) (stack : List Formula) :
    RMDag.IterHalts Dag254.dag254
      (L2.enc (state N A D X Y L top cache stack)) ↔
      BProv NativeTheory254.NativeAx [] Form.fBot :=
  DirtyProgram254.iter_halts_iff_native_refutation _
    (state_safe N A D X Y L top cache stack)

/-- Nonzero formula fields really occur in the certified family. -/
example : Formula.code (.eqRefl 0) = 3 := by decide
example : Formula.code (.all 1 .truth) = 6 := by decide
example : stackCode [.all 0 .truth, .truth] = 3 := by decide
example : stackCode [.truth, .all 0 .truth] = 9 := by decide

#print axioms Formula.sound
#print axioms stack_good
#print axioms state_safe
#print axioms program_halts_iff

end SetTheory.BusyBeaver.ZFC.SeedInvariant254
