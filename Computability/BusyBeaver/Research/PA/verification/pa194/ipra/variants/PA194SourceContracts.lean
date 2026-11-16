import PA194FoldedChecks
import ConPAMachineCompressedNormalization

set_option autoImplicit false

namespace PA194SourceContracts
open M6.Runtime M6.Source PA194SourceProgram PA194CompressedRootContracts

def contract (machine : M6.Zip.TMN) (path : Nat → Path)
    (br : Branch) (i j extra fuel : Nat) (e : Eff) : Bool :=
  (exec machine br (fun s => sMatches s (PA194RuntimeContracts.rootFrame (path j) extra e))
    fuel (PA194RuntimeContracts.rootFrame (path i)) false).isSome

def haltContract (machine : M6.Zip.TMN) (path : Nat → Path) (i fuel : Nat) : Bool :=
  (exec machine none (fun s => s.1 == 254) fuel
    (PA194RuntimeContracts.rootFrame (path i)) false).isSome

def checkInstruction (machine : M6.Zip.TMN) (path : Nat → Path) (i : Nat) : Instruction → Bool
  | .inc r next => decide (next.getD 0 < 3673) &&
    contract machine path none i (next.getD 0) 0 512 (.inc (physicalRegister r))
  | .dec r z p => decide (z.getD 0 < 3673 ∧ p.getD 0 < 3673) &&
    (contract machine path (some (physicalRegister r, true)) i (z.getD 0) 0 512 .none &&
    contract machine path (some (physicalRegister r, false)) i (p.getD 0) 1 512 (.dec (physicalRegister r)))
  | .jump next => decide (next.getD 0 < 3673) &&
    contract machine path none i (next.getD 0) 0 512 .none
  | .halt => haltContract machine path i 512

/-- Check both the resolved source instruction and every applicable physical branch. -/
def checkAt (machine : M6.Zip.TMN) (path : Nat → Path) (codeAt : Nat → Option Instruction)
    (i : Nat) : Bool :=
  decide (codeAt i = PA194CheckCoverage.codeAt i) &&
    (codeAt i).any (checkInstruction machine path i)

theorem checked_at (machine : M6.Zip.TMN) (path : Nat → Path) (codeAt : Nat → Option Instruction)
    (i : Nat) (h : checkAt machine path codeAt i = true) :
    ∃ code, M6.Source.resolveAt sites i = some code ∧ checkInstruction machine path i code = true := by
  unfold checkAt at h
  rcases Bool.and_eq_true_iff.mp h with ⟨agreement, checked⟩
  rw [of_decide_eq_true agreement] at checked
  cases hc : PA194CheckCoverage.codeAt i with
  | none => simp [hc] at checked
  | some code =>
    refine ⟨code, ?_, by simpa [hc] using checked⟩
    rw [PA194SourceProgram.resolve_tree]
    exact hc

def blockCheck (check : Nat → Bool) (base count : Nat) : Bool :=
  (List.range count).all (fun j => check (base + j))

theorem block_sound {check : Nat → Bool} {base count i : Nat} (h : blockCheck check base count = true)
    (lo : base ≤ i) (hi : i < base + count) : check i = true := by
  have checked := List.all_eq_true.mp h (i - base) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le lo] using checked

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ConPA.Machine ConPA.Machine.Compressed

section models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def root (label : Nat → Nat) (path : Nat → Path) (gap : V) (box : BoxSt → V)
    (i : Nat) (extra : Nat := 0) (effect : Eff := .none) : V :=
  encode label gap box (PA194RuntimeContracts.rootFrame (path i) extra effect)

theorem encodeControl (label : Nat → Nat) (gap : V) (box : BoxSt → V) (s : SConf) :
    π₁ (encode label gap box s) = (label s.1 : V) := by
  rcases s with ⟨q, onLeft, l, r⟩
  cases onLeft <;> simp [encode, scanFrame]

theorem contract_sound {T : Table} {machine : M6.Zip.TMN} {label : Nat → Nat}
    (rows : RowAgreement T machine label) (path : Nat → Path)
    (gap : V) {br : Branch} {box : BoxSt → V} (boxes : BoxAgreement T label br box)
    (i j extra fuel : Nat) (effect : Eff) (cert : contract machine path br i j extra fuel effect = true) :
    Reach1 T (root label path gap box i) (root label path gap box j extra effect) :=
  checkedMatch rows gap boxes fuel _ _ cert

theorem halt_sound {T : Table} {machine : M6.Zip.TMN} {label : Nat → Nat}
    (rows : RowAgreement T machine label) (path : Nat → Path) {halt : Nat}
    (terminal : label 254 = halt) (gap : V) {box : BoxSt → V} (boxes : BoxAgreement T label none box)
    (i fuel : Nat) (cert : haltContract machine path i fuel = true) :
    ∃ final, Reach1 T (root label path gap box i) final ∧ π₁ final = (halt : V) := by
  let start := PA194RuntimeContracts.rootFrame (path i)
  change (exec machine none (fun s => s.1 == 254) fuel start false).isSome = true at cert
  cases observed : exec machine none (fun s => s.1 == 254) fuel start false with
  | none => simp [observed] at cert
  | some last =>
    obtain ⟨finished, _, positive⟩ :=
      checkedRun rows gap boxes (fun s => s.1 == 254) fuel start last false observed
    refine ⟨encode label gap box last, positive rfl, ?_⟩
    rw [encodeControl, beq_iff_eq.mp finished, terminal]

#print axioms checked_at
#print axioms contract_sound
#print axioms halt_sound
end models
end PA194SourceContracts
