module
public import PA196.Program
public import PA196.Arithmetic.Machine.PAModelPrimitive
public import PA196.Arithmetic.Machine.OriginalCoverage
@[expose] public section
namespace PA196.Arithmetic.Machine.OriginalModelCoverage
open M6.Source M6.Runtime PA196.Arithmetic.Machine.PA.ModelPrimitive
open OriginalCheck (path)

theorem path_short (i : Nat) : (path i).length ≤ 38 :=
  PA196.Program.path_short i

theorem checked_instruction (i : Nat) (code : Instruction)
    (h : OriginalCheck.checkInstruction i code = true) :
    Implements path 3812 (path i) code := by
  cases code with
  | inc r next =>
    obtain ⟨hn,hc⟩ := Bool.and_eq_true_iff.mp h
    exact implements_inc path 3812 (path i) r next 0 1024 (of_decide_eq_true hn)
      (path_short _) hc
  | dec r z p =>
    obtain ⟨hb,hc⟩ := Bool.and_eq_true_iff.mp h
    obtain ⟨hz,hp⟩ := of_decide_eq_true hb
    obtain ⟨cz,cp⟩ := Bool.and_eq_true_iff.mp hc
    exact implements_dec path 3812 (path i) r z p 0 1 1024 1024 hz hp
      (path_short _) (path_short _) cz cp
  | jump next =>
    obtain ⟨hn,hc⟩ := Bool.and_eq_true_iff.mp h
    exact implements_jump path 3812 (path i) next 0 1024 (of_decide_eq_true hn)
      (path_short _) hc
  | halt => exact implements_halt path 3812 (path i) 1024 h

/-- Every original source instruction, including both decrement branches,
executes on the fresh PA196 auxiliary machine in every PA model with a full file and gap floor48.
The original E increment includes the new extra Continue before original F. -/
theorem coverage (i : Nat) (hi : i < 3812) :
    ∃ code, resolveAt PA196.Program.sites i = some code ∧
      Implements path 3812 (path i) code := by
  have h := OriginalCoverage.checked i hi
  unfold PA196.CheckCoverage.checkAt at h
  cases hc : PA196.CheckCoverage.codeAt i with
  | none => simp [hc] at h
  | some code =>
    refine ⟨code,?_,checked_instruction i code ?_⟩
    · rw [PA196.Program.resolve_tree]
      exact hc
    · simpa [hc] using h
#print axioms coverage
end PA196.Arithmetic.Machine.OriginalModelCoverage
