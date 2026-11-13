module
public import M6PA.Model.PAModelPrimitive
public import M6PA.Model.OriginalCoverage
@[expose] public section
namespace M6.Arithmetic.OriginalModelCoverage
open M6.Source M6.Runtime M6.Arithmetic.PA.ModelPrimitive
open OriginalCheck (path)

theorem path_short (i : Nat) : (path i).length ≤ 38 := by
  have h := M6.Program.path_short (OriginalCheck.lift i)
  change (M6.Program.path (OriginalCheck.lift i)).length ≤ 38
  omega

theorem checked_instruction (i : Nat) (code : Instruction)
    (h : OriginalCheck.checkInstruction i code = true) :
    Implements path 3947 (path i) code := by
  cases code with
  | inc r next =>
    obtain ⟨hn,hc⟩ := Bool.and_eq_true_iff.mp h
    exact implements_inc path 3947 (path i) r next 0 1024 (of_decide_eq_true hn)
      (path_short _) hc
  | dec r z p =>
    obtain ⟨hb,hc⟩ := Bool.and_eq_true_iff.mp h
    obtain ⟨hz,hp⟩ := of_decide_eq_true hb
    obtain ⟨cz,cp⟩ := Bool.and_eq_true_iff.mp hc
    exact implements_dec path 3947 (path i) r z p 0 1 1024 1024 hz hp
      (path_short _) (path_short _) cz cp
  | jump next =>
    obtain ⟨hn,hc⟩ := Bool.and_eq_true_iff.mp h
    exact implements_jump path 3947 (path i) next 0 1024 (of_decide_eq_true hn)
      (path_short _) hc
  | halt => exact implements_halt path 3947 (path i) 1024 h

/-- Every original source instruction, including both decrement branches,
executes on the fresh 209 machine in every PA model with a full file and width38.
The original E increment includes the new extra Continue before original F. -/
theorem coverage (i : Nat) (hi : i < 3947) :
    ∃ code, resolveAt exactSites i = some code ∧
      Implements path 3947 (path i) code := by
  have h := OriginalCoverage.checked i hi
  unfold OriginalCheck.checkAt at h
  cases hc : OriginalCheck.codeAt i with
  | none => simp [hc] at h
  | some code =>
    refine ⟨code,?_,checked_instruction i code ?_⟩
    · rw [M6.Legacy213.FastCodes.baseline_resolve]
      exact hc
    · simpa [hc] using h
#print axioms coverage
end M6.Arithmetic.OriginalModelCoverage
