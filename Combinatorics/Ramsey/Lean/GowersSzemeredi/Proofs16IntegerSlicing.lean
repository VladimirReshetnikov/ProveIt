import GowersSzemeredi.Proofs16AscendingIntegerBoxes
import GowersSzemeredi.Proofs16Slicing

/-! Ascending-axis certificates survive the lift and slice of Lemma 16.1. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem boxCons_axis_isAscendingInteger {N k : Nat} [NeZero N]
    (P : Box N k) (hP : P.IsAscendingInteger) (i0 : Fin k) :
    (boxCons P (P.axis i0) (P.axis_step i0)).IsAscendingInteger := by
  obtain ⟨d, Q, hd, hcommon, hQ⟩ := hP
  refine ⟨d, Fin.cons (Q i0) Q, hd, hcommon, ?_⟩
  intro j
  exact Fin.cases (hQ i0) (fun i => hQ i) j

theorem boxTail_isAscendingInteger {N k : Nat} [NeZero N]
    (P : Box N (k + 1)) (hP : P.IsAscendingInteger) : (boxTail P).IsAscendingInteger := by
  obtain ⟨d, Q, hd, hcommon, hQ⟩ := hP
  exact ⟨d, fun i => Q i.succ, hd, hcommon, fun i => hQ i.succ⟩

end LeanProofs.GowersSzemeredi
