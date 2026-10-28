import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Computation
import OAI.Algorithms.SubexponentialSAT.SqrtLog.StatementScale

namespace OAI.Algorithms

/-!
# Canonical primitive-machine statement of the stronger SAT target

All input and machine semantics are the audited original definitions.  The
machine is chosen once per fixed width, before all input sizes and formulas.
The final target below is a proposition, not an asserted existence theorem.
-/

namespace SubexponentialSAT.SqrtLog.Statement

open _root_.OAI.Algorithms.SubexponentialSAT.Computation

/-- Correct decision on every canonical input, with a measured primitive trace.
There is no density promise, oracle, or large-input-only qualification. -/
def DecidesWithBound (machine : PrimitiveMachine) (width : ℕ)
    (constant exponentConstant : ℝ) (degree : ℕ) : Prop :=
  ∀ (n : ℕ) (F : SAT.CNF (Fin n)), SAT.WidthAtMost width F →
    ∃ (answer : Bool) (time : ℕ),
      machine.OutputsInTime (Encoding.encodeCNF F) answer time ∧
      (answer = true ↔ SAT.Satisfiable F) ∧
      (time : ℝ) ≤ runtimeBound constant exponentConstant degree
        (Encoding.formulaBitLength F) n

/-- The machine and all constants may depend on width only. -/
def Feasible (width : ℕ) : Prop :=
  ∃ (machine : PrimitiveMachine) (constant exponentConstant : ℝ) (degree : ℕ),
    0 < constant ∧ 0 < exponentConstant ∧ 0 < degree ∧
      DecidesWithBound machine width constant exponentConstant degree

/-- The complete uniform fixed-width target; no inhabitant is supplied here. -/
def MainTheorem : Prop := ∀ width : ℕ, 3 ≤ width → Feasible width

/-- Expansion of every semantic abbreviation in the target's input and output
contract.  This is an equivalence of statements, not a proof of either side. -/
theorem mainTheorem_iff_explicit : MainTheorem ↔
    ∀ k : ℕ, 3 ≤ k →
      ∃ (machine : PrimitiveMachine) (C A : ℝ) (d : ℕ),
        0 < C ∧ 0 < A ∧ 0 < d ∧
        ∀ (n : ℕ) (F : Finset (Finset (SAT.Literal (Fin n)))),
          (∀ clause ∈ F, clause.card ≤ k) →
          ∃ (answer : Bool) (time : ℕ),
            (∃ c : machine.Cfg,
              RunsIn machine.step time (machine.init (Encoding.encodeCNF F)) c ∧
              c.state = Sum.inl answer) ∧
            (answer = true ↔ ∃ assignment : Fin n → Bool,
              ∀ clause ∈ F, ∃ literal ∈ clause,
                assignment literal.variable = literal.positive) ∧
            (time : ℝ) ≤ C * (((Encoding.encodeCNF F).length : ℝ) + 1) ^ d *
              (2 : ℝ) ^ (A * ((n : ℝ) *
                (Real.log (Real.log ((n : ℝ) + 16))) ^ 2 /
                Real.sqrt (Real.log ((n : ℝ) + 16)))) := by
  simp only [MainTheorem, Feasible, DecidesWithBound, SAT.WidthAtMost,
    PrimitiveMachine.OutputsInTime, SAT.Satisfiable, SAT.CNF.eval_eq_true,
    SAT.Clause.eval_eq_true, SAT.Literal.eval_eq_true, runtimeBound,
    runtimeScale, Encoding.formulaBitLength]

theorem feasible_width_antitone {width width' : ℕ} (hw : width ≤ width')
    (h : Feasible width') : Feasible width := by
  obtain ⟨machine, C, A, d, hC, hA, hd, hdec⟩ := h
  refine ⟨machine, C, A, d, hC, hA, hd, ?_⟩
  intro n F hF
  exact hdec n F (fun clause hc => (hF clause hc).trans hw)

end SubexponentialSAT.SqrtLog.Statement

end OAI.Algorithms
