import DiophantineConsistency.NaturalRegisterRelation
import DiophantineConsistency.CantorRepresentation

/-!
# Older-enumerator Cantor arithmetic with shared registers and existential inputs

The two projection builders use the actual Cantor pairing and `unP` employed
by the older EnumPerm refutation enumerator. The annotated proof checker instead
uses Mathlib max-square pairing; see `RegisterNatPairing`. The missing component is explicit natural
input data which is hidden only at the final representation boundary.
-/

namespace DiophantineConsistency.RegisterCantorPairing

open NaturalRegisterProgram NaturalRegisterRelation ArithmeticDAG
open SetTheory SetTheory.BusyBeaver.ZFC EnumPerm Code254 KCode222

/-- Inputs 0 and 1 are the proposed component and encoded pair; input 2 is
an auxiliary component. Swapping `left` and `right` selects the projection. -/
def cantorProgram (left right : Fin 3) : Program 3 where
  nodes := [.input left, .input 1, .input right, .literal 1,
    .add 0 2, .add 4 3, .mul 4 5, .add 2 2, .add 6 7, .add 1 1]
  topological := by decide +revert
  allowed := by decide +revert

private def lhsWire (left right : Fin 3) : Fin (cantorProgram left right).nodes.length :=
  ⟨9,by simp [cantorProgram]⟩
private def rhsWire (left right : Fin 3) : Fin (cantorProgram left right).nodes.length :=
  ⟨8,by simp [cantorProgram]⟩

private theorem cantorProgram_lhs (left right : Fin 3) (x : Fin 3 → ℕ) :
    (cantorProgram left right).eval x (lhsWire left right) = 2 * x 1 := by
  apply Int.ofNat.inj
  change ((cantorProgram left right).eval x (lhsWire left right) : ℤ) = (2 * x 1 : ℕ)
  rw [Program.cast_eval]
  simp [cantorProgram,lhsWire,ArithmeticDAG.value,ArithmeticDAG.run,Node.eval]
  ring

private theorem cantorProgram_rhs (left right : Fin 3) (x : Fin 3 → ℕ) :
    (cantorProgram left right).eval x (rhsWire left right) =
      (x left + x right) * (x left + x right + 1) + 2 * x right := by
  apply Int.ofNat.inj
  change ((cantorProgram left right).eval x (rhsWire left right) : ℤ) =
    (((x left + x right) * (x left + x right + 1) + 2 * x right : ℕ) : ℤ)
  rw [Program.cast_eval]
  simp [cantorProgram,rhsWire,ArithmeticDAG.value,ArithmeticDAG.run,Node.eval]
  ring

private theorem cantor_equation (a b z : ℕ) :
    2 * z = (a + b) * (a + b + 1) + 2 * b ↔ z = P a b := by
  rw [←CantorRepresentation.two_pair]
  omega

/-- All natural encoded pairs, including zero, are covered. -/
def cantorLeft : Relation 2 (fun v => v 0 = (unP (v 1)).1) where
  auxiliaryCount := 1
  program := cantorProgram 0 2
  left := lhsWire 0 2
  right := rhsWire 0 2
  correct := by
    intro v
    simp only [cantorProgram_lhs,cantorProgram_rhs]
    change v 0 = (unP (v 1)).1 ↔ ∃ a : Fin 1 → ℕ,
      2 * v 1 = (v 0 + a 0) * (v 0 + a 0 + 1) + 2 * a 0
    constructor
    · intro h
      refine ⟨fun _ => (unP (v 1)).2, (cantor_equation _ _ _).mpr ?_⟩
      rw [h]
      exact (Cantor.toNat_ofNat (v 1)).symm
    · rintro ⟨a,ha⟩
      have hp := (cantor_equation _ _ _).mp ha
      rw [hp,unP_P']

/-- The second inverse-pairing projection uses the same shared circuit recipe. -/
def cantorRight : Relation 2 (fun v => v 0 = (unP (v 1)).2) where
  auxiliaryCount := 1
  program := cantorProgram 2 0
  left := lhsWire 2 0
  right := rhsWire 2 0
  correct := by
    intro v
    simp only [cantorProgram_lhs,cantorProgram_rhs]
    change v 0 = (unP (v 1)).2 ↔ ∃ a : Fin 1 → ℕ,
      2 * v 1 = (a 0 + v 0) * (a 0 + v 0 + 1) + 2 * v 0
    constructor
    · intro h
      refine ⟨fun _ => (unP (v 1)).1, (cantor_equation _ _ _).mpr ?_⟩
      rw [h]
      exact (Cantor.toNat_ofNat (v 1)).symm
    · rintro ⟨a,ha⟩
      have hp := (cantor_equation _ _ _).mp ha
      rw [hp,unP_P']

private def graphIndex : Fin 2 → Option (Fin 1) :=
  Fin.cases none (fun _ => some 0)

/-- The exact function used by `NativeGraphEnumerator.unpairLeft`. -/
def cantorLeftGraph : GraphRep (fun v : Fin 1 → ℕ => (unP (v 0)).1) :=
  (cantorLeft.compile.reindex graphIndex).ofIff (fun _ => Iff.rfl)

/-- The exact function used by `NativeGraphEnumerator.unpairRight`. -/
def cantorRightGraph : GraphRep (fun v : Fin 1 → ℕ => (unP (v 0)).2) :=
  (cantorRight.compile.reindex graphIndex).ofIff (fun _ => Iff.rfl)

@[simp] theorem cantorLeftGraph_witnessCount : cantorLeftGraph.witnessCount = 11 := rfl
@[simp] theorem cantorRightGraph_witnessCount : cantorRightGraph.witnessCount = 11 := rfl

theorem cantorLeftGraph_binaryOps : cantorLeftGraph.expression.binaryOps ≤ 64 := by
  simpa only [cantorLeftGraph,Rep.ofIff,Rep.reindex,Expr.binaryOps_rename] using
    (show cantorLeft.compile.expression.binaryOps ≤ 64 from cantorLeft.compile_binaryOps)

theorem cantorRightGraph_binaryOps : cantorRightGraph.expression.binaryOps ≤ 64 := by
  simpa only [cantorRightGraph,Rep.ofIff,Rep.reindex,Expr.binaryOps_rename] using
    (show cantorRight.compile.expression.binaryOps ≤ 64 from cantorRight.compile_binaryOps)

theorem cantorLeftGraph_degree : cantorLeftGraph.expression.toPolynomial.totalDegree ≤ 4 := by
  simp only [cantorLeftGraph,Rep.ofIff,Rep.reindex,rename_toPolynomial]
  exact (MvPolynomial.totalDegree_rename_le _ _).trans cantorLeft.compile_degree

theorem cantorRightGraph_degree : cantorRightGraph.expression.toPolynomial.totalDegree ≤ 4 := by
  simp only [cantorRightGraph,Rep.ofIff,Rep.reindex,rename_toPolynomial]
  exact (MvPolynomial.totalDegree_rename_le _ _).trans cantorRight.compile_degree

end DiophantineConsistency.RegisterCantorPairing
