import DiophantineConsistency.PairingProjection
import DiophantineConsistency.RegisterRelationLogic
import DiophantineConsistency.PairingRepresentation

/-!
# The direct annotated checker's max-square pairing with shared registers

This module uses Mathlib's `Nat.pair`/`Nat.unpair`, not the older enumerator's
Cantor pairing. A natural slack certifies the selected inequality branch;
the branch equations are conjoined and disjoined using explicit nonnegative
register values. No supplied semantic compiler theorem is assumed.
-/

namespace DiophantineConsistency.RegisterNatPairing

open NaturalRegisterProgram NaturalRegisterRelation ArithmeticDAG RegisterRelationLogic

attribute [local irreducible] Nat.unpair

def leftA (z a b s : ℕ) := andLeft (a + s + 1) b z (b * b + a)
def leftB (z a b s : ℕ) := andRight (a + s + 1) b z (b * b + a)
def rightA (z a b s : ℕ) := andLeft (b + s) a z (a * a + a + b)
def rightB (z a b s : ℕ) := andRight (b + s) a z (a * a + a + b)

def certificateLeft (z a b s : ℕ) := orLeft (leftA z a b s) (leftB z a b s)
  (rightA z a b s) (rightB z a b s)
def certificateRight (z a b s : ℕ) := orRight (leftA z a b s) (leftB z a b s)
  (rightA z a b s) (rightB z a b s)

theorem certificate_iff (z a b s : ℕ) :
    certificateLeft z a b s = certificateRight z a b s ↔
      (a + s + 1 = b ∧ z = b * b + a) ∨
      (b + s = a ∧ z = a * a + a + b) := by
  simp only [certificateLeft,certificateRight,or_equality_iff,leftA,leftB,rightA,rightB,
    and_equality_iff]

theorem exists_certificate_iff (z a b : ℕ) :
    (∃ s, certificateLeft z a b s = certificateRight z a b s) ↔ z = Nat.pair a b := by
  simp only [certificate_iff]
  constructor
  · rintro ⟨s,(⟨hab,hz⟩ | ⟨hba,hz⟩)⟩
    · have hlt : a < b := by omega
      simpa only [Nat.pair,if_pos hlt] using hz
    · have hnot : ¬a < b := by omega
      simpa only [Nat.pair,if_neg hnot] using hz
  · intro hz
    by_cases hab : a < b
    · exact ⟨b-a-1,Or.inl ⟨by omega,by simpa only [Nat.pair,if_pos hab] using hz⟩⟩
    · exact ⟨a-b,Or.inr ⟨by omega,by simpa only [Nat.pair,if_neg hab] using hz⟩⟩

/-- Input 1 is the encoded pair; inputs `left`,`right` supply its components;
input 3 is the inequality slack. Each intermediate is stored once. -/
def program (left right : Fin 4) : Program 4 where
  nodes := [
    .input 1, .input left, .input right, .input 3, .literal 1, .literal 2,
    .add 1 3, .add 6 4, .mul 2 2, .add 8 1, .mul 7 7, .mul 0 0,
    .mul 9 9, .add 10 8, .add 11 12, .add 13 14,
    .mul 7 2, .mul 0 9, .add 16 17, .mul 5 18,
    .add 2 3, .mul 1 1, .add 21 1, .add 22 2, .mul 20 20, .mul 23 23,
    .add 24 21, .add 11 25, .add 26 27,
    .mul 20 1, .mul 0 23, .add 29 30, .mul 5 31,
    .mul 15 28, .mul 19 32, .add 33 34,
    .mul 15 32, .mul 19 28, .add 36 37]
  topological := by decide +revert
  allowed := by decide +revert

private def lhsWire (left right : Fin 4) : Fin (program left right).nodes.length :=
  ⟨35,by simp [program]⟩
private def rhsWire (left right : Fin 4) : Fin (program left right).nodes.length :=
  ⟨38,by simp [program]⟩

private theorem program_lhs (left right : Fin 4) (x : Fin 4 → ℕ) :
    (program left right).eval x (lhsWire left right) =
      certificateLeft (x 1) (x left) (x right) (x 3) := by
  apply Int.ofNat.inj
  change ((program left right).eval x (lhsWire left right) : ℤ) =
    (certificateLeft (x 1) (x left) (x right) (x 3) : ℤ)
  rw [Program.cast_eval]
  simp [program,lhsWire,ArithmeticDAG.value,ArithmeticDAG.run,Node.eval,
    certificateLeft,leftA,leftB,rightA,rightB,andLeft,andRight,orLeft]

private theorem program_rhs (left right : Fin 4) (x : Fin 4 → ℕ) :
    (program left right).eval x (rhsWire left right) =
      certificateRight (x 1) (x left) (x right) (x 3) := by
  apply Int.ofNat.inj
  change ((program left right).eval x (rhsWire left right) : ℤ) =
    (certificateRight (x 1) (x left) (x right) (x 3) : ℤ)
  rw [Program.cast_eval]
  simp [program,rhsWire,ArithmeticDAG.value,ArithmeticDAG.run,Node.eval,
    certificateRight,leftA,leftB,rightA,rightB,andLeft,andRight,orRight]

/-- The first projection for every input to the annotated proof checker. -/
def leftRelation : Relation 2 (fun v => v 0 = (Nat.unpair (v 1)).1) where
  auxiliaryCount := 2
  program := program 0 2
  left := lhsWire 0 2
  right := rhsWire 0 2
  correct := by
    intro v
    simp only [program_lhs,program_rhs]
    change v 0 = (Nat.unpair (v 1)).1 ↔ ∃ w : Fin 2 → ℕ,
      certificateLeft (v 1) (v 0) (w 0) (w 1) = certificateRight (v 1) (v 0) (w 0) (w 1)
    symm
    simp only [Fin.exists_fin_succ_pi, Fin.exists_fin_zero_pi]
    change (∃ b s, certificateLeft (v 1) (v 0) b s =
      certificateRight (v 1) (v 0) b s) ↔ _
    simp only [exists_certificate_iff]
    exact PairingProjection.exists_right_iff Nat.pairEquiv (v 1) (v 0)

/-- The second projection uses the identical branch circuit with swapped inputs. -/
def rightRelation : Relation 2 (fun v => v 0 = (Nat.unpair (v 1)).2) where
  auxiliaryCount := 2
  program := program 2 0
  left := lhsWire 2 0
  right := rhsWire 2 0
  correct := by
    intro v
    simp only [program_lhs,program_rhs]
    change v 0 = (Nat.unpair (v 1)).2 ↔ ∃ w : Fin 2 → ℕ,
      certificateLeft (v 1) (w 0) (v 0) (w 1) = certificateRight (v 1) (w 0) (v 0) (w 1)
    symm
    simp only [Fin.exists_fin_succ_pi, Fin.exists_fin_zero_pi]
    change (∃ b s, certificateLeft (v 1) b (v 0) s =
      certificateRight (v 1) b (v 0) s) ↔ _
    simp only [exists_certificate_iff]
    exact PairingProjection.exists_left_iff Nat.pairEquiv (v 1) (v 0)

private def graphIndex : Fin 2 → Option (Fin 1) :=
  Fin.cases none (fun _ => some 0)

/-- Explicit shared-register graph data for Mathlib's first inverse projection. -/
def leftGraph : GraphRep (fun v : Fin 1 → ℕ => (Nat.unpair (v 0)).1) :=
  (leftRelation.compile.reindex graphIndex).ofIff (fun _ => Iff.rfl)

def rightGraph : GraphRep (fun v : Fin 1 → ℕ => (Nat.unpair (v 0)).2) :=
  (rightRelation.compile.reindex graphIndex).ofIff (fun _ => Iff.rfl)

@[simp] theorem leftGraph_witnessCount : leftGraph.witnessCount = 41 := rfl
@[simp] theorem rightGraph_witnessCount : rightGraph.witnessCount = 41 := rfl

theorem leftGraph_binaryOps : leftGraph.expression.binaryOps ≤ 238 := by
  simpa only [leftGraph,Rep.ofIff,Rep.reindex,Expr.binaryOps_rename] using
    (show leftRelation.compile.expression.binaryOps ≤ 238 from leftRelation.compile_binaryOps)

theorem rightGraph_binaryOps : rightGraph.expression.binaryOps ≤ 238 := by
  simpa only [rightGraph,Rep.ofIff,Rep.reindex,Expr.binaryOps_rename] using
    (show rightRelation.compile.expression.binaryOps ≤ 238 from rightRelation.compile_binaryOps)

theorem leftGraph_degree : leftGraph.expression.toPolynomial.totalDegree ≤ 4 := by
  simp only [leftGraph,Rep.ofIff,Rep.reindex,rename_toPolynomial]
  exact (MvPolynomial.totalDegree_rename_le _ _).trans leftRelation.compile_degree

theorem rightGraph_degree : rightGraph.expression.toPolynomial.totalDegree ≤ 4 := by
  simp only [rightGraph,Rep.ofIff,Rep.reindex,rename_toPolynomial]
  exact (MvPolynomial.totalDegree_rename_le _ _).trans rightRelation.compile_degree

end DiophantineConsistency.RegisterNatPairing
