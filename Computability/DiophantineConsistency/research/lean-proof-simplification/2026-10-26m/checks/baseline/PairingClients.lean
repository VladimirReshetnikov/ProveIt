import DiophantineConsistency.QuadraticTreeCodeGraphs

/-! Exact client replacements: all constructor data are unchanged. -/
namespace DiophantineConsistency.GraphRep

theorem exists_pair_right_iff (z a : ℕ) :
    (∃ b, z = Nat.pair a b) ↔ a = (Nat.unpair z).1 := by
  constructor
  · rintro ⟨b, rfl⟩
    simp
  · intro h
    exact ⟨(Nat.unpair z).2, by rw [h, Nat.pair_unpair]⟩

theorem exists_pair_left_iff (z b : ℕ) :
    (∃ a, z = Nat.pair a b) ↔ b = (Nat.unpair z).2 := by
  constructor
  · rintro ⟨a, rfl⟩
    simp
  · intro h
    exact ⟨(Nat.unpair z).1, by rw [h, Nat.pair_unpair]⟩

def unpairLeftCoordinate_short : GraphRep (fun v : Fin 1 → ℕ => (Nat.unpair (v 0)).1) := by
  let index : Option (Fin 2) → Option (Fin 1) ⊕ Fin 1
    | none => .inl (some 0)
    | some i => if i = 0 then .inl none else .inr 0
  refine ((Rep.reindex pairCoordinates index).existsBlock).ofIff ?_
  intro v
  change (∃ w : Fin 1 → ℕ, v (some 0) = Nat.pair (v none) (w 0)) ↔
    v none = (Nat.unpair (v (some 0))).1
  simp [Fin.exists_fin_succ_pi, exists_pair_right_iff]

def unpairRightCoordinate_short : GraphRep (fun v : Fin 1 → ℕ => (Nat.unpair (v 0)).2) := by
  let index : Option (Fin 2) → Option (Fin 1) ⊕ Fin 1
    | none => .inl (some 0)
    | some i => if i = 0 then .inr 0 else .inl none
  refine ((Rep.reindex pairCoordinates index).existsBlock).ofIff ?_
  intro v
  change (∃ w : Fin 1 → ℕ, v (some 0) = Nat.pair (w 0) (v none)) ↔
    v none = (Nat.unpair (v (some 0))).2
  simp [Fin.exists_fin_succ_pi, exists_pair_left_iff]

theorem unpairLeftCoordinate_short_eq : unpairLeftCoordinate_short = unpairLeftCoordinate := rfl
theorem unpairRightCoordinate_short_eq : unpairRightCoordinate_short = unpairRightCoordinate := rfl

end DiophantineConsistency.GraphRep

namespace DiophantineConsistency.QuadraticNatPairing
open NaturalRegisterProgram NaturalRegisterRelation QuadraticRegisterSystem
attribute [local irreducible] Nat.unpair

def pairRepresentation_short : Rep (Fin 3) (fun v => v 1 = Nat.pair (v 0) (v 2)) :=
  (System.scopedRep (a := 3) (k := 3) (system 0 2)).ofIff (by
    intro v
    simp only [holds_iff]
    change (∃ w : Fin 3 → ℕ, Certificate (v 1) (v 0) (v 2) (w 0) (w 1) (w 2)) ↔ _
    simpa [Fin.exists_fin_succ_pi] using exists_certificate_iff (v 1) (v 0) (v 2))

def leftRepresentation_short : Rep (Fin 2) (fun v => v 0 = (Nat.unpair (v 1)).1) :=
  (System.scopedRep (a := 2) (k := 4) (system 0 2)).ofIff (by
    intro v
    simp only [holds_iff]
    change (∃ w : Fin 4 → ℕ, Certificate (v 1) (v 0) (w 0) (w 1) (w 2) (w 3)) ↔ _
    simp [Fin.exists_fin_succ_pi, exists_certificate_iff, GraphRep.exists_pair_right_iff])

def rightRepresentation_short : Rep (Fin 2) (fun v => v 0 = (Nat.unpair (v 1)).2) :=
  (System.scopedRep (a := 2) (k := 4) (system 2 0)).ofIff (by
    intro v
    simp only [holds_iff]
    change (∃ w : Fin 4 → ℕ, Certificate (v 1) (w 0) (v 0) (w 1) (w 2) (w 3)) ↔ _
    simp [Fin.exists_fin_succ_pi, exists_certificate_iff, GraphRep.exists_pair_left_iff])

theorem pairRepresentation_short_eq : pairRepresentation_short = pairRepresentation := rfl
theorem leftRepresentation_short_eq : leftRepresentation_short = leftRepresentation := rfl
theorem rightRepresentation_short_eq : rightRepresentation_short = rightRepresentation := rfl

end DiophantineConsistency.QuadraticNatPairing

namespace DiophantineConsistency.QuadraticTreeCodeGraphs
open NaturalRegisterProgram QuadraticRegisterSystem AnnotatedCodeArithmetic
attribute [local irreducible] Nat.unpair

def treeLeftRepresentation_short : Rep (Fin 2) (fun v => v 0 = AnnotatedCodeArithmetic.treeLeft (v 1)) :=
  (System.scopedRep (a := 2) (k := 5) leftSystem).ofIff (by
    intro v
    simp only [left_holds_iff]
    change (∃ w : Fin 5 → ℕ, w 0 = (v 1).pred ∧
      QuadraticNatPairing.Certificate (w 0) (v 0) (w 1) (w 2) (w 3) (w 4)) ↔ _
    simp [Fin.exists_fin_succ_pi, exists_and_left,
      QuadraticNatPairing.exists_certificate_iff, GraphRep.exists_pair_right_iff,
      AnnotatedCodeArithmetic.treeLeft])

def treeRightRepresentation_short : Rep (Fin 2) (fun v => v 0 = AnnotatedCodeArithmetic.treeRight (v 1)) :=
  (System.scopedRep (a := 2) (k := 5) rightSystem).ofIff (by
    intro v
    simp only [right_holds_iff]
    change (∃ w : Fin 5 → ℕ, w 0 = (v 1).pred ∧
      QuadraticNatPairing.Certificate (w 0) (w 1) (v 0) (w 2) (w 3) (w 4)) ↔ _
    simp [Fin.exists_fin_succ_pi, exists_and_left,
      QuadraticNatPairing.exists_certificate_iff, GraphRep.exists_pair_left_iff,
      AnnotatedCodeArithmetic.treeRight])

theorem treeLeftRepresentation_short_eq : treeLeftRepresentation_short = treeLeftRepresentation := rfl
theorem treeRightRepresentation_short_eq : treeRightRepresentation_short = treeRightRepresentation := rfl

#print axioms treeLeftRepresentation_short
#print axioms treeRightRepresentation_short
#print axioms GraphRep.unpairLeftCoordinate_short
#print axioms QuadraticNatPairing.leftRepresentation_short

end DiophantineConsistency.QuadraticTreeCodeGraphs
