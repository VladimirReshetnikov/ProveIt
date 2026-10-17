import BusyBeaver.ZFC.ArithmeticCantor

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor

#print axioms triangle_double
#print axioms triangle_succ
#print axioms triangle_mono
#print axioms le_triangle
#print axioms cantor_double
#print axioms cantor_graph
#print axioms components_le
#print axioms diagonal_lt
#print axioms cantor_injective
#print axioms diagonal_exists
#print axioms cantor_surjective
#print axioms projections_spec
#print axioms cantor_projections
#print axioms first_cantor
#print axioms second_cantor
#print axioms cantor_defined
#print axioms first_defined
#print axioms second_defined
#print axioms triangle_nat
#print axioms cantor_nat
#print axioms projections_nat
#print axioms first_nat
#print axioms second_nat
#print axioms codeP_defined
#print axioms codeFirst_defined
#print axioms codeSecond_defined
#print axioms codeP_graph

section GenericCallers
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]

-- All elements of an arbitrary, potentially nonstandard, IOpen model.
example (p : V) : ∃ a b, a ≤ p ∧ b ≤ p ∧ p = cantor a b :=
  cantor_surjective p

example (p : V) : ∃! ab : V × V, p = cantor ab.1 ab.2 := by
  refine ⟨(first p, second p), (projections_spec p).2.2, ?_⟩
  intro ab hab
  exact Prod.ext (cantor_injective (hab.symm.trans (cantor_projections p).symm)).1
    (cantor_injective (hab.symm.trans (cantor_projections p).symm)).2

example (a b c d : V) : cantor a b = cantor c d ↔ a = c ∧ b = d := by
  constructor
  · exact cantor_injective
  · rintro ⟨rfl, rfl⟩; rfl

example (p : V) : first p ≤ p ∧ second p ≤ p :=
  ⟨(projections_spec p).1, (projections_spec p).2.1⟩

example (v : Fin 3 → V) : ArithmeticCantor.pairDef.val.Evalb v ↔ v 0 = cantor (v 1) (v 2) :=
  (cantor_defined (V := V)).df v

example (v : Fin 2 → V) : firstDef.val.Evalb v ↔ v 0 = first (v 1) :=
  (first_defined (V := V)).df v

example (v : Fin 2 → V) : secondDef.val.Evalb v ↔ v 0 = second (v 1) :=
  (second_defined (V := V)).df v
end GenericCallers

-- No extra arithmetic/model premises in these actual implementation callers.
example (a b : Nat) : cantor a b = Code254.P a b := cantor_nat a b
example (p : Nat) : (first p, second p) = SetTheory.Cantor.ofNat p := projections_nat p
example (a b : Nat) : first (Code254.P a b) = a := by
  rw [first_nat, Code254.unP_P]
example (a b : Nat) : second (Code254.P a b) = b := by
  rw [second_nat, Code254.unP_P]
example : first (0 : Nat) = 0 ∧ second (0 : Nat) = 0 := by
  exact ⟨first_nat 0, second_nat 0⟩
example (p a b : Nat) : p = Code254.P a b ↔
    2 * p = (a + b) * (a + b + 1) + 2 * b := codeP_graph p a b
example (v : Fin 3 → Nat) : ArithmeticCantor.pairDef.val.Evalb v ↔ v 0 = Code254.P (v 1) (v 2) :=
  codeP_defined.df v
example (v : Fin 2 → Nat) : firstDef.val.Evalb v ↔ v 0 = (SetTheory.Cantor.ofNat (v 1)).1 :=
  codeFirst_defined.df v
example (v : Fin 2 → Nat) : secondDef.val.Evalb v ↔ v 0 = (SetTheory.Cantor.ofNat (v 1)).2 :=
  codeSecond_defined.df v
example (a b : Nat) : Code254.wim a b = 4 * cantor a b := by rw [cantor_nat]; rfl
example (a b : Nat) : Code254.wel a b = 4 * cantor a b + 1 := by rw [cantor_nat]; rfl
example (a b : Nat) : Code254.wal a b = 4 * cantor a b + 2 := by rw [cantor_nat]; rfl
example (a b : Nat) : Code254.weq a b = 4 * cantor a b + 3 := by rw [cantor_nat]; rfl
