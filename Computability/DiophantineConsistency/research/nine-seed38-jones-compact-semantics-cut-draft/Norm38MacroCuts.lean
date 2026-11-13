import DiophantineConsistency.Norm38MacroLanguage

/-! Source-only candidate generic cut lemmas; no recipe identity is claimed. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Norm38MacroCuts
open Norm38MacroLanguage ExecutableJones

variable {R : Type*} [CommRing R] (a : Fin 9 → R)

/-- Appending a node preserves every earlier value. -/
theorem snoc_previous {n : Nat} (d : Dag n) (t : Term n) (i : Fin n) :
    (Dag.snoc d t).values a i.castSucc = d.values a i := by
  simp only [Dag.values, Fin.snoc_castSucc]

/-- The newest value is the term evaluated against the prior prefix. -/
theorem snoc_last {n : Nat} (d : Dag n) (t : Term n) :
    (Dag.snoc d t).values a (Fin.last n) = t.eval a (d.values a) 0 (fun _ => 0) := by
  simp only [Dag.values, Fin.snoc_last]

/-- The finite-range macro remains a symbolic sum. -/
theorem eval_range {n : Nat} (prev : Fin n → R) (r : Nat) (k : Fin 40 → Nat)
    (upper : NExpr) (body : Term n) :
    (Term.sumRange upper body).eval a prev r k =
      ∑ j ∈ Finset.range (upper.eval r k), body.eval a prev j k := by
  rfl

/-- The star macro remains the exact seed-indexed finite sum. -/
theorem eval_star {n : Nat} (prev : Fin n → R) (r : Nat) (k : Fin 40 → Nat)
    (body : Term n) :
    (Term.sumStar body).eval a prev r k =
      ∑ k' ∈ codingStar 38 4, body.eval a prev r k' := by
  rfl

#print axioms snoc_previous
#print axioms snoc_last
#print axioms eval_range
#print axioms eval_star
end DiophantineConsistency.Norm38MacroCuts
