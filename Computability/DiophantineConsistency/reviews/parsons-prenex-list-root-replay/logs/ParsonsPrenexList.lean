import DiophantineConsistency.ParsonsPrenexTree
import DiophantineConsistency.ParsonsStructure

/-! Normalize a finite side-context disjunction of packed prenex trees. -/
set_option autoImplicit false
namespace DiophantineConsistency.ParsonsPrenexList
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ParsonsRule ParsonsPrenexTuple ParsonsPrenexTree

structure Packed where
  n : ℕ
  k : ℕ
  tree : Tree n k

def asFormula (p : Packed) : Proposition ℒₒᵣ := source p.tree

def aggregate : List Packed → Packed
  | [] => ⟨0,0, .leaf (⊥ : ArithmeticSemiformula ℕ 0)⟩
  | p :: ps =>
      let q := aggregate ps
      ⟨q.n+p.n, q.k+p.k, .disj p.tree q.tree⟩

theorem aggregate_source (ps : List Packed) :
    source (aggregate ps).tree = ParsonsStructure.disjoin (ps.map asFormula) := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [aggregate, source, asFormula, ParsonsStructure.disjoin, ih]

theorem aggregate_bounded (ps : List Packed) (h : ∀ p ∈ ps, bounded p.tree) :
    bounded (aggregate ps).tree := by
  induction ps with
  | nil => simp [aggregate, bounded]
  | cons p ps ih =>
      change bounded p.tree ∧ bounded (aggregate ps).tree
      exact ⟨h p (by simp), ih (fun q hq => h q (by simp [hq]))⟩

theorem matrix_bounded (ps : List Packed) (h : ∀ p ∈ ps, bounded p.tree) :
    Hierarchy 𝚺 0 (matrix (aggregate ps).tree) :=
  ParsonsPrenexTree.matrix_bounded _ (aggregate_bounded ps h)

noncomputable def forward (ps : List Packed)
    (h : Proof 𝗣𝗔⁻ (ParsonsStructure.disjoin (ps.map asFormula))) :
    Proof 𝗣𝗔⁻ (block (matrix (aggregate ps).tree)) := by
  apply ParsonsPrenexTree.forward (aggregate ps).tree
  simpa [aggregate_source] using h

noncomputable def backward (ps : List Packed)
    (h : Proof 𝗣𝗔⁻ (block (matrix (aggregate ps).tree))) :
    Proof 𝗣𝗔⁻ (ParsonsStructure.disjoin (ps.map asFormula)) := by
  have hp := ParsonsPrenexTree.backward (aggregate ps).tree h
  simpa [aggregate_source] using hp

end DiophantineConsistency.ParsonsPrenexList
