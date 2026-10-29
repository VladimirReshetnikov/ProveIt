import DiophantineConsistency.ParsonsPrenexAll
import DiophantineConsistency.ParsonsPrenexPair
import DiophantineConsistency.ParsonsSpecialize

/-! Disjunction of two strict ∀∃ formulas has a tupled ∀∀∃∃ form. -/
set_option autoImplicit false
namespace DiophantineConsistency.ParsonsPrenexPiTwoOr
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ParsonsRule ParsonsSpecialize
variable {L : Language} [L.ORing]

def leftMap : Rew L ℕ 2 ℕ 4 := Rew.bind ![.bvar 1, .bvar 3] .fvar
def rightMap : Rew L ℕ 2 ℕ 4 := Rew.bind ![.bvar 0, .bvar 2] .fvar

def matrix (A B : Semiproposition L 2) : Semiproposition L 4 :=
  (leftMap ▹ A) ⋎ (rightMap ▹ B)

def source (A B : Semiproposition L 2) : Proposition L :=
  (∀⁰ ∃⁰ A) ⋎ (∀⁰ ∃⁰ B)

def target (A B : Semiproposition L 2) : Proposition L :=
  ∀⁰ ∀⁰ ∃⁰ ∃⁰ matrix A B

theorem matrix_bounded (A B : Semiproposition L 2)
    (hA : Hierarchy 𝚺 0 A) (hB : Hierarchy 𝚺 0 B) : Hierarchy 𝚺 0 (matrix A B) := by
  simp [matrix, Hierarchy.rew _ hA, Hierarchy.rew _ hB]

section models
variable {M : Type} [Nonempty M] [Structure L M] [Structure.Eq L M]

theorem eval_matrix (A B : Semiproposition L 2) (e : Fin 4 → M) (f : ℕ → M) :
    (matrix A B).Eval e f ↔ A.Eval ![e 1, e 3] f ∨ B.Eval ![e 0, e 2] f := by
  have hleft : (fun x : Fin 2 => Semiterm.val (L := L) e f (![.bvar 1, .bvar 3] x)) = ![e 1, e 3] := by
    funext i
    exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.elim0 k) j) i
  have hright : (fun x : Fin 2 => Semiterm.val (L := L) e f (![.bvar 0, .bvar 2] x)) = ![e 0, e 2] := by
    funext i
    exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.elim0 k) j) i
  simp [matrix, Semiformula.eval_rew, leftMap, rightMap, Function.comp_def, hleft, hright]

omit [L.ORing] [Nonempty M] [Structure.Eq L M] in
theorem eval_source (A B : Semiproposition L 2) (f : ℕ → M) :
    (source A B).Eval ![] f ↔
      (∀ x : M, ∃ y : M, A.Eval ![y,x] f) ∨ (∀ u : M, ∃ v : M, B.Eval ![v,u] f) := by
  rfl

theorem eval_target (A B : Semiproposition L 2) (f : ℕ → M) :
    (target A B).Eval ![] f ↔
      ∀ x u : M, ∃ y v : M, A.Eval ![y,x] f ∨ B.Eval ![v,u] f := by
  change (∀ x u : M, ∃ y v : M, (matrix A B).Eval ![v,y,u,x] f) ↔ _
  simp [eval_matrix]

theorem semantic_equiv (A B : Semiproposition L 2) (f : ℕ → M) :
    (source A B).Eval ![] f ↔ (target A B).Eval ![] f := by
  rw [eval_source, eval_target]
  classical
  constructor
  · rintro (h | h) x u
    · obtain ⟨y,hy⟩ := h x
      exact ⟨y, Classical.choice ‹Nonempty M›, Or.inl hy⟩
    · obtain ⟨v,hv⟩ := h u
      exact ⟨Classical.choice ‹Nonempty M›, v, Or.inr hv⟩
  · intro h
    by_contra hn
    push Not at hn
    obtain ⟨⟨x,hx⟩, ⟨u,hu⟩⟩ := hn
    obtain ⟨y,v,hy | hv⟩ := h x u
    · exact hx y hy
    · exact hu v hv

end models
end DiophantineConsistency.ParsonsPrenexPiTwoOr
