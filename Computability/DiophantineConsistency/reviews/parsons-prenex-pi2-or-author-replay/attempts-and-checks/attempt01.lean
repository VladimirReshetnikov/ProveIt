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

end DiophantineConsistency.ParsonsPrenexPiTwoOr
