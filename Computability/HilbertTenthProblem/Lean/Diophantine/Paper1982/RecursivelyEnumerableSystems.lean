import Diophantine.Paper1982.RecursivelyEnumerableQuartic
import Diophantine.Paper1982.Theorem1
import Diophantine.Paper1982.Theorem2
import Diophantine.Paper1982.Theorem3

/-!
# The three printed systems represent every recursively enumerable set

The normalized quartic representation with 58 witnesses supplies a single
coding triple for all three systems. Specializing their parameter to 58
recovers the printed exponent `5^60`. The solvability predicates below
display all 12, 14, and 28 strictly positive witnesses explicitly; the
input and the fixed coding triple are separate parameters.
-/

namespace Jones1982

/-- Solvability of the printed Theorem 1 system, with exactly twelve
strictly positive natural witnesses and the exponent `5^60`. -/
def Theorem1Solvable58 (x z u y : ℕ) : Prop :=
  ∃ b e g l m q t w α η θ lam : ℕ,
    0 < b ∧ 0 < e ∧ 0 < g ∧ 0 < l ∧ 0 < m ∧ 0 < q ∧
    0 < t ∧ 0 < w ∧ 0 < α ∧ 0 < η ∧ 0 < θ ∧ 0 < lam ∧
    Thm1 58 x z u y b e g l m q t w α η θ lam

/-- Solvability of the printed Theorem 2 system, with exactly fourteen
strictly positive natural witnesses and the exponent `5^60`. -/
def Theorem2Solvable58 (x z u y : ℕ) : Prop :=
  ∃ b e g l m n q r t w α η θ lam : ℕ,
    0 < b ∧ 0 < e ∧ 0 < g ∧ 0 < l ∧ 0 < m ∧ 0 < n ∧
    0 < q ∧ 0 < r ∧ 0 < t ∧ 0 < w ∧ 0 < α ∧ 0 < η ∧ 0 < θ ∧ 0 < lam ∧
    Thm2 58 x z u y b e g l m n q r t w α η θ lam

/-- Solvability of the printed Theorem 3 system, with exactly twenty-eight
strictly positive natural witnesses and the exponent `5^60`. -/
def Theorem3Solvable58 (x z u y : ℕ) : Prop :=
  ∃ a b c d e f g h i j k l m n o p q r s t w α γ η θ lam τ φ : ℕ,
    0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧ 0 < e ∧ 0 < f ∧ 0 < g ∧ 0 < h ∧
    0 < i ∧ 0 < j ∧ 0 < k ∧ 0 < l ∧ 0 < m ∧ 0 < n ∧ 0 < o ∧ 0 < p ∧
    0 < q ∧ 0 < r ∧ 0 < s ∧ 0 < t ∧ 0 < w ∧ 0 < α ∧ 0 < γ ∧ 0 < η ∧
    0 < θ ∧ 0 < lam ∧ 0 < τ ∧ 0 < φ ∧
    Thm3 58 x z u y a b c d e f g h i j k l m n o p q r s t w α γ η θ lam τ φ

/-- One strictly positive coding triple represents a recursively enumerable
set by all three printed systems, uniformly over positive inputs. -/
theorem rePred_printed_systems {S : Set ℕ} (hS : REPred S) :
    ∃ z u y : ℕ, 0 < z ∧ 0 < u ∧ 0 < y ∧
      ∀ x : ℕ, 0 < x →
        (x ∈ S ↔ Theorem1Solvable58 x z u y) ∧
        (x ∈ S ↔ Theorem2Solvable58 x z u y) ∧
        (x ∈ S ↔ Theorem3Solvable58 x z u y) := by
  obtain ⟨Q, hdegree, hnorm, hQ⟩ := rePred_quartic58 hS
  obtain ⟨z, u, y, hz, hu, hy, hI⟩ := exists_index (ν := 58) Q (by decide)
  refine ⟨z, u, y, hz, hu, hy, fun x hx => ?_⟩
  exact ⟨(hQ x hx).trans (theorem_1 (ν := 58) (by decide) hdegree hnorm hI hx),
    (hQ x hx).trans (theorem_2 (ν := 58) (by decide) hdegree hnorm hI hx),
    (hQ x hx).trans (theorem_3 (ν := 58) (by decide) hdegree hnorm hI hx)⟩

/-- Every recursively enumerable set is represented by the printed Theorem 1
system with twelve strictly positive witnesses, on positive inputs. -/
theorem rePred_theorem1_system {S : Set ℕ} (hS : REPred S) :
    ∃ z u y : ℕ, 0 < z ∧ 0 < u ∧ 0 < y ∧
      ∀ x : ℕ, 0 < x → (x ∈ S ↔ Theorem1Solvable58 x z u y) := by
  obtain ⟨z, u, y, hz, hu, hy, h⟩ := rePred_printed_systems hS
  exact ⟨z, u, y, hz, hu, hy, fun x hx => (h x hx).1⟩

/-- Every recursively enumerable set is represented by the printed Theorem 2
system with fourteen strictly positive witnesses, on positive inputs. -/
theorem rePred_theorem2_system {S : Set ℕ} (hS : REPred S) :
    ∃ z u y : ℕ, 0 < z ∧ 0 < u ∧ 0 < y ∧
      ∀ x : ℕ, 0 < x → (x ∈ S ↔ Theorem2Solvable58 x z u y) := by
  obtain ⟨z, u, y, hz, hu, hy, h⟩ := rePred_printed_systems hS
  exact ⟨z, u, y, hz, hu, hy, fun x hx => (h x hx).2.1⟩

/-- Every recursively enumerable set is represented by the printed Theorem 3
system with twenty-eight strictly positive witnesses, on positive inputs. -/
theorem rePred_theorem3_system {S : Set ℕ} (hS : REPred S) :
    ∃ z u y : ℕ, 0 < z ∧ 0 < u ∧ 0 < y ∧
      ∀ x : ℕ, 0 < x → (x ∈ S ↔ Theorem3Solvable58 x z u y) := by
  obtain ⟨z, u, y, hz, hu, hy, h⟩ := rePred_printed_systems hS
  exact ⟨z, u, y, hz, hu, hy, fun x hx => (h x hx).2.2⟩

end Jones1982
