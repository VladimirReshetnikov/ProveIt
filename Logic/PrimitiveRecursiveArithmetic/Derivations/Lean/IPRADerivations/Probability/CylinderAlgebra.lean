import IPRADerivations.Core.OrderCertificates
import IPRADerivations.Probability.Variance

/-!
# The cylinder algebra: union, intersection and additivity as bounded sums

Packet: `probability/ipra_probability_2026-11-20`, `paper/sections/foundation.tex`, Lemma `lem:prob-finite`
("The finite probability kernel"): "The cylinder algebra has exact finite additivity, monotonicity, complement
and union laws … The event statements follow from Boolean identities on each row. For example,
`1_{A ∪ B} + 1_{A ∩ B} = 1_A + 1_B`." Events are row bodies `a(i, x)`, `b(i, x)` over the rows `i < N`
(`N` an object-level term), and probabilities are the bounded sums cleared of the row count:

* `orB a b = a + (b ∸ a)`, `andB a b = b ∸ (b ∸ a)`: the union and the intersection of two events as bodies
  (maximum and minimum of the indicators);
* `monus_le_self`, `point_law`: the row identity `(A ∨ B) + (A ∧ B) = A + B`;
* `union_law`: `∑ (a ∨ b) + ∑ (a ∧ b) ≐ ∑ a + ∑ b`;
* `union_bound`: `∑ (a ∨ b) ≤ ∑ a + ∑ b`;
* `additivity`: if the intersection has mass zero, `∑ (a ∨ b) ≐ ∑ a + ∑ b`;
* `notB a = 1 ∸ a`, `complement_law`: for an indicator (`a(i, x) ≤ 1` on the rows), `∑ (1 ∸ a) + ∑ a ≐ N`.

Monotonicity is `Analysis/PowerSums.sum_le`.
-/

namespace LeanProofs.IPRA.Probability.CylinderAlgebra

open_ipra
open LeanProofs.IPRA.Probability.Variance (sum_one)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

alias monus_le_self := Common.monus_le_self

/-- The row identity `(A ∨ B) + (A ∧ B) = A + B`. -/
theorem point_law (A B : PTm n) : Γ ⊢[PRAAx] A + monus B A + monus B (monus B A) ≐ A + B := by
  ipra_lc -natEq (eq_add_of_le (monus_le_self (Γ := Γ) B A))

variable (a b : PTm 2)

/-- The union of two events: the maximum of the indicators. -/
def orB : PTm 2 := a + monus b a

/-- The intersection of two events: the minimum of the indicators. -/
def andB : PTm 2 := monus b (monus b a)

theorem inst2_orB (i x : PTm n) :
    inst2 (orB a b) i x = inst2 a i x + monus (inst2 b i x) (inst2 a i x) := by
  simp [inst2, orB]

theorem inst2_andB (i x : PTm n) :
    inst2 (andB a b) i x = monus (inst2 b i x) (monus (inst2 b i x) (inst2 a i x)) := by
  simp [inst2, andB]

/-- `P(A ∪ B) + P(A ∩ B) = P(A) + P(B)`, cleared of the row count. -/
theorem union_law (N x : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (orB a b)) N x + ap2 (sumF (andB a b)) N x ≐ ap2 (sumF a) N x + ap2 (sumF b) N x := by
  have h₁ := sum_add (Γ := Γ) (orB a b) (andB a b) N x
  have h₂ := sum_add (Γ := Γ) a b N x
  have h₃ : Γ ⊢[PRAAx] ap2 (sumF (addBody (orB a b) (andB a b))) N x ≐ ap2 (sumF (addBody a b)) N x := by
    refine sum_congr_bounded _ _ x x N (.allI (.impI ?_))
    rw [inst2_addBody, inst2_addBody, inst2_orB, inst2_andB]
    exact point_law _ _
  exact h₁.eqSymm.eqTrans (h₃.eqTrans h₂)

/-- The union bound. -/
theorem union_bound (N x : PTm n) :
    Γ ⊢[PRAAx] le (ap2 (sumF (orB a b)) N x) (ap2 (sumF a) N x + ap2 (sumF b) N x) :=
  le_of_eq_add (union_law a b N x).eqSymm

/-- Finite additivity: events whose intersection has mass zero. -/
theorem additivity (N x : PTm n) (h0 : Γ ⊢[PRAAx] ap2 (sumF (andB a b)) N x ≐ zero) :
    Γ ⊢[PRAAx] ap2 (sumF (orB a b)) N x ≐ ap2 (sumF a) N x + ap2 (sumF b) N x := by
  ipra_lc natEq (union_law (Γ := Γ) a b N x) - natEq h0

/-- The complement of an event. -/
def notB : PTm 2 := monus one a

theorem inst2_notB (i x : PTm n) : inst2 (notB a) i x = monus one (inst2 a i x) := by
  simp [inst2, notB]

/-- `P(Aᶜ) + P(A) = 1`, cleared of the row count: `∑ (1 ∸ a) + ∑ a ≐ N` for an indicator body. -/
theorem complement_law (N x : PTm n)
    (h01 : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶ le (inst2 a (var 0) (Syn.shift x)) one)) :
    Γ ⊢[PRAAx] ap2 (sumF (notB a)) N x + ap2 (sumF a) N x ≐ N := by
  have h₁ := sum_add (Γ := Γ) (notB a) a N x
  have h₃ : Γ ⊢[PRAAx] ap2 (sumF (addBody (notB a) a)) N x ≐ ap2 (sumF (one : PTm 2)) N x := by
    refine sum_congr_bounded _ _ x x N (.allI (.impI ?_))
    have e1 : inst2 (one : PTm 2) (var 0) (Syn.shift x) = one := by simp [inst2]
    rw [inst2_addBody, inst2_notB, e1]
    have hle := Prf.impE h01.allOpen.wk Prf.hyp0
    ipra_lc -natEq (eq_add_of_le hle)
  exact h₁.eqSymm.eqTrans (h₃.eqTrans (sum_one N x))

end LeanProofs.IPRA.Probability.CylinderAlgebra
