import DiophantineConsistency.NaturalExpression
import Diophantine.Common.PolynomialDegree
import Diophantine.Common.PolynomialRenaming
import Diophantine.Paper1982.Master1
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.FinCases

/-!
# A finite quartic compiler from supplied arithmetic representation data

Natural expressions are flattened into one natural-valued gate per syntax
node. The node type, its cardinality, and its bijection with a finite range
are computed by structural recursion. Quadratic gate residuals, an output
equality, and a guard equal to one give a normalized sum-of-squares quartic.
No representation or enumeration index is selected from an existential
proposition.
-/

namespace DiophantineConsistency.QuarticCompiler

open MvPolynomial Jones1982

namespace Gates

variable {σ : Type*}

/-- A leaf has one node; an operation adds its root before its two subtrees. -/
abbrev Wire : NatExpr σ → Type
  | .constant _ => Fin 1
  | .var _ => Fin 1
  | .add p q => Fin 1 ⊕ (Wire p ⊕ Wire q)
  | .mul p q => Fin 1 ⊕ (Wire p ⊕ Wire q)

def count : NatExpr σ → ℕ
  | .constant _ => 1
  | .var _ => 1
  | .add p q => 1 + (count p + count q)
  | .mul p q => 1 + (count p + count q)

/-- The finite indexing is literal sum indexing, rather than `Fintype.equivFin`. -/
def index : (e : NatExpr σ) → Wire e ≃ Fin (count e)
  | .constant _ => Equiv.refl _
  | .var _ => Equiv.refl _
  | .add p q =>
      ((Equiv.sumCongr (Equiv.refl (Fin 1)) (Equiv.sumCongr (index p) (index q))).trans
        (Equiv.sumCongr (Equiv.refl (Fin 1)) finSumFinEquiv)).trans finSumFinEquiv
  | .mul p q =>
      ((Equiv.sumCongr (Equiv.refl (Fin 1)) (Equiv.sumCongr (index p) (index q))).trans
        (Equiv.sumCongr (Equiv.refl (Fin 1)) finSumFinEquiv)).trans finSumFinEquiv

instance (e : NatExpr σ) : Fintype (Wire e) := Fintype.ofEquiv (Fin (count e)) (index e).symm

/-- The output root of an expression tree. -/
def root : (e : NatExpr σ) → Wire e
  | .constant _ => 0
  | .var _ => 0
  | .add _ _ => Sum.inl 0
  | .mul _ _ => Sum.inl 0

/-- Actual acyclic gate code, expressed by one quadratic residual per node. -/
def residualSyntax : (e : NatExpr σ) → Wire e → Expr (σ ⊕ Wire e)
  | .constant n, _ => .var (Sum.inr 0) - .constant (n : ℤ)
  | .var i, _ => .var (Sum.inr 0) - .var (Sum.inl i)
  | .add p q, Sum.inl _ =>
      .var (Sum.inr (Sum.inl 0)) - (.var (Sum.inr (Sum.inr (Sum.inl (root p)))) + .var (Sum.inr (Sum.inr (Sum.inr (root q)))))
  | .add p _, Sum.inr (Sum.inl k) =>
      (residualSyntax p k).rename (Sum.map id (fun j => Sum.inr (Sum.inl j)))
  | .add _ q, Sum.inr (Sum.inr k) =>
      (residualSyntax q k).rename (Sum.map id (fun j => Sum.inr (Sum.inr j)))
  | .mul p q, Sum.inl _ =>
      .var (Sum.inr (Sum.inl 0)) - .var (Sum.inr (Sum.inr (Sum.inl (root p)))) * .var (Sum.inr (Sum.inr (Sum.inr (root q))))
  | .mul p _, Sum.inr (Sum.inl k) =>
      (residualSyntax p k).rename (Sum.map id (fun j => Sum.inr (Sum.inl j)))
  | .mul _ q, Sum.inr (Sum.inr k) =>
      (residualSyntax q k).rename (Sum.map id (fun j => Sum.inr (Sum.inr j)))

noncomputable def residual (e : NatExpr σ) (k : Wire e) : MvPolynomial (σ ⊕ Wire e) ℤ :=
  (residualSyntax e k).toPolynomial

/-- Canonical natural values at all syntax nodes. -/
def values : (e : NatExpr σ) → (σ → ℕ) → Wire e → ℕ
  | .constant n, _, _ => n
  | .var i, v, _ => v i
  | .add p q, v, Sum.inl _ => p.eval v + q.eval v
  | .add p _, v, Sum.inr (Sum.inl k) => values p v k
  | .add _ q, v, Sum.inr (Sum.inr k) => values q v k
  | .mul p q, v, Sum.inl _ => p.eval v * q.eval v
  | .mul p _, v, Sum.inr (Sum.inl k) => values p v k
  | .mul _ q, v, Sum.inr (Sum.inr k) => values q v k

@[simp] theorem values_root (e : NatExpr σ) (v : σ → ℕ) : values e v (root e) = e.eval v := by
  cases e <;> rfl

private theorem assignment_comp {τ ι : Type*} (v : σ → ℕ) (w : τ → ℕ) (f : ι → τ) :
    natAssignment v w ∘ Sum.map id f = natAssignment v (fun i => w (f i)) := by
  funext i
  cases i <;> rfl

/-- The explicit node evaluation satisfies every gate residual. -/
theorem complete (e : NatExpr σ) (v : σ → ℕ) :
    ∀ k : Wire e, (residualSyntax e k).eval (natAssignment v (values e v)) = 0 := by
  induction e with
  | constant n => intro k; simp [residualSyntax, Expr.eval, natAssignment, values]
  | var i => intro k; simp [residualSyntax, Expr.eval, natAssignment, values]
  | add p q hp hq | mul p q hp hq =>
      intro k
      cases k with
      | inl j => simp [residualSyntax, Expr.eval, natAssignment, values, values_root]
      | inr k =>
          cases k with
          | inl k => simpa [residualSyntax, Expr.eval_rename, assignment_comp, values] using hp k
          | inr k => simpa [residualSyntax, Expr.eval_rename, assignment_comp, values] using hq k

/-- Every satisfying natural gate assignment has the intended root value. -/
theorem sound (e : NatExpr σ) (v : σ → ℕ) (w : Wire e → ℕ)
    (h : ∀ k, (residualSyntax e k).eval (natAssignment v w) = 0) :
    w (root e) = e.eval v := by
  induction e with
  | constant n =>
      have hh := h 0
      change (w 0 : ℤ) - (n : ℤ) = 0 at hh
      exact_mod_cast sub_eq_zero.mp hh
  | var i =>
      have hh := h 0
      change (w 0 : ℤ) - (v i : ℤ) = 0 at hh
      exact_mod_cast sub_eq_zero.mp hh
  | add p q hp hq =>
      have hleft : ∀ k, (residualSyntax p k).eval
          (natAssignment v (fun j => w (Sum.inr (Sum.inl j)))) = 0 := by
        intro k
        simpa [residualSyntax, Expr.eval_rename, assignment_comp] using h (Sum.inr (Sum.inl k))
      have hright : ∀ k, (residualSyntax q k).eval
          (natAssignment v (fun j => w (Sum.inr (Sum.inr j)))) = 0 := by
        intro k
        simpa [residualSyntax, Expr.eval_rename, assignment_comp] using h (Sum.inr (Sum.inr k))
      have hl := hp (fun j => w (Sum.inr (Sum.inl j))) hleft
      have hr := hq (fun j => w (Sum.inr (Sum.inr j))) hright
      have hh := h (Sum.inl 0)
      change (w (Sum.inl 0) : ℤ) - ((w (Sum.inr (Sum.inl (root p))) : ℤ) + w (Sum.inr (Sum.inr (root q)))) = 0 at hh
      change w (Sum.inl 0) = p.eval v + q.eval v
      rw [← hl, ← hr]
      exact_mod_cast sub_eq_zero.mp hh
  | mul p q hp hq =>
      have hleft : ∀ k, (residualSyntax p k).eval
          (natAssignment v (fun j => w (Sum.inr (Sum.inl j)))) = 0 := by
        intro k
        simpa [residualSyntax, Expr.eval_rename, assignment_comp] using h (Sum.inr (Sum.inl k))
      have hright : ∀ k, (residualSyntax q k).eval
          (natAssignment v (fun j => w (Sum.inr (Sum.inr j)))) = 0 := by
        intro k
        simpa [residualSyntax, Expr.eval_rename, assignment_comp] using h (Sum.inr (Sum.inr k))
      have hl := hp (fun j => w (Sum.inr (Sum.inl j))) hleft
      have hr := hq (fun j => w (Sum.inr (Sum.inr j))) hright
      have hh := h (Sum.inl 0)
      change (w (Sum.inl 0) : ℤ) - ((w (Sum.inr (Sum.inl (root p))) : ℤ) * w (Sum.inr (Sum.inr (root q)))) = 0 at hh
      change w (Sum.inl 0) = p.eval v * q.eval v
      rw [← hl, ← hr]
      exact_mod_cast sub_eq_zero.mp hh

theorem polynomial_rename {σ τ : Type*} (e : Expr σ) (f : σ → τ) :
    (e.rename f).toPolynomial = MvPolynomial.rename f e.toPolynomial := by
  induction e <;> simp_all [Expr.rename, Expr.toPolynomial]

private theorem degree_sub {α : Type*} {p q : MvPolynomial α ℤ} {d : ℕ}
    (hp : p.totalDegree ≤ d) (hq : q.totalDegree ≤ d) : (p - q).totalDegree ≤ d :=
  (MvPolynomial.totalDegree_sub p q).trans (max_le hp hq)

private theorem degree_add {α : Type*} {p q : MvPolynomial α ℤ} {d : ℕ}
    (hp : p.totalDegree ≤ d) (hq : q.totalDegree ≤ d) : (p + q).totalDegree ≤ d :=
  (MvPolynomial.totalDegree_add p q).trans (max_le hp hq)

/-- Every stored gate equation is quadratic, irrespective of the input expression's degree. -/
theorem residual_degree (e : NatExpr σ) : ∀ k, (residual e k).totalDegree ≤ 2 := by
  induction e with
  | constant n =>
      intro k
      change ((MvPolynomial.X (Sum.inr 0) : MvPolynomial (σ ⊕ Fin 1) ℤ) - MvPolynomial.C (n : ℤ)).totalDegree ≤ 2
      exact degree_sub (by simp) (by rw [MvPolynomial.totalDegree_C]; omega)
  | var i =>
      intro k
      change ((MvPolynomial.X (Sum.inr 0) : MvPolynomial (σ ⊕ Fin 1) ℤ) - MvPolynomial.X (Sum.inl i)).totalDegree ≤ 2
      exact degree_sub (by simp) (by simp)
  | add p q hp hq =>
      intro k
      cases k with
      | inl j =>
          change ((MvPolynomial.X (Sum.inr (Sum.inl 0)) : MvPolynomial (σ ⊕ Wire (.add p q)) ℤ) -
            (MvPolynomial.X (Sum.inr (Sum.inr (Sum.inl (root p)))) + MvPolynomial.X (Sum.inr (Sum.inr (Sum.inr (root q)))))).totalDegree ≤ 2
          exact degree_sub (by simp) (degree_add (by simp) (by simp))
      | inr k =>
          cases k with
          | inl k =>
              simpa only [residual, residualSyntax, polynomial_rename] using
                (MvPolynomial.totalDegree_rename_le _ (residual p k)).trans (hp k)
          | inr k =>
              simpa only [residual, residualSyntax, polynomial_rename] using
                (MvPolynomial.totalDegree_rename_le _ (residual q k)).trans (hq k)
  | mul p q hp hq =>
      intro k
      cases k with
      | inl j =>
          change ((MvPolynomial.X (Sum.inr (Sum.inl 0)) : MvPolynomial (σ ⊕ Wire (.mul p q)) ℤ) -
            MvPolynomial.X (Sum.inr (Sum.inr (Sum.inl (root p)))) * MvPolynomial.X (Sum.inr (Sum.inr (Sum.inr (root q))))).totalDegree ≤ 2
          apply degree_sub (by simp)
          exact (MvPolynomial.totalDegree_mul _ _).trans (by simp)
      | inr k =>
          cases k with
          | inl k =>
              simpa only [residual, residualSyntax, polynomial_rename] using
                (MvPolynomial.totalDegree_rename_le _ (residual p k)).trans (hp k)
          | inr k =>
              simpa only [residual, residualSyntax, polynomial_rename] using
                (MvPolynomial.totalDegree_rename_le _ (residual q k)).trans (hq k)

end Gates

private def sumIndex {A B : Type*} {a b : ℕ} (f : A ≃ Fin a) (g : B ≃ Fin b) :
    A ⊕ B ≃ Fin (a + b) := (Equiv.sumCongr f g).trans finSumFinEquiv

/-- Original witnesses, left-tree nodes, right-tree nodes, and one normalization guard. -/
abbrev Witness {m : ℕ} (p q : NatExpr (Empty ⊕ Fin m)) :=
  Fin m ⊕ (Gates.Wire p ⊕ (Gates.Wire q ⊕ Fin 1))

/-- Guard, left-tree gates, right-tree gates, and equality of the two outputs. -/
abbrev Equation {m : ℕ} (p q : NatExpr (Empty ⊕ Fin m)) :=
  Fin 1 ⊕ (Gates.Wire p ⊕ (Gates.Wire q ⊕ Fin 1))

def witnessCount {m : ℕ} (p q : NatExpr (Empty ⊕ Fin m)) : ℕ :=
  m + (Gates.count p + (Gates.count q + 1))

def witnessIndex {m : ℕ} (p q : NatExpr (Empty ⊕ Fin m)) :
    Witness p q ≃ Fin (witnessCount p q) :=
  sumIndex (Equiv.refl (Fin m))
    (sumIndex (Gates.index p) (sumIndex (Gates.index q) (Equiv.refl (Fin 1))))

def coordinate {m : ℕ} (p q : NatExpr (Empty ⊕ Fin m)) :
    Option (Witness p q) ≃ Fin (witnessCount p q + 1) :=
  (Equiv.optionCongr (witnessIndex p q)).trans (finSuccEquiv (witnessCount p q)).symm

@[simp] theorem coordinate_none {m : ℕ} (p q : NatExpr (Empty ⊕ Fin m)) :
    coordinate p q none = 0 := by simp [coordinate]

private def initial {m : ℕ} {p q : NatExpr (Empty ⊕ Fin m)} :
    Empty ⊕ Fin m → Option (Witness p q) := Sum.elim Empty.elim (fun i => some (Sum.inl i))

private def leftEmbedding {m : ℕ} (p q : NatExpr (Empty ⊕ Fin m)) :
    (Empty ⊕ Fin m) ⊕ Gates.Wire p → Option (Witness p q) :=
  Sum.elim initial (fun i => some (Sum.inr (Sum.inl i)))

private def rightEmbedding {m : ℕ} (p q : NatExpr (Empty ⊕ Fin m)) :
    (Empty ⊕ Fin m) ⊕ Gates.Wire q → Option (Witness p q) :=
  Sum.elim initial (fun i => some (Sum.inr (Sum.inr (Sum.inl i))))

/-- Complete finite code for the quadratic residual system. -/
def residualSyntax {m : ℕ} (p q : NatExpr (Empty ⊕ Fin m)) :
    Equation p q → Expr (Option (Witness p q))
  | Sum.inl _ => .var (some (Sum.inr (Sum.inr (Sum.inr 0)))) - 1
  | Sum.inr (Sum.inl k) => (Gates.residualSyntax p k).rename (leftEmbedding p q)
  | Sum.inr (Sum.inr (Sum.inl k)) => (Gates.residualSyntax q k).rename (rightEmbedding p q)
  | Sum.inr (Sum.inr (Sum.inr _)) =>
      .var (some (Sum.inr (Sum.inl (Gates.root p)))) - .var (some (Sum.inr (Sum.inr (Sum.inl (Gates.root q)))))

noncomputable def residual {m : ℕ} (p q : NatExpr (Empty ⊕ Fin m)) (i : Equation p q) :
    MvPolynomial (Option (Witness p q)) ℤ := (residualSyntax p q i).toPolynomial

noncomputable def sumSquares {m : ℕ} (p q : NatExpr (Empty ⊕ Fin m)) :
    MvPolynomial (Option (Witness p q)) ℤ := ∑ i : Equation p q, residual p q i ^ 2

theorem residual_degree {m : ℕ} (p q : NatExpr (Empty ⊕ Fin m)) (i : Equation p q) :
    (residual p q i).totalDegree ≤ 2 := by
  cases i with
  | inl i =>
      change ((MvPolynomial.X (some (Sum.inr (Sum.inr (Sum.inr 0)))) : MvPolynomial (Option (Witness p q)) ℤ) - MvPolynomial.C 1).totalDegree ≤ 2
      exact (MvPolynomial.totalDegree_sub _ _).trans (by simp)
  | inr i =>
      cases i with
      | inl k =>
          simpa only [residual, residualSyntax, Gates.polynomial_rename, Gates.residual] using
            (MvPolynomial.totalDegree_rename_le _ (Gates.residual p k)).trans (Gates.residual_degree p k)
      | inr i =>
          cases i with
          | inl k =>
              simpa only [residual, residualSyntax, Gates.polynomial_rename, Gates.residual] using
                (MvPolynomial.totalDegree_rename_le _ (Gates.residual q k)).trans (Gates.residual_degree q k)
          | inr i =>
              change ((MvPolynomial.X (some (Sum.inr (Sum.inl (Gates.root p)))) : MvPolynomial (Option (Witness p q)) ℤ) -
                MvPolynomial.X (some (Sum.inr (Sum.inr (Sum.inl (Gates.root q)))))).totalDegree ≤ 2
              exact (MvPolynomial.totalDegree_sub _ _).trans (by simp)

theorem sumSquares_degree {m : ℕ} (p q : NatExpr (Empty ⊕ Fin m)) :
    (sumSquares p q).totalDegree ≤ 4 :=
  Diophantine.totalDegree_sum_pow_le Finset.univ (residual p q) 2 2
    (fun i _ => residual_degree p q i)

/-- The distinguished input is present in the polynomial type and ignored by every residual. -/
def assignment {m : ℕ} {p q : NatExpr (Empty ⊕ Fin m)} (x : ℤ) (w : Witness p q → ℕ) :
    Option (Witness p q) → ℤ
  | none => x
  | some i => w i

private theorem assignment_left {m : ℕ} (p q : NatExpr (Empty ⊕ Fin m)) (x : ℤ)
    (w : Witness p q → ℕ) :
    assignment x w ∘ leftEmbedding p q =
      natAssignment (Sum.elim Empty.elim (fun i => w (Sum.inl i))) (fun i => w (Sum.inr (Sum.inl i))) := by
  funext i
  cases i with
  | inl i => cases i with
      | inl i => exact i.elim
      | inr i => rfl
  | inr i => rfl

private theorem assignment_right {m : ℕ} (p q : NatExpr (Empty ⊕ Fin m)) (x : ℤ)
    (w : Witness p q → ℕ) :
    assignment x w ∘ rightEmbedding p q =
      natAssignment (Sum.elim Empty.elim (fun i => w (Sum.inl i))) (fun i => w (Sum.inr (Sum.inr (Sum.inl i)))) := by
  funext i
  cases i with
  | inl i => cases i with
      | inl i => exact i.elim
      | inr i => rfl
  | inr i => rfl

theorem eval_sumSquares_zero_iff {m : ℕ} (p q : NatExpr (Empty ⊕ Fin m))
    (a : Option (Witness p q) → ℤ) :
    MvPolynomial.eval a (sumSquares p q) = 0 ↔
      ∀ i, (residualSyntax p q i).eval a = 0 := by
  simp only [sumSquares, MvPolynomial.eval_sum, MvPolynomial.eval_pow,
    residual, Expr.eval_toPolynomial]
  simpa only [pow_two, Finset.mem_univ, forall_true_left] using
    (Finset.sum_mul_self_eq_zero_iff (Finset.univ : Finset (Equation p q))
      (fun i => (residualSyntax p q i).eval a))

/-- Given original witnesses, supply all gate nodes and set the guard to one. -/
def witnesses {m : ℕ} (p q : NatExpr (Empty ⊕ Fin m)) (v : Fin m → ℕ) : Witness p q → ℕ
  | Sum.inl i => v i
  | Sum.inr (Sum.inl i) => Gates.values p (Sum.elim Empty.elim v) i
  | Sum.inr (Sum.inr (Sum.inl i)) => Gates.values q (Sum.elim Empty.elim v) i
  | Sum.inr (Sum.inr (Sum.inr _)) => 1

theorem exists_sumSquares_iff {m : ℕ} (p q : NatExpr (Empty ⊕ Fin m)) (x : ℤ) :
    (∃ w : Witness p q → ℕ, MvPolynomial.eval (assignment x w) (sumSquares p q) = 0) ↔
      ∃ v : Fin m → ℕ, p.eval (Sum.elim Empty.elim v) = q.eval (Sum.elim Empty.elim v) := by
  constructor
  · rintro ⟨w, hw⟩
    have h := (eval_sumSquares_zero_iff p q (assignment x w)).mp hw
    have hl : ∀ k, (Gates.residualSyntax p k).eval
        (natAssignment (Sum.elim Empty.elim (fun i => w (Sum.inl i))) (fun i => w (Sum.inr (Sum.inl i)))) = 0 := by
      intro k
      simpa only [residualSyntax, Expr.eval_rename, assignment_left] using h (Sum.inr (Sum.inl k))
    have hr : ∀ k, (Gates.residualSyntax q k).eval
        (natAssignment (Sum.elim Empty.elim (fun i => w (Sum.inl i))) (fun i => w (Sum.inr (Sum.inr (Sum.inl i))))) = 0 := by
      intro k
      simpa only [residualSyntax, Expr.eval_rename, assignment_right] using h (Sum.inr (Sum.inr (Sum.inl k)))
    have hout := h (Sum.inr (Sum.inr (Sum.inr 0)))
    change (w (Sum.inr (Sum.inl (Gates.root p))) : ℤ) - w (Sum.inr (Sum.inr (Sum.inl (Gates.root q)))) = 0 at hout
    have houtNat : w (Sum.inr (Sum.inl (Gates.root p))) = w (Sum.inr (Sum.inr (Sum.inl (Gates.root q)))) := by
      exact_mod_cast sub_eq_zero.mp hout
    refine ⟨fun i => w (Sum.inl i), ?_⟩
    exact (Gates.sound p _ _ hl).symm.trans (houtNat.trans (Gates.sound q _ _ hr))
  · rintro ⟨v, hv⟩
    refine ⟨witnesses p q v, (eval_sumSquares_zero_iff p q _).mpr ?_⟩
    intro i
    cases i with
    | inl i => simp [residualSyntax, Expr.eval, assignment, witnesses]
    | inr i =>
        cases i with
        | inl k =>
            simpa only [residualSyntax, Expr.eval_rename, assignment_left, witnesses] using Gates.complete p (Sum.elim Empty.elim v) k
        | inr i =>
            cases i with
            | inl k =>
                simpa only [residualSyntax, Expr.eval_rename, assignment_right, witnesses] using Gates.complete q (Sum.elim Empty.elim v) k
            | inr i => simp [residualSyntax, Expr.eval, assignment, witnesses, Gates.values_root, hv]

/-- The guard makes the quartic nonzero at the zero witness tuple, even for integer input. -/
theorem sumSquares_normalized {m : ℕ} (p q : NatExpr (Empty ⊕ Fin m)) (x : ℤ) :
    MvPolynomial.eval (assignment x (fun _ => 0)) (sumSquares p q) ≠ 0 := by
  intro h
  have hg := (eval_sumSquares_zero_iff p q _).mp h (Sum.inl 0)
  norm_num [residualSyntax, Expr.eval, assignment] at hg

/-- Standard-coordinate polynomial, retaining input coordinate zero. -/
noncomputable def quartic {m : ℕ} (p q : NatExpr (Empty ⊕ Fin m)) :
    MvPolynomial (Fin (witnessCount p q + 1)) ℤ :=
  MvPolynomial.rename (coordinate p q) (sumSquares p q)

theorem quartic_degree {m : ℕ} (p q : NatExpr (Empty ⊕ Fin m)) :
    (quartic p q).totalDegree ≤ 4 :=
  (MvPolynomial.totalDegree_rename_le _ _).trans (sumSquares_degree p q)

theorem wset_quartic_iff {m : ℕ} (p q : NatExpr (Empty ⊕ Fin m)) (x : ℕ) :
    Wset (quartic p q) x ↔
      ∃ v : Fin m → ℕ, p.eval (Sum.elim Empty.elim v) = q.eval (Sum.elim Empty.elim v) := by
  rw [← exists_sumSquares_iff p q (x : ℤ)]
  have h := Diophantine.exists_eval_rename_option_iff (coordinate p q) (sumSquares p q)
    (fun value : ℕ => (value : ℤ)) x 0
  simp only [coordinate_none, Function.comp_def] at h
  refine h.trans ?_
  apply exists_congr
  intro v
  apply Iff.of_eq
  apply congrArg (fun a : Option (Witness p q) → ℤ => MvPolynomial.eval a (sumSquares p q) = 0)
  funext i
  cases i <;> rfl

theorem quartic_normalized {m : ℕ} (p q : NatExpr (Empty ⊕ Fin m)) :
    Normalized (quartic p q) := by
  intro x
  have h := Diophantine.eval_rename_zeroWitnesses (coordinate p q) (sumSquares p q) (x : ℤ)
  simp only [coordinate_none] at h
  change MvPolynomial.eval _ (MvPolynomial.rename (coordinate p q) (sumSquares p q)) ≠ 0
  rw [h]
  refine (congrArg (fun a : Option (Witness p q) → ℤ => MvPolynomial.eval a (sumSquares p q) ≠ 0) ?_).mp
    (sumSquares_normalized p q (x : ℤ))
  funext i
  cases i <;> rfl

/-- Explicit normalized quartic data ready for the choice-free Jones finalizer. -/
structure Result (A : Prop) where
  ν : ℕ
  positive : 1 ≤ ν
  polynomial : MvPolynomial (Fin (ν + 1)) ℤ
  degree : polynomial.totalDegree ≤ 4
  normalized : Normalized polynomial
  correct : ∀ x : ℕ, Wset polynomial x ↔ A

/-- Compile the supplied representation data, using its own syntax and witnesses. -/
noncomputable def compile {A : Prop} (r : Rep Empty (fun _ => A)) : Result A :=
  let p := r.expression.splitNatural.1
  let q := r.expression.splitNatural.2
  { ν := witnessCount p q
    positive := by dsimp only [witnessCount]; omega
    polynomial := quartic p q
    degree := quartic_degree p q
    normalized := quartic_normalized p q
    correct := fun x => (wset_quartic_iff p q x).trans (r.correct_splitNatural Empty.elim).symm }

#print axioms compile

end DiophantineConsistency.QuarticCompiler
