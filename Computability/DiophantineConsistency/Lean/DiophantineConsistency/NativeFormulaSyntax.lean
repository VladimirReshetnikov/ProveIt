import DiophantineConsistency.CantorRepresentation
import DiophantineConsistency.NaturalExpression

/-! # Natural polynomial syntax for the enumerator's formula constructors -/

namespace DiophantineConsistency.NativeFormulaSyntax

open SetTheory SetTheory.BusyBeaver.ZFC.Code254 SetTheory.BusyBeaver.ZFC.KCode222

variable {σ : Type*}

/-- Clearing the fixed factor in `4*P` gives a natural polynomial directly. -/
def implication (a b : NatExpr σ) : NatExpr σ :=
  2 * (a + b) * (a + b + 1) + 4 * b

@[simp] theorem eval_implication (a b : NatExpr σ) (v : σ → ℕ) :
    (implication a b).eval v = wim (a.eval v) (b.eval v) := by
  simp only [implication, NatExpr.eval, wim]
  calc
    _ = 2 * ((a.eval v + b.eval v) * (a.eval v + b.eval v + 1) + 2 * b.eval v) := by ring
    _ = 2 * (2 * P (a.eval v) (b.eval v)) := by rw [CantorRepresentation.two_pair]
    _ = _ := by ring

def membership (a b : NatExpr σ) : NatExpr σ := implication a b + 1
def universal (a b : NatExpr σ) : NatExpr σ := implication a b + 2
def equality (a b : NatExpr σ) : NatExpr σ := implication a b + 3
def negation (a : NatExpr σ) : NatExpr σ := implication a 1
def existential (a b : NatExpr σ) : NatExpr σ := negation (universal a (negation b))

@[simp] theorem eval_membership (a b : NatExpr σ) (v : σ → ℕ) :
    (membership a b).eval v = wel (a.eval v) (b.eval v) := by
  simp [membership, wel, wim, NatExpr.eval]
@[simp] theorem eval_universal (a b : NatExpr σ) (v : σ → ℕ) :
    (universal a b).eval v = wal (a.eval v) (b.eval v) := by
  simp [universal, wal, wim, NatExpr.eval]
@[simp] theorem eval_equality (a b : NatExpr σ) (v : σ → ℕ) :
    (equality a b).eval v = weq (a.eval v) (b.eval v) := by
  simp [equality, weq, wim, NatExpr.eval]
@[simp] theorem eval_negation (a : NatExpr σ) (v : σ → ℕ) :
    (negation a).eval v = wn (a.eval v) := by simp [negation, wn, F, NatExpr.eval]
@[simp] theorem eval_existential (a b : NatExpr σ) (v : σ → ℕ) :
    (existential a b).eval v = wex (a.eval v) (b.eval v) := by simp [existential, wex]

def row1 (a b : NatExpr σ) : NatExpr σ := existential a (equality a b)
def row2 (a b c : NatExpr σ) : NatExpr σ :=
  implication (universal a (implication b c)) (implication (universal a b) (universal a c))
def row3 (a b c : NatExpr σ) : NatExpr σ :=
  implication (equality a b) (implication (membership c a) (membership c b))
def row4 (a b c : NatExpr σ) : NatExpr σ :=
  implication (universal a (universal b c)) (universal b (universal a c))
def row5 (a b c : NatExpr σ) : NatExpr σ :=
  implication (equality c a) (implication (membership c b) (membership a b))
def row6 (a b : NatExpr σ) : NatExpr σ :=
  implication (existential a (universal a b)) b
def growth (a b c : NatExpr σ) : NatExpr σ :=
  implication (equality c a) (implication (equality c b)
    (universal (membership a b) (equality a b)))
def request (b k m : NatExpr σ) : NatExpr σ :=
  universal b (implication m (negation (universal b
    (implication m (negation (membership b k))))))
def closure (a b k m : NatExpr σ) : NatExpr σ :=
  universal b (implication (membership b k) (negation (universal a
    (implication m (negation (universal a (implication
      (universal k (implication (membership k a) (membership k b)))
      (request b k m))))))))
def row8 (a b c u : NatExpr σ) : NatExpr σ :=
  implication (implication (implication c u) a)
    (implication (implication a c) (implication b c))
def bundle (a b c : NatExpr σ) : NatExpr σ :=
  negation (implication
    (implication (membership a b) (universal c (membership a b)))
    (universal c (implication (closure a b c c) (negation (request b c c)))))

@[simp] theorem eval_row1 (a b : NatExpr σ) (v : σ → ℕ) :
    (row1 a b).eval v = rho1 (a.eval v) (b.eval v) := by simp [row1, rho1]
@[simp] theorem eval_row2 (a b c : NatExpr σ) (v : σ → ℕ) :
    (row2 a b c).eval v = rho2 (a.eval v) (b.eval v) (c.eval v) := by simp [row2, rho2]
@[simp] theorem eval_row3 (a b c : NatExpr σ) (v : σ → ℕ) :
    (row3 a b c).eval v = rho3 (a.eval v) (b.eval v) (c.eval v) := by simp [row3, rho3]
@[simp] theorem eval_row4 (a b c : NatExpr σ) (v : σ → ℕ) :
    (row4 a b c).eval v = rho4 (a.eval v) (b.eval v) (c.eval v) := by simp [row4, rho4]
@[simp] theorem eval_row5 (a b c : NatExpr σ) (v : σ → ℕ) :
    (row5 a b c).eval v = rho5 (a.eval v) (b.eval v) (c.eval v) := by simp [row5, rho5]
@[simp] theorem eval_row6 (a b : NatExpr σ) (v : σ → ℕ) :
    (row6 a b).eval v = rho6 (a.eval v) (b.eval v) := by simp [row6, rho6]
@[simp] theorem eval_growth (a b c : NatExpr σ) (v : σ → ℕ) :
    (growth a b c).eval v = growG (a.eval v) (b.eval v) (c.eval v) := by simp [growth, growG]
@[simp] theorem eval_request (b k m : NatExpr σ) (v : σ → ℕ) :
    (request b k m).eval v = req (b.eval v) (k.eval v) (m.eval v) := by simp [request, req]
@[simp] theorem eval_closure (a b k m : NatExpr σ) (v : σ → ℕ) :
    (closure a b k m).eval v = clos (a.eval v) (b.eval v) (k.eval v) (m.eval v) := by
  simp [closure, clos]
@[simp] theorem eval_row8 (a b c u : NatExpr σ) (v : σ → ℕ) :
    (row8 a b c u).eval v = rho8 (a.eval v) (b.eval v) (c.eval v) (u.eval v) := by
  simp [row8, rho8]
@[simp] theorem eval_bundle (a b c : NatExpr σ) (v : σ → ℕ) :
    (bundle a b c).eval v = bundle222 (a.eval v) (b.eval v) (c.eval v) := by
  simp [bundle, bundle222, vrel, nks]

#print axioms eval_bundle

end DiophantineConsistency.NativeFormulaSyntax
