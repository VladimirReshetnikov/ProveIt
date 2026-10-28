import DiophantineConsistency.QuarticCompiler

/-!
# Checked size folds without constructing the two natural expressions

The positive and negative syntax sizes can be calculated by integer
arithmetic on child metadata. This avoids materializing `splitNatural`.
-/

namespace DiophantineConsistency.ExpressionSize

structure SplitSize where
  positive : ℕ
  negative : ℕ
  deriving Repr, DecidableEq

namespace SplitSize

def leaf : SplitSize := ⟨1, 1⟩
def add (a b : SplitSize) : SplitSize :=
  ⟨1 + a.positive + b.positive, 1 + a.negative + b.negative⟩
def sub (a b : SplitSize) : SplitSize :=
  ⟨1 + a.positive + b.negative, 1 + a.negative + b.positive⟩
def mul (a b : SplitSize) : SplitSize :=
  let n := a.positive + a.negative + b.positive + b.negative + 3
  ⟨n, n⟩
def conjunction (a b : SplitSize) : SplitSize := add (mul a a) (mul b b)

end SplitSize

/-- Structural size interpretation; its values do not depend on coefficients. -/
def splitSize {σ : Type*} : Expr σ → SplitSize
  | .constant _ => .leaf
  | .var _ => .leaf
  | .add p q => .add (splitSize p) (splitSize q)
  | .sub p q => .sub (splitSize p) (splitSize q)
  | .mul p q => .mul (splitSize p) (splitSize q)

theorem splitSize_correct {σ : Type*} (e : Expr σ) :
    QuarticCompiler.Gates.count e.splitNatural.1 = (splitSize e).positive ∧
    QuarticCompiler.Gates.count e.splitNatural.2 = (splitSize e).negative := by
  induction e <;>
    simp_all only [Expr.splitNatural, QuarticCompiler.Gates.count, splitSize, SplitSize.leaf,
      SplitSize.add, SplitSize.sub, SplitSize.mul, and_self] <;> constructor <;> omega

@[simp] theorem splitSize_rename {σ τ : Type*} (e : Expr σ) (f : σ → τ) :
    splitSize (e.rename f) = splitSize e := by
  induction e <;> simp_all [Expr.rename, splitSize]

theorem graphAdd_witnessCount {σ : Type*} {f g : (σ → ℕ) → ℕ}
    (r : GraphRep f) (s : GraphRep g) :
    (r.add s).witnessCount = r.witnessCount + s.witnessCount + 2 := by
  change 1 + ((1 + (0 + s.witnessCount)) + r.witnessCount) = _
  omega

theorem graphMul_witnessCount {σ : Type*} {f g : (σ → ℕ) → ℕ}
    (r : GraphRep f) (s : GraphRep g) :
    (r.mul s).witnessCount = r.witnessCount + s.witnessCount + 2 := by
  change 1 + ((1 + (0 + s.witnessCount)) + r.witnessCount) = _
  omega

/-- The existing natural-expression graph compiler allocates two witnesses
per internal node. This identity needs no expanded graph expression. -/
theorem natGraph_witnessCount {σ : Type*} (e : NatExpr σ) :
    e.graphRep.witnessCount + 1 = QuarticCompiler.Gates.count e := by
  induction e with
  | constant n => rfl
  | var i => rfl
  | add p q hp hq =>
    change (p.graphRep.add q.graphRep).witnessCount + 1 =
      1 + (QuarticCompiler.Gates.count p + QuarticCompiler.Gates.count q)
    rw [graphAdd_witnessCount, ← hp, ← hq]
    omega
  | mul p q hp hq =>
    change (p.graphRep.mul q.graphRep).witnessCount + 1 =
      1 + (QuarticCompiler.Gates.count p + QuarticCompiler.Gates.count q)
    rw [graphMul_witnessCount, ← hp, ← hq]
    omega

end DiophantineConsistency.ExpressionSize
