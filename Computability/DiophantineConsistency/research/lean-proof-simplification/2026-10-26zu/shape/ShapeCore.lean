import Lean.Elab.Tactic.Omega

/-! Generated from exact pinned declarations; see ShapeCore.manifest.json. -/


namespace DiophantineConsistency


/- Extracted: Representation.Expr. -/
inductive Expr (σ : Type _)
  | constant (value : Int)
  | var (index : σ)
  | add (left right : Expr σ)
  | sub (left right : Expr σ)
  | mul (left right : Expr σ)
  deriving Repr, DecidableEq


/- Extracted: NaturalExpression.NatExpr. -/
inductive NatExpr (σ : Type _)
  | constant (value : Nat)
  | var (index : σ)
  | add (left right : NatExpr σ)
  | mul (left right : NatExpr σ)
  deriving Repr, DecidableEq


namespace NatExpr
variable {σ : Type _}


/- Extracted: NaturalExpression.NatExpr instances. -/
instance (n : Nat) : OfNat (NatExpr σ) n := ⟨constant n⟩
instance : Add (NatExpr σ) := ⟨add⟩
instance : Mul (NatExpr σ) := ⟨mul⟩


end NatExpr
namespace Expr
variable {σ : Type _}


/- Extracted: NaturalExpression.Expr.splitNatural. -/
def splitNatural : Expr σ → NatExpr σ × NatExpr σ
  | .constant a => (.constant a.toNat, .constant (-a).toNat)
  | .var i => (.var i, 0)
  | .add p q =>
      let a := p.splitNatural
      let b := q.splitNatural
      (a.1 + b.1, a.2 + b.2)
  | .sub p q =>
      let a := p.splitNatural
      let b := q.splitNatural
      (a.1 + b.2, a.2 + b.1)
  | .mul p q =>
      let a := p.splitNatural
      let b := q.splitNatural
      (a.1 * b.1 + a.2 * b.2, a.1 * b.2 + a.2 * b.1)


end Expr
namespace QuarticCompiler.Gates
variable {σ : Type _}


/- Extracted: QuarticCompiler.Gates.count. -/
def count : NatExpr σ → Nat
  | .constant _ => 1
  | .var _ => 1
  | .add p q => 1 + (count p + count q)
  | .mul p q => 1 + (count p + count q)


end QuarticCompiler.Gates
namespace NatExpr


/- Extracted: RepresentationSize.NatExpr.depth. -/
def depth {σ : Type _} : NatExpr σ → Nat
  | .constant _ | .var _ => 0
  | .add p q | .mul p q => 1 + max p.depth q.depth


end NatExpr
namespace ExpressionSize


/- Extracted: ExpressionSize.SplitSize and operations. -/
structure SplitSize where
  positive : Nat
  negative : Nat
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


namespace Legacy


/- Extracted: original ExpressionSize.splitSize (namespace-isolated). -/
def splitSize {σ : Type _} : Expr σ → SplitSize
  | .constant _ => .leaf
  | .var _ => .leaf
  | .add p q => .add (splitSize p) (splitSize q)
  | .sub p q => .sub (splitSize p) (splitSize q)
  | .mul p q => .mul (splitSize p) (splitSize q)


end Legacy


/- Extracted: candidate ExpressionSize.halfSize and splitSize. -/
def halfSize {σ : Type _} : Expr σ → Nat
  | .constant _ | .var _ => 1
  | .add p q | .sub p q => 1 + halfSize p + halfSize q
  | .mul p q => 3 + 2 * halfSize p + 2 * halfSize q

/-- Raw signed splitting reaches only the diagonal of `SplitSize`. -/
def splitSize {σ : Type _} (e : Expr σ) : SplitSize :=
  ⟨halfSize e, halfSize e⟩


/- Extracted: candidate ExpressionSize.splitSize_correct. -/
theorem splitSize_correct {σ : Type _} (e : Expr σ) :
    QuarticCompiler.Gates.count e.splitNatural.1 = (splitSize e).positive ∧
    QuarticCompiler.Gates.count e.splitNatural.2 = (splitSize e).negative := by
  induction e <;>
    simp_all [splitSize, halfSize, Expr.splitNatural, QuarticCompiler.Gates.count] <;> omega


end ExpressionSize
end DiophantineConsistency


/- Extracted: candidate SplitShape declarations and proofs. -/
namespace DiophantineConsistency

namespace NatExpr

def shapeFold {σ : Type _} {A : Type _} (leaf : A)
    (add mul : A → A → A) : NatExpr σ → A
  | .constant _ | .var _ => leaf
  | .add p q => add (shapeFold leaf add mul p) (shapeFold leaf add mul q)
  | .mul p q => mul (shapeFold leaf add mul p) (shapeFold leaf add mul q)

def eraseLeaves {σ : Type _} (e : NatExpr σ) : NatExpr Empty :=
  shapeFold (.constant 0) .add .mul e

end NatExpr

namespace Expr

theorem splitNatural_shapeFold_eq {σ A : Type _} (leaf : A)
    (add mul : A → A → A) (e : Expr σ) :
    NatExpr.shapeFold leaf add mul e.splitNatural.1 =
      NatExpr.shapeFold leaf add mul e.splitNatural.2 := by
  induction e <;> simp_all [splitNatural, NatExpr.shapeFold]

theorem splitNatural_eraseLeaves_eq {σ : Type _} (e : Expr σ) :
    NatExpr.eraseLeaves e.splitNatural.1 = NatExpr.eraseLeaves e.splitNatural.2 := by
  simpa only [NatExpr.eraseLeaves] using
    (splitNatural_shapeFold_eq (A := NatExpr Empty) (NatExpr.constant 0)
      NatExpr.add NatExpr.mul e)

end Expr

#print axioms Expr.splitNatural_shapeFold_eq
#print axioms Expr.splitNatural_eraseLeaves_eq

end DiophantineConsistency


namespace DiophantineConsistency

namespace NatExpr

theorem shapeFold_count {σ : Type _} (e : NatExpr σ) :
    shapeFold (1 : Nat) (fun a b => 1 + (a + b))
      (fun a b => 1 + (a + b)) e = QuarticCompiler.Gates.count e := by
  induction e <;> simp_all [shapeFold, QuarticCompiler.Gates.count]

theorem shapeFold_depth {σ : Type _} (e : NatExpr σ) :
    shapeFold (0 : Nat) (fun a b => 1 + max a b)
      (fun a b => 1 + max a b) e = depth e := by
  induction e <;> simp_all [shapeFold, depth]

end NatExpr

namespace Expr

theorem splitNatural_count_eq {σ : Type _} (e : Expr σ) :
    QuarticCompiler.Gates.count e.splitNatural.1 =
      QuarticCompiler.Gates.count e.splitNatural.2 := by
  simpa only [NatExpr.shapeFold_count] using
    splitNatural_shapeFold_eq (1 : Nat) (fun a b => 1 + (a + b))
      (fun a b => 1 + (a + b)) e

theorem splitNatural_depth_eq {σ : Type _} (e : Expr σ) :
    NatExpr.depth e.splitNatural.1 = NatExpr.depth e.splitNatural.2 := by
  simpa only [NatExpr.shapeFold_depth] using
    splitNatural_shapeFold_eq (0 : Nat) (fun a b => 1 + max a b)
      (fun a b => 1 + max a b) e

end Expr

namespace ExpressionSize

theorem legacy_splitSize_diagonal {σ : Type _} (e : Expr σ) :
    Legacy.splitSize e = ⟨halfSize e, halfSize e⟩ := by
  induction e with
  | constant a => rfl
  | var i => rfl
  | add p q hp hq =>
    simp only [Legacy.splitSize, hp, hq, SplitSize.add, halfSize]
  | sub p q hp hq =>
    simp only [Legacy.splitSize, hp, hq, SplitSize.sub, halfSize]
  | mul p q hp hq =>
    simp only [Legacy.splitSize, hp, hq, SplitSize.mul, halfSize]
    congr 1 <;> omega

theorem splitSize_eq_legacy {σ : Type _} (e : Expr σ) :
    splitSize e = Legacy.splitSize e :=
  (legacy_splitSize_diagonal e).symm

theorem splitSize_positive_eq_negative {σ : Type _} (e : Expr σ) :
    (splitSize e).positive = (splitSize e).negative := rfl

end ExpressionSize

example : QuarticCompiler.Gates.count
    (Expr.mul (Expr.var ()) (Expr.var ())).splitNatural.1 = 7 := rfl
example : QuarticCompiler.Gates.count
    (Expr.mul (Expr.var ()) (Expr.var ())).splitNatural.2 = 7 := rfl

-- A raw-shape theorem cannot alone identify separately simplified trees.
-- These are only the indicated normal-form shapes; the actual simplify
-- implementation has not been extracted or asserted to produce them here.
example : QuarticCompiler.Gates.count
      (NatExpr.mul (NatExpr.var ()) (NatExpr.var ())) !=
    QuarticCompiler.Gates.count (NatExpr.constant (σ := Unit) 0) := by decide

#print axioms Expr.splitNatural_count_eq
#print axioms Expr.splitNatural_depth_eq
#print axioms ExpressionSize.splitSize_correct
#print axioms ExpressionSize.legacy_splitSize_diagonal
#print axioms ExpressionSize.splitSize_eq_legacy
#print axioms ExpressionSize.splitSize_positive_eq_negative

end DiophantineConsistency
