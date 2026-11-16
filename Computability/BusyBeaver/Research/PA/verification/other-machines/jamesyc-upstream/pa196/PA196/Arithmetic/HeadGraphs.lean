module
public import M6PA.Scheduler.ActualArithmeticGraph
public import PA196.Commands.Code
@[expose] public section

/-! Uniform Σ₁ graphs for the PA196 formula constructors and heads.
The expression language and its proved graph compiler are reused from PA209;
the formulas below are newly specified with the transposed quantifier and
equality-vacuity gate. No old head or gate is identified with a new one. -/
namespace PA196.Arithmetic.HeadGraphs
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open M6.PA.ActualArithmeticGraph

def im (x y : Expr) : Expr := .mul (.lit 4) (.pair x y)
def al (x y : Expr) : Expr := .add (im y x) (.lit 2)
def mem (x y : Expr) : Expr := .add (im x y) (.lit 1)
def eqn (x y : Expr) : Expr := .add (im x y) (.lit 3)
def neg (x : Expr) : Expr := im x (.lit 1)
def conj (x y : Expr) : Expr := neg (im x (neg y))
def ex (x y : Expr) : Expr := neg (al x (neg y))

def implicationExpr : Expr := im .a .b
def universalExpr : Expr := al .a .b
def head1Expr : Expr := im (ex .a (al .a .b)) .b
def head2Expr : Expr := im (al .a (al .b .c)) (al .b (al .a .c))
def head3Expr : Expr := im (mem .c .a) (im (eqn .c .b) (mem .b .a))
def head4Expr : Expr := im (eqn .c .a) (im (mem .b .c) (mem .b .a))
def head5Expr : Expr := ex .a (eqn .b .a)
def head6Expr : Expr := im (al .a .b) (im (al .a (im .b .c)) (al .a .c))
def rho8Expr : Expr := im (im (im .c .u) .a) (im (im .a .c) (im .b .c))
def eqVacExpr : Expr := im (eqn .a .b) (al .c (eqn .a .b))
def memVacExpr : Expr := im (mem .a .b) (al .c (mem .a .b))
def pointExpr : Expr := im .c (mem .c .b)
def separationExpr : Expr := al .b (conj (im (mem .a .b) pointExpr) (im (mem .c .b) .c))
def bundleExpr : Expr :=
  neg (im eqVacExpr (im memVacExpr (al .c (im separationExpr (neg pointExpr)))))

theorem implication_exact (a b c u : Nat) : evalNat implicationExpr a b c u = Commands.Code.I a b := rfl
theorem universal_exact (a b c u : Nat) : evalNat universalExpr a b c u = Commands.Code.U a b := rfl
theorem head1_exact (a b c u : Nat) : evalNat head1Expr a b c u = Commands.Code.head1 a b := rfl
theorem head2_exact (a b c u : Nat) : evalNat head2Expr a b c u = Commands.Code.head2 a b c := rfl
theorem head3_exact (a b c u : Nat) : evalNat head3Expr a b c u = Commands.Code.head3 a b c := rfl
theorem head4_exact (a b c u : Nat) : evalNat head4Expr a b c u = Commands.Code.head4 a b c := rfl
theorem head5_exact (a b c u : Nat) : evalNat head5Expr a b c u = Commands.Code.head5 a b := rfl
theorem head6_exact (a b c u : Nat) : evalNat head6Expr a b c u = Commands.Code.head6 a b c := rfl
theorem rho8_exact (a b c u : Nat) : evalNat rho8Expr a b c u = Commands.Code.rho8 a b c u := rfl
theorem bundle_exact (a b c u : Nat) : evalNat bundleExpr a b c u = Commands.Code.bundle a b c := rfl

theorem universal_graph_standard (z a b c u : Nat) :
    (graph universalExpr).val.Evalb ![z, a, b, c, u] ↔ z = Commands.Code.U a b := by
  rw [graph_correct, eval_standard, universal_exact]

theorem bundle_graph_standard (z a b c u : Nat) :
    (graph bundleExpr).val.Evalb ![z, a, b, c, u] ↔ z = Commands.Code.bundle a b c := by
  rw [graph_correct, eval_standard, bundle_exact]

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Existence and uniqueness hold for arbitrary, possibly nonstandard,
parameters. This is an instance of the proved expression graph compiler. -/
theorem formula_graph_total (e : Expr) (a b c u : V) :
    ∃! z, (graph e).val.Evalb ![z, a, b, c, u] := graph_total_unique e a b c u

#print axioms universal_graph_standard
#print axioms bundle_graph_standard
#print axioms formula_graph_total
end PA196.Arithmetic.HeadGraphs
