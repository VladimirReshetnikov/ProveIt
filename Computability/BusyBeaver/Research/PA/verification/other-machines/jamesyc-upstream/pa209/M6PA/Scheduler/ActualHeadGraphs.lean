module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.ActualArithmeticGraph
public import M6.Source.ActualAXCode
@[expose] public section
open M6.Arithmetic.PA
namespace M6.PA.ActualHeadGraphs
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open ActualArithmeticGraph M6.Source

def im (x y : Expr) : Expr := .mul (.lit 4) (.pair x y)
def al (x y : Expr) : Expr := .add (im x y) (.lit 2)
def mem (x y : Expr) : Expr := .add (im x y) (.lit 1)
def eqn (x y : Expr) : Expr := .add (im x y) (.lit 3)
def neg (x : Expr) : Expr := im x (.lit 1)
def conj (x y : Expr) : Expr := neg (im x (neg y))
def ex (x y : Expr) : Expr := neg (al x (neg y))

def implicationExpr : Expr := im .a .b
def universalExpr : Expr := al .a .b
def rho1Expr : Expr := ex .a (eqn .a .b)
def rho2Expr : Expr := im (al .a (im .b .c)) (im (al .a .b) (al .a .c))
def rho3Expr : Expr := im (eqn .a .b) (im (mem .c .a) (mem .c .b))
def rho4Expr : Expr := im (al .a (al .b .c)) (al .b (al .a .c))
def rho5Expr : Expr := im (eqn .c .a) (im (mem .c .b) (mem .a .b))
def rho6Expr : Expr := im (ex .a (al .a .b)) .b
def rho7Expr : Expr := im (eqn .c .a) (im (eqn .c .b) (al (mem .a .b) (eqn .a .b)))
def rho8Expr : Expr := im (im (im .c .u) .a) (im (im .a .c) (im .b .c))
def pointExpr : Expr := im .c (mem .c .b)
def separationExpr : Expr := al .b (conj (im (mem .a .b) pointExpr) (im (mem .c .b) .c))
def memVacExpr : Expr := im (mem .a .b) (al .c (mem .a .b))
def bundleExpr : Expr := neg (im memVacExpr (al .c (im separationExpr (neg pointExpr))))

theorem implication_exact (a b c u : Nat) : evalNat implicationExpr a b c u = AXCode.wim a b := rfl
theorem universal_exact (a b c u : Nat) : evalNat universalExpr a b c u = AXCode.wal a b := rfl
theorem rho1_exact (a b c u : Nat) : evalNat rho1Expr a b c u = ActualAXCode.rho1 a b := rfl
theorem rho2_exact (a b c u : Nat) : evalNat rho2Expr a b c u = ActualAXCode.rho2 a b c := rfl
theorem rho3_exact (a b c u : Nat) : evalNat rho3Expr a b c u = ActualAXCode.rho3 a b c := rfl
theorem rho4_exact (a b c u : Nat) : evalNat rho4Expr a b c u = ActualAXCode.rho4 a b c := rfl
theorem rho5_exact (a b c u : Nat) : evalNat rho5Expr a b c u = ActualAXCode.rho5 a b c := rfl
theorem rho6_exact (a b c u : Nat) : evalNat rho6Expr a b c u = ActualAXCode.rho6 a b := rfl
theorem rho7_exact (a b c u : Nat) : evalNat rho7Expr a b c u = ActualAXCode.rho7 a b c := rfl
theorem rho8_exact (a b c u : Nat) : evalNat rho8Expr a b c u = ActualAXCode.rho8 a b c u := rfl
theorem bundle_exact (a b c u : Nat) : evalNat bundleExpr a b c u = ActualAXCode.bundle a b c := rfl

/-- Uniform object graph, with standard-model calibration to the literal actual
profile. No historical rho3/rho5/rho7/bundle identification is used. -/
theorem rho3_graph_standard (z a b c u : Nat) :
    (Nat ⊧/![z,a,b,c,u] (graph rho3Expr).val) ↔ z=ActualAXCode.rho3 a b c := by
  rw [graph_correct,eval_standard,rho3_exact]
theorem rho5_graph_standard (z a b c u : Nat) :
    (Nat ⊧/![z,a,b,c,u] (graph rho5Expr).val) ↔ z=ActualAXCode.rho5 a b c := by
  rw [graph_correct,eval_standard,rho5_exact]
theorem rho7_graph_standard (z a b c u : Nat) :
    (Nat ⊧/![z,a,b,c,u] (graph rho7Expr).val) ↔ z=ActualAXCode.rho7 a b c := by
  rw [graph_correct,eval_standard,rho7_exact]
theorem bundle_graph_standard (z a b c u : Nat) :
    (Nat ⊧/![z,a,b,c,u] (graph bundleExpr).val) ↔ z=ActualAXCode.bundle a b c := by
  rw [graph_correct,eval_standard,bundle_exact]

#print axioms rho3_exact
#print axioms rho7_exact
#print axioms bundle_exact
#print axioms rho3_graph_standard
#print axioms bundle_graph_standard
end M6.PA.ActualHeadGraphs

