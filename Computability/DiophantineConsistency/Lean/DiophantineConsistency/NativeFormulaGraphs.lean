import DiophantineConsistency.NativeFormulaSyntax
import DiophantineConsistency.PolynomialGraph
import DiophantineConsistency.GraphBranching
import DiophantineConsistency.DirectComposition

/-!
# Fixed coordinate graphs for formula generation and the axiom stack

Formula rows use natural polynomial syntax. The nested Cantor stack uses
a fixed positive denominator, cleared in its single graph equation.
Each external operand graph is substituted once in its coordinate block.
-/

namespace DiophantineConsistency.NativeFormulaGraphs

open SetTheory SetTheory.BusyBeaver.ZFC EnumPerm Code254 KCode222
open NativeFormulaSyntax

attribute [local irreducible] P axStack

private def realize {σ : Type*} {f : (σ → ℕ) → ℕ} (e : NatExpr σ)
    (h : ∀ v, e.eval v = f v) : GraphRep f :=
  e.directGraphRep.ofIff (fun v => by
    change v none = e.eval (v ∘ some) ↔ v none = f (v ∘ some)
    rw [h])

def implicationCoordinates : GraphRep (fun v : Fin 2 → ℕ => wim (v 0) (v 1)) :=
  realize (implication (.var 0) (.var 1)) (fun v => by simp [NatExpr.eval])

def row1Coordinates : GraphRep (fun v : Fin 2 → ℕ => rho1 (v 0) (v 1)) :=
  realize (row1 (.var 0) (.var 1)) (fun v => by simp [NatExpr.eval])
def row2Coordinates : GraphRep (fun v : Fin 3 → ℕ => rho2 (v 0) (v 1) (v 2)) :=
  realize (row2 (.var 0) (.var 1) (.var 2)) (fun v => by simp [NatExpr.eval])
def row3Coordinates : GraphRep (fun v : Fin 3 → ℕ => rho3 (v 0) (v 1) (v 2)) :=
  realize (row3 (.var 0) (.var 1) (.var 2)) (fun v => by simp [NatExpr.eval])
def row4Coordinates : GraphRep (fun v : Fin 3 → ℕ => rho4 (v 0) (v 1) (v 2)) :=
  realize (row4 (.var 0) (.var 1) (.var 2)) (fun v => by simp [NatExpr.eval])
def row5Coordinates : GraphRep (fun v : Fin 3 → ℕ => rho5 (v 0) (v 1) (v 2)) :=
  realize (row5 (.var 0) (.var 1) (.var 2)) (fun v => by simp [NatExpr.eval])
def row6Coordinates : GraphRep (fun v : Fin 2 → ℕ => rho6 (v 0) (v 1)) :=
  realize (row6 (.var 0) (.var 1)) (fun v => by simp [NatExpr.eval])
def growthCoordinates : GraphRep (fun v : Fin 3 → ℕ => growG (v 0) (v 1) (v 2)) :=
  realize (growth (.var 0) (.var 1) (.var 2)) (fun v => by simp [NatExpr.eval])
def row8Coordinates : GraphRep (fun v : Fin 4 → ℕ => rho8 (v 0) (v 1) (v 2) (v 3)) :=
  realize (row8 (.var 0) (.var 1) (.var 2) (.var 3)) (fun v => by simp [NatExpr.eval])
def bundleCoordinates : GraphRep (fun v : Fin 3 → ℕ => bundle222 (v 0) (v 1) (v 2)) :=
  realize (bundle (.var 0) (.var 1) (.var 2)) (fun v => by simp [NatExpr.eval])

@[simp] theorem implicationCoordinates_witnessCount : implicationCoordinates.witnessCount = 0 := rfl
@[simp] theorem row1Coordinates_witnessCount : row1Coordinates.witnessCount = 0 := rfl
@[simp] theorem row2Coordinates_witnessCount : row2Coordinates.witnessCount = 0 := rfl
@[simp] theorem row3Coordinates_witnessCount : row3Coordinates.witnessCount = 0 := rfl
@[simp] theorem row4Coordinates_witnessCount : row4Coordinates.witnessCount = 0 := rfl
@[simp] theorem row5Coordinates_witnessCount : row5Coordinates.witnessCount = 0 := rfl
@[simp] theorem row6Coordinates_witnessCount : row6Coordinates.witnessCount = 0 := rfl
@[simp] theorem growthCoordinates_witnessCount : growthCoordinates.witnessCount = 0 := rfl
@[simp] theorem row8Coordinates_witnessCount : row8Coordinates.witnessCount = 0 := rfl
@[simp] theorem bundleCoordinates_witnessCount : bundleCoordinates.witnessCount = 0 := rfl

def gateCoordinates : GraphRep (fun v : Fin 3 → ℕ => gate (v 0) (v 1) (v 2)) := by
  let a : GraphRep (fun v : Fin 3 → ℕ => v 0) := GraphRep.coordinate 0
  let b : GraphRep (fun v : Fin 3 → ℕ => v 1) := GraphRep.coordinate 1
  let c : GraphRep (fun v : Fin 3 → ℕ => v 2) := GraphRep.coordinate 2
  refine (c.ifEq a (GraphRep.constant 0)
    (c.ifEq b (GraphRep.constant 0) bundleCoordinates)).ofIff ?_
  intro v
  by_cases hca : v (some 2) = v (some 0) <;>
    by_cases hcb : v (some 2) = v (some 1) <;>
    simp [gate, hca, hcb]

@[simp] theorem gateCoordinates_witnessCount : gateCoordinates.witnessCount = 14 := rfl

/-- The ten nested source pairings as one fixed-denominator polynomial. -/
def stackScaled : ScaledNatural (fun v : Fin 7 → ℕ =>
    axStack (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)) := by
  let a : NatExpr (Fin 7) := .var 0
  let h : NatExpr (Fin 7) := .var 1
  let b : NatExpr (Fin 7) := .var 2
  let c : NatExpr (Fin 7) := .var 3
  let u : NatExpr (Fin 7) := .var 4
  let t : NatExpr (Fin 7) := .var 5
  let w : NatExpr (Fin 7) := .var 6
  let pair := @ScaledNatural.cantorPair (Fin 7)
  let ofExpr := @ScaledNatural.ofNatExpr (Fin 7)
  let p := pair (ofExpr (row1 a b)) (pair (ofExpr (row2 a b c))
    (pair (ofExpr (row3 a b c)) (pair (ofExpr (row4 a b c))
    (pair (ofExpr (row5 a b c)) (pair (ofExpr (row6 a c))
    (pair (ofExpr (growth a b c)) (pair (ofExpr (row8 a b c u))
    (pair (ofExpr (universal u h)) (pair (ofExpr t) (ofExpr w))))))))))
  refine ⟨p.denominator, p.positive, p.numerator, fun v => (p.correct v).trans ?_⟩
  apply congrArg (fun n => p.denominator * n)
  simp [a, h, b, c, u, t, w, NatExpr.eval, axStack]

def stackCoordinates : GraphRep (fun v : Fin 7 → ℕ =>
    axStack (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)) := stackScaled.graphRep

@[simp] theorem stackCoordinates_witnessCount : stackCoordinates.witnessCount = 0 := rfl

def implication {σ : Type*} {a b : (σ → ℕ) → ℕ} (ha : GraphRep a) (hb : GraphRep b) :
    GraphRep (fun v => wim (a v) (b v)) := by
  let args : ∀ i : Fin 2, GraphRep (![a, b] i) :=
    Fin.cases ha (Fin.cases hb (fun i => Fin.elim0 i))
  exact GraphRep.composeDirect implicationCoordinates args

def gated {σ : Type*} {a b c : (σ → ℕ) → ℕ}
    (ha : GraphRep a) (hb : GraphRep b) (hc : GraphRep c) :
    GraphRep (fun v => gate (a v) (b v) (c v)) := by
  let args : ∀ i : Fin 3, GraphRep (![a, b, c] i) :=
    Fin.cases ha (Fin.cases hb (Fin.cases hc (fun i => Fin.elim0 i)))
  exact GraphRep.composeDirect gateCoordinates args

def stack {σ : Type*} {a h b c u t w : (σ → ℕ) → ℕ}
    (ha : GraphRep a) (hh : GraphRep h) (hb : GraphRep b) (hc : GraphRep c)
    (hu : GraphRep u) (ht : GraphRep t) (hw : GraphRep w) :
    GraphRep (fun v => axStack (a v) (h v) (b v) (c v) (u v) (t v) (w v)) := by
  let args : ∀ i : Fin 7, GraphRep (![a, h, b, c, u, t, w] i) :=
    Fin.cases ha (Fin.cases hh (Fin.cases hb (Fin.cases hc
      (Fin.cases hu (Fin.cases ht (Fin.cases hw (fun i => Fin.elim0 i)))))))
  exact GraphRep.composeDirect stackCoordinates args

theorem implication_witnessCount {σ : Type*} {a b : (σ → ℕ) → ℕ}
    (ha : GraphRep a) (hb : GraphRep b) :
    (implication ha hb).witnessCount = 2 + ha.witnessCount + hb.witnessCount := by
  change 2 + (0 + (ha.witnessCount + (hb.witnessCount + 0))) = _
  omega

theorem gated_witnessCount {σ : Type*} {a b c : (σ → ℕ) → ℕ}
    (ha : GraphRep a) (hb : GraphRep b) (hc : GraphRep c) :
    (gated ha hb hc).witnessCount = 17 + ha.witnessCount + hb.witnessCount + hc.witnessCount := by
  change 3 + (14 + (ha.witnessCount + (hb.witnessCount + (hc.witnessCount + 0)))) = _
  omega

theorem stack_witnessCount {σ : Type*} {a h b c u t w : (σ → ℕ) → ℕ}
    (ha : GraphRep a) (hh : GraphRep h) (hb : GraphRep b) (hc : GraphRep c)
    (hu : GraphRep u) (ht : GraphRep t) (hw : GraphRep w) :
    (stack ha hh hb hc hu ht hw).witnessCount =
      7 + ha.witnessCount + hh.witnessCount + hb.witnessCount + hc.witnessCount +
        hu.witnessCount + ht.witnessCount + hw.witnessCount := by
  change 7 + (0 + (ha.witnessCount + (hh.witnessCount + (hb.witnessCount +
    (hc.witnessCount + (hu.witnessCount + (ht.witnessCount + (hw.witnessCount + 0)))))))) = _
  omega

#print axioms stackCoordinates

end DiophantineConsistency.NativeFormulaGraphs
