import Foundation.FirstOrder.Arithmetic.HFS.PRF
import Mathlib.Tactic.Ring

/-! Represented Pell recurrence at arbitrary internal IΣ1 times.
The offset base b+2 makes the discriminant a polynomial over natural
arithmetic. This package does not classify solutions or construct the
complete Diophantine equivalence. -/
set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticPellRecurrence
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def delta (b : V) : V := (b+1)*(b+3)

noncomputable def advance (b previous : V) : V :=
  ⟪(b+2)*π₁ previous+delta b*π₂ previous, π₁ previous+(b+2)*π₂ previous⟫

def zeroDef : 𝚺₁.Semisentence 2 := .mkSigma
  “out b. !pairDef out 1 0”
def succDef : 𝚺₁.Semisentence 4 := .mkSigma
  “out previous index b. ∃ x y,
    !pi₁Def x previous ∧ !pi₂Def y previous ∧
    !pairDef out ((b+2)*x+(b+1)*(b+3)*y) (x+(b+2)*y)”
def blueprint : PR.Blueprint 1 where
  zero := zeroDef
  succ := succDef

noncomputable def construction : PR.Construction V blueprint where
  zero _ := ⟪1,0⟫
  succ parameters _ previous := advance (parameters 0) previous
  zero_defined := .mk fun e => by simp [blueprint,zeroDef]
  succ_defined := .mk fun e => by simp [blueprint,succDef,advance,delta]

noncomputable def run (time b : V) : V := construction.result ![b] time
def runDef : 𝚺₁.Semisentence 3 := blueprint.resultDef
def runDeltaDef : 𝚫₁.Semisentence 3 := blueprint.resultDeltaDef

instance run_defined : 𝚺₁-Function₂[V] run via runDef := .mk fun e => by
  have he : (fun i : Fin 1 => e i.succ.succ) = ![e 2] := by
    funext i
    have hi : i=0 := Subsingleton.elim _ _
    subst i
    rfl
  have h := (construction (V := V)).result_defined.df e
  change blueprint.resultDef.val.Evalb e ↔
    e 0=construction.result (fun i : Fin 1 => e i.succ.succ) (e 1) at h
  rw [he] at h
  exact h
instance run_defined_delta : 𝚫₁-Function₂[V] run via runDeltaDef := run_defined.graph_delta
instance run_definable : 𝚺₁-Function₂[V] run := run_defined.to_definable

@[simp] theorem run_zero (b : V) : run 0 b=⟪1,0⟫ := by simp [run,construction]
@[simp] theorem run_succ (time b : V) :
    run (time+1) b=advance b (run time b) := by
  simp [run,PR.Construction.result_succ,construction]

noncomputable def xcoord (time b : V) : V := π₁ (run time b)
noncomputable def ycoord (time b : V) : V := π₂ (run time b)
def xDef : 𝚺₁.Semisentence 3 := .mkSigma
  “out time b. ∃ state, !runDef state time b ∧ !pi₁Def out state”
def yDef : 𝚺₁.Semisentence 3 := .mkSigma
  “out time b. ∃ state, !runDef state time b ∧ !pi₂Def out state”
instance x_defined : 𝚺₁-Function₂[V] xcoord via xDef := .mk fun e => by
  simp [xDef,xcoord]
instance y_defined : 𝚺₁-Function₂[V] ycoord via yDef := .mk fun e => by
  simp [yDef,ycoord]
instance x_definable : 𝚺₁-Function₂[V] xcoord := x_defined.to_definable
instance y_definable : 𝚺₁-Function₂[V] ycoord := y_defined.to_definable

@[simp] theorem x_zero (b : V) : xcoord 0 b=1 := by simp [xcoord]
@[simp] theorem y_zero (b : V) : ycoord 0 b=0 := by simp [ycoord]
theorem x_succ (time b : V) :
    xcoord (time+1) b=(b+2)*xcoord time b+delta b*ycoord time b := by
  simp [xcoord,ycoord,advance]
theorem y_succ (time b : V) :
    ycoord (time+1) b=xcoord time b+(b+2)*ycoord time b := by
  simp [xcoord,ycoord,advance]

theorem run_total (time b : V) : ∃! out, runDef.val.Evalb ![out,time,b] := by simp

/-- A polynomial identity proves preservation without signed subtraction. -/
theorem norm_step (b x y : V) (h : x*x=1+delta b*y*y) :
    ((b+2)*x+delta b*y)*((b+2)*x+delta b*y)=
      1+delta b*(x+(b+2)*y)*(x+(b+2)*y) := by
  let common := delta b*x*x+2*(b+2)*delta b*x*y+delta b*delta b*y*y
  have hl : ((b+2)*x+delta b*y)*((b+2)*x+delta b*y)=x*x+common := by
    dsimp [common,delta]
    ring
  have hr : 1+delta b*(x+(b+2)*y)*(x+(b+2)*y)=(1+delta b*y*y)+common := by
    dsimp [common,delta]
    ring
  rw [hl,hr,h]

theorem norm (time b : V) :
    xcoord time b*xcoord time b=1+delta b*ycoord time b*ycoord time b := by
  induction time using ISigma1.sigma1_succ_induction
  · unfold delta
    definability
  case zero => simp
  case succ time ih => rw [x_succ,y_succ]; exact norm_step b _ _ ih

theorem base_ge_one (b : V) : 1≤b+2 :=
  le_trans (by simp : (1:V)≤2) (by simp : (2:V)≤b+2)

theorem one_le_x (time b : V) : 1≤xcoord time b := by
  induction time using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ time ih =>
    rw [x_succ]
    exact le_trans (one_le_mul (base_ge_one b) ih) (by simp)

theorem y_succ_ge (time b : V) : ycoord time b+1≤ycoord (time+1) b := by
  rw [y_succ,add_comm (ycoord time b) 1]
  exact add_le_add (one_le_x time b)
    (le_mul_of_one_le_left (by simp) (base_ge_one b))

theorem y_succ_lt (time b : V) : ycoord time b<ycoord (time+1) b :=
  lt_of_lt_of_le (lt_add_one _) (y_succ_ge time b)

theorem time_le_y (time b : V) : time≤ycoord time b := by
  induction time using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ time ih => exact le_trans (add_le_add_right ih 1) (y_succ_ge time b)

/-- Both addition formulas hold for arbitrary internal indices. -/
theorem addition (left right b : V) :
    xcoord (left+right) b=xcoord left b*xcoord right b+delta b*ycoord left b*ycoord right b ∧
    ycoord (left+right) b=xcoord left b*ycoord right b+ycoord left b*xcoord right b := by
  induction right using ISigma1.sigma1_succ_induction
  · unfold delta
    definability
  case zero => simp
  case succ right ih =>
    rw [←add_assoc,x_succ,y_succ,ih.1,ih.2,x_succ,y_succ]
    constructor <;> dsimp [delta] <;> ring

end DiophantineConsistency.ArithmeticPellRecurrence
