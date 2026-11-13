import Trace74PellModularBinary

/-! Finite binary Pell residue checker with pre-reduced coefficients. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace74PellBitlistChecker
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticPellRecurrence
open Trace74PellModularBinary
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem same_add {m x y z w : V} (hm : 0<m)
    (h : x%m=y%m) (h' : z%m=w%m) : (x+z)%m=(y+w)%m := by
  rw [mod_add hm,mod_add (a:=y) hm,h,h']

private theorem same_mul {m x y z w : V} (hm : 0<m)
    (h : x%m=y%m) (h' : z%m=w%m) : (x*z)%m=(y*w)%m := by
  rw [mod_mul hm,mod_mul (a:=y) hm,h,h']

/-- Process one most-significant-first bit. Only coefficient residues
`L,D` and state residues are needed by the evaluator. -/
def step (m L D : V) (xy : V×V) (bit : Bool) : V×V :=
  let A := xy.1*xy.1+D*xy.2*xy.2
  let B := 2*xy.1*xy.2
  if bit then ((L*A+D*B)%m,(A+L*B)%m) else (A%m,B%m)

def stepIndex (t : V) (bit : Bool) : V := if bit then 2*t+1 else 2*t

/-- Each evaluator step preserves equality with the true Pell residues. -/
theorem step_correct (b m L D t X Y : V) (bit : Bool) (hm : 0<m)
    (hL : (b+2)%m=L%m) (hD : delta b%m=D%m)
    (hx : xcoord t b%m=X) (hy : ycoord t b%m=Y) :
    let out := step m L D (X,Y) bit
    xcoord (stepIndex t bit) b%m=out.1 ∧
      ycoord (stepIndex t bit) b%m=out.2 := by
  have hx' : xcoord t b%m=X%m := by
    rw [←hx,mod_eq_self_of_lt (mod_lt _ hm)]
  have hy' : ycoord t b%m=Y%m := by
    rw [←hy,mod_eq_self_of_lt (mod_lt _ hm)]
  obtain ⟨he,ho⟩ := even_step b t m X Y hm hx' hy'
  have hA : (X*X+delta b*Y*Y)%m=(X*X+D*Y*Y)%m :=
    same_add hm rfl (same_mul hm (same_mul hm hD rfl) rfl)
  have he' : xcoord (2*t) b%m=(X*X+D*Y*Y)%m := he.trans hA
  cases bit with
  | false => simpa [step,stepIndex] using And.intro he' ho
  | true =>
    simp only [step,stepIndex,ite_true]
    constructor
    · rw [x_succ]
      exact same_add hm (same_mul hm hL he') (same_mul hm hD ho)
    · rw [y_succ]
      exact same_add hm he' (same_mul hm hL ho)

/-- A list of bits describes a single pass from left to right. -/
def runIndex (bits : List Bool) : V := bits.foldl stepIndex 0
def run (m L D : V) (bits : List Bool) : V×V :=
  bits.foldl (step m L D) (1%m,0%m)

theorem fold_correct (b m L D : V) (bits : List Bool) (hm : 0<m)
    (hL : (b+2)%m=L%m) (hD : delta b%m=D%m)
    (t X Y : V) (hx : xcoord t b%m=X) (hy : ycoord t b%m=Y) :
    let out := bits.foldl (step m L D) (X,Y)
    let index := bits.foldl stepIndex t
    xcoord index b%m=out.1 ∧ ycoord index b%m=out.2 := by
  induction bits generalizing t X Y with
  | nil => exact ⟨hx,hy⟩
  | cons bit bits ih =>
    obtain ⟨hx',hy'⟩ := step_correct b m L D t X Y bit hm hL hD hx hy
    exact ih (stepIndex t bit) (step m L D (X,Y) bit).1
      (step m L D (X,Y) bit).2 hx' hy'

/-- The modular evaluator returns the true coordinate residues at the
index represented by the most-significant-first bit list. -/
theorem run_correct (b m L D : V) (bits : List Bool) (hm : 0<m)
    (hL : (b+2)%m=L%m) (hD : delta b%m=D%m) :
    xcoord (runIndex bits) b%m=(run m L D bits).1 ∧
      ycoord (runIndex bits) b%m=(run m L D bits).2 := by
  exact fold_correct b m L D bits hm hL hD 0 (1%m) (0%m) (by simp) (by simp)

#print axioms Trace74PellBitlistChecker.step_correct
#print axioms Trace74PellBitlistChecker.run_correct
end Trace74PellBitlistChecker
