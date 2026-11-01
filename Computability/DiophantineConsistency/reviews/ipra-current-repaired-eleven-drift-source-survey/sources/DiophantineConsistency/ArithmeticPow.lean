import Foundation.FirstOrder.Arithmetic.HFS.PRF
import Mathlib.Tactic.Ring

/-! Represented variable-base power at arbitrary internal bases and exponents.
`power x n` is the genuine primitive-recursive result with zero value 1 and
successor value `x*previous`; it is not Lean's `x ^ n` with `n : ℕ`.
The module closes with the integer perturbation inequality
`2*r*e ≤ a → a*power (a+e) r ≤ (a+2*r*e)*power a r`. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticPow
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def zeroDef : 𝚺₁.Semisentence 2 := .mkSigma “out x. out=1”
def succDef : 𝚺₁.Semisentence 4 := .mkSigma “out previous index x. out=x*previous”
def blueprint : PR.Blueprint 1 where
  zero := zeroDef
  succ := succDef

noncomputable def construction : PR.Construction V blueprint where
  zero _ := 1
  succ parameters _ previous := parameters 0*previous
  zero_defined := .mk fun e => by simp [blueprint,zeroDef]
  succ_defined := .mk fun e => by simp [blueprint,succDef]

/-- The represented power `power base exponent`. -/
noncomputable def power (x n : V) : V := construction.result ![x] n

/-- Public graph with argument order output/base/exponent. -/
def powerDef : 𝚺₁.Semisentence 3 := blueprint.resultDef |>.rew (Rew.subst ![#0, #2, #1])
def powerDeltaDef : 𝚫₁.Semisentence 3 := powerDef.graphDelta

instance power_defined : 𝚺₁-Function₂[V] power via powerDef := .mk
  fun v ↦ by simp [construction.result_defined_iff, powerDef, power]; rfl
instance power_defined_delta : 𝚫₁-Function₂[V] power via powerDeltaDef := power_defined.graph_delta
instance power_definable : 𝚺₁-Function₂[V] power := power_defined.to_definable

theorem power_total (x n : V) : ∃! out, powerDef.val.Evalb ![out,x,n] := by simp

@[simp] theorem power_zero (x : V) : power x 0=1 := by simp [power,construction]
theorem power_succ (x n : V) : power x (n+1)=x*power x n := by
  simp [power,PR.Construction.result_succ,construction]

@[simp] theorem power_one (x : V) : power x 1=x := by
  simpa using power_succ x 0

@[simp] theorem one_power (n : V) : power 1 n=1 := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ n ih => rw [power_succ,ih,one_mul]

theorem zero_power_of_pos (n : V) (hn : 0<n) : power 0 n=0 := by
  rcases zero_or_succ n with rfl|⟨n,rfl⟩
  · simp at hn
  · rw [power_succ,zero_mul]

theorem power_pos (x n : V) (hx : 0<x) : 0<power x n := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ n ih => rw [power_succ]; exact mul_pos hx ih

theorem power_add (x m n : V) : power x (m+n)=power x m*power x n := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ n ih => rw [←add_assoc,power_succ,power_succ,ih]; ring

theorem power_mul_base (x y n : V) : power (x*y) n=power x n*power y n := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ n ih => rw [power_succ,power_succ,power_succ,ih]; ring

theorem power_iterate (x m n : V) : power (power x m) n=power x (m*n) := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ n ih => rw [power_succ,ih,mul_add,mul_one,power_add]; ring

theorem power_mono_base (x y n : V) (hxy : x≤y) : power x n≤power y n := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ n ih =>
    rw [power_succ,power_succ]
    exact mul_le_mul hxy ih (by simp) (by simp)

theorem one_le_power (x n : V) (hx : 1≤x) : 1≤power x n := by
  simpa using power_mono_base 1 x n hx

theorem power_mono_exponent (x m n : V) (hx : 1≤x) (hmn : m≤n) : power x m≤power x n := by
  have hn : n=m+(n-m) := (add_tsub_cancel_of_le hmn).symm
  rw [hn,power_add]
  simpa using mul_le_mul_of_nonneg_left (one_le_power x (n-m) hx) (by simp : (0:V)≤power x m)

theorem power_strict_base (x y n : V) (hxy : x<y) (hn : 0<n) : power x n<power y n := by
  rcases zero_or_succ n with rfl|⟨n,rfl⟩
  · simp at hn
  · have hy : 0<y := lt_of_le_of_lt (by simp) hxy
    rw [power_succ,power_succ]
    calc
      x*power x n≤x*power y n := mul_le_mul_of_nonneg_left (power_mono_base x y n hxy.le) (by simp)
      _<y*power y n := mul_lt_mul_of_pos_right hxy (power_pos y n hy)

theorem power_two (n : V) : power 2 n=Exp.exp n := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ n ih => rw [power_succ,ih,exp_succ]

theorem power_two_exp (n : V) : power 2 n=Exp.exp n := power_two n

/-- The integer perturbation step: `(a+2re)(a+e) ≤ a(a+2(r+1)e)` when `2re ≤ a`. -/
theorem perturbation_coefficient (a e r : V) (h : 2*r*e≤a) :
    (a+2*r*e)*(a+e)≤a*(a+2*(r+1)*e) := by
  have hd : 2*r*e+(a-2*r*e)=a := add_tsub_cancel_of_le h
  have hid : a*(a+2*(r+1)*e)=(a+2*r*e)*(a+e)+e*(a-2*r*e) := by
    rw [← hd]
    simp only [add_tsub_cancel_left]
    ring
  rw [hid]
  exact le_add_of_nonneg_right (by simp)

/-- The complete integer perturbation inequality, valid at every internal
`a e r` including `r=0`, `a=0` and `e=0`. -/
theorem perturbation (a e r : V) (h : 2*r*e≤a) :
    a*power (a+e) r≤(a+2*r*e)*power a r := by
  induction r using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero => simp
  | succ r ih =>
    have hr0 : 2*r*e≤a := le_trans (by
        have : 2*r*e≤2*(r+1)*e := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (by simp) (by simp)) (by simp)
        exact this) h
    have ih' := ih hr0
    rw [power_succ,power_succ]
    calc
        a*((a+e)*power (a+e) r)=(a+e)*(a*power (a+e) r) := by ring
        _≤(a+e)*((a+2*r*e)*power a r) := mul_le_mul_of_nonneg_left ih' (by simp)
        _=((a+2*r*e)*(a+e))*power a r := by ring
        _≤(a*(a+2*(r+1)*e))*power a r :=
          mul_le_mul_of_nonneg_right (perturbation_coefficient a e r hr0) (by simp)
        _=(a+2*(r+1)*e)*(a*power a r) := by ring

end DiophantineConsistency.ArithmeticPow
