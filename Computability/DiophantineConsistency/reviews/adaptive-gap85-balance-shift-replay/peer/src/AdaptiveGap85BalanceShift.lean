import DiophantineConsistency.AdaptiveGap85Literal

/-! Algebra for a second possible 85-witness shift.

The identities below hold in any commutative ring. They do not establish
positivity of shifted coordinates, preservation of a whole natural-model
zero, or existence of a normalized representative.
-/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85BalanceShift
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveFirstRootFactor87Syntax AdaptiveDirectOrdinate86Context
open AdaptiveGap85Literal

variable {R : Type*} [CommRing R]

def ringEval {σ : Type*} (v : σ → R) : Expr σ → R
  | .constant z => (z : R)
  | .var i => v i
  | .add a b => ringEval v a + ringEval v b
  | .sub a b => ringEval v a - ringEval v b
  | .mul a b => ringEval v a * ringEval v b

@[simp] theorem ringEval_var {σ : Type*} (v : σ → R) (i : σ) :
    ringEval v (.var i) = v i := rfl
@[simp] theorem ringEval_constant {σ : Type*} (v : σ → R) (z : ℤ) :
    ringEval v (.constant z) = (z : R) := rfl
@[simp] theorem ringEval_add {σ : Type*} (v : σ → R) (a b : Expr σ) :
    ringEval v (a+b) = ringEval v a + ringEval v b := rfl
@[simp] theorem ringEval_sub {σ : Type*} (v : σ → R) (a b : Expr σ) :
    ringEval v (a-b) = ringEval v a - ringEval v b := rfl
@[simp] theorem ringEval_mul {σ : Type*} (v : σ → R) (a b : Expr σ) :
    ringEval v (a*b) = ringEval v a * ringEval v b := rfl
@[simp] theorem ringEval_ofNat {σ : Type*} (v : σ → R) (n : ℕ) :
    ringEval v (ofNat(n) : Expr σ) = (n : R) := by
  change ((n : ℤ) : R) = (n : R)
  exact Int.cast_natCast n

/-- The rank input is fixed while F rises by b*t and C falls by q*b*t. -/
theorem rank_preserved (q F C b t : R) :
    (q - (F + b*t))*q - (C - q*b*t) = (q-F)*q-C := by
  ring

/-- The transport input changes by the explicitly divisible quantity. -/
theorem transport_change (q F C b t A : R) :
    (C-q*b*t)*A-(F+b*t)*q = (C*A-F*q)-q*b*t*(A+1) := by
  ring

/-- The accompanying r shift exactly preserves the first-factor root input.
The arbitrary L stands for the unchanged sum ell+k. -/
theorem first_root_preserved (q F C b t A k r L Y : R) :
    (q*q*q*b)*(L + (r-q*t*(A+1)*(b*k+1)) -
      k*((C-q*b*t)*A-(F+b*t)*q)) + Y*b -
      ((C-q*b*t)*A-(F+b*t)*q)*(q*q*q) =
    (q*q*q*b)*(L+r-k*(C*A-F*q)) + Y*b - (C*A-F*q)*(q*q*q) := by
  ring

/-- If q=1+b, the sum that must be normalized decreases by b²*t. -/
theorem gap_sum_change (F C b t : R) :
    (F+b*t) + (C-(1+b)*b*t) = F+C-b*b*t := by
  ring

/-- The proposed shift, stated in a ring so no subtraction is truncated. -/
def shift (p : Fin 4 → ℤ) (v : Fin 13 → R) (t : R) : Fin 13 → R :=
  let b := v 0 * (p 0 : R)
  let q := 1+b
  let A := v 6+(p 1 : R)*q
  let k := v 9+v 10
  ![v 0, v 1+b*t, v 2-q*b*t, v 3, v 4, v 5, v 6, v 7,
    v 8-q*t*(A+1)*(b*k+1), v 9, v 10, v 11, v 12]

/-- The two inputs through which the changed coordinates affect the literal. -/
def rankInput (p : Fin 4 → ℤ) (v : Fin 13 → R) : R :=
  let b := v 0*(p 0 : R)
  let q := 1+b
  (q-v 1)*q-v 2

def rootInput (p : Fin 4 → ℤ) (v : Fin 13 → R) : R :=
  let b := v 0*(p 0 : R)
  let q := 1+b
  let k := v 9+v 10
  let ell := (v 6*v 7)*(v 7*k)
  let A := v 6+(p 1 : R)*q
  let Bt := v 2*A-v 1*q
  (q*(q*q)*b)*((ell+k)+v 8-k*Bt)+v 7*b-Bt*(q*(q*q))

theorem shift_rank (p : Fin 4 → ℤ) (v : Fin 13 → R) (t : R) :
    rankInput p (shift p v t)=rankInput p v := by
  dsimp [rankInput, shift]
  ring

theorem shift_root (p : Fin 4 → ℤ) (v : Fin 13 → R) (t : R) :
    rootInput p (shift p v t)=rootInput p v := by
  dsimp [rootInput, shift]
  ring

/-- Exact semantic shell, with the two variable inputs made explicit. -/
def shell (p : Fin 4 → ℤ) (v : Fin 13 → R) (Z G : R) : R :=
  let J := v 0
  let f := v 3
  let i := v 4
  let T := v 5
  let X := v 6
  let Y := v 7
  let eta := v 9
  let zeta := v 10
  let y := v 11
  let gamma := v 12
  let b := J*(p 0 : R)
  let q := 1+b
  let q2 := q*q
  let q3 := q*q2
  let U := Y*q2
  let E := X*Y
  let k := eta+zeta
  let kY := Y*k
  let c := eta+kY
  let c2 := c*c
  let a := E+Y
  let H := 3+4*a
  let Delta := H+a*a
  let b0 := X+a*c
  let ell := E*kY
  let M := q3*b
  let A0 := Z*Z-M*M*(1+ell*(ell+k))
  let R0 := G*(q2-1)+J*((p 2 : R)+(p 3 : R)*q)
  let r0 := (k-R0)-1
  let shift0 := (U*gamma+E*q)-r0
  let Dstar := U*b0+H*shift0
  let A1 := Dstar*Dstar-U*U*(1+Delta*c2)
  let f2 := f*f
  let Q := Delta*(f2-1)
  let I := c2*i
  let Fs := 1+(I*I-Q)
  let V := f2*(T*c-R0)-c
  let Fa := y*y-Q*(y*y-V*V)
  let F0 := 1+A0
  let F1 := 1+A1
  Fs*(Fa*(F0*F1))-1

theorem eval_eq_shell (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    ringEval v (expressionAt85 p) = shell p v (rootInput p v) (rankInput p v) := by
  simp only [expressionAt85, ringEval_add, ringEval_sub, ringEval_mul,
    ringEval_var, ringEval_constant, ringEval_ofNat, Nat.cast_ofNat, Nat.cast_one,
    shell, rootInput, rankInput]

theorem shell_shift (p : Fin 4 → ℤ) (v : Fin 13 → R) (t Z G : R) :
    shell p (shift p v t) Z G = shell p v Z G := by
  simp [shell, shift]

/-- Ring-level preservation of the entire literal; positive-natural-model
normalization still requires a separate translation and positivity bounds. -/
theorem literal_eval_shift (p : Fin 4 → ℤ) (v : Fin 13 → R) (t : R) :
    ringEval (shift p v t) (expressionAt85 p) = ringEval v (expressionAt85 p) := by
  rw [eval_eq_shell, eval_eq_shell, shift_root, shift_rank, shell_shift]

theorem ringEval_int {σ : Type*} (v : σ → ℤ) (e : Expr σ) :
    ringEval v e = e.eval v := by
  induction e <;> simp_all [ringEval, Expr.eval]

/-- The same exact equality for the existing integer expression evaluator. -/
theorem literal_integer_shift (p : Fin 4 → ℤ) (v : Fin 13 → ℤ) (t : ℤ) :
    (expressionAt85 p).eval (shift p v t) = (expressionAt85 p).eval v := by
  simpa only [ringEval_int] using literal_eval_shift p v t

/-- The explicit inequalities needed to retain positive integer coordinates. -/
theorem shift_integer_positive (p : Fin 4 → ℤ) (v : Fin 13 → ℤ) (t : ℤ)
    (hp : 0 ≤ p 0) (ht : 0 ≤ t) (hv : ∀ j, 0 < v j)
    (hC : (1+v 0*p 0)*(v 0*p 0)*t < v 2)
    (hr : (1+v 0*p 0)*t*(v 6+p 1*(1+v 0*p 0)+1)*
      ((v 0*p 0)*(v 9+v 10)+1) < v 8) :
    ∀ j, 0 < shift p v t j := by
  have hb : 0 ≤ v 0*p 0 := mul_nonneg (le_of_lt (hv 0)) hp
  have hbt : 0 ≤ v 0*p 0*t := mul_nonneg hb ht
  intro j
  fin_cases j <;> dsimp [shift] <;> first
    | exact hv 0 | exact hv 3 | exact hv 4 | exact hv 5 | exact hv 6
    | exact hv 7 | exact hv 9 | exact hv 10 | exact hv 11 | exact hv 12
    | exact add_pos_of_pos_of_nonneg (hv 1) hbt
    | exact sub_pos.mpr hC
    | exact sub_pos.mpr hr

/-- A positive zero remains a positive zero under the displayed bounds. -/
theorem positive_integer_zero_shift (p : Fin 4 → ℤ) (v : Fin 13 → ℤ) (t : ℤ)
    (hp : 0 ≤ p 0) (ht : 0 ≤ t) (hv : ∀ j, 0 < v j)
    (hC : (1+v 0*p 0)*(v 0*p 0)*t < v 2)
    (hr : (1+v 0*p 0)*t*(v 6+p 1*(1+v 0*p 0)+1)*
      ((v 0*p 0)*(v 9+v 10)+1) < v 8)
    (hz : (expressionAt85 p).eval v = 0) :
    (∀ j, 0 < shift p v t j) ∧ (expressionAt85 p).eval (shift p v t) = 0 := by
  exact ⟨shift_integer_positive p v t hp ht hv hC hr,
    (literal_integer_shift p v t).trans hz⟩

theorem shifted_gap_sum (p : Fin 4 → ℤ) (v : Fin 13 → ℤ) (t : ℤ) :
    shift p v t 1 + shift p v t 2 =
      v 1+v 2-(v 0*p 0)*(v 0*p 0)*t := by
  dsimp [shift]
  ring

end DiophantineConsistency.AdaptiveGap85BalanceShift
