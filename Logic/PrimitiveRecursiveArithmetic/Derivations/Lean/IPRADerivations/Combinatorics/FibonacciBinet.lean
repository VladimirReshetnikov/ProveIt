import IPRADerivations.Combinatorics.Fibonacci
import IPRADerivations.Core.CertificateTactics

/-!
# Algebraic Binet identities

Packet: `combinatorics/fibonacci_lucas_ipra`, `FibonacciLucasIPRA.tex`, equation (21).
Represent the elements of `ℤ[t]/(t² − t − 1)` by their two signed coefficients in
the basis `1,t`. Compute the coefficients of `t^m` by simultaneous primitive
recursion. Substitution of `1 − t` for `t` computes the conjugate power, whose
initial value and multiplication step are checked separately. The two Binet
identities are coefficientwise equations in iPRA, with the Fibonacci identity
multiplied by `2t − 1` to stay in the integral ring.
-/

namespace LeanProofs.IPRA.Combinatorics.FibonacciBinet

open_ipra
open LeanProofs.IPRA.Combinatorics.Fibonacci

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- The coefficients of `a + bt` in the integral quadratic ring. -/
abbrev Element (n : ℕ) := ZT n × ZT n

def coordEq (x y : Element n) : Fm PTm n :=
  ZT.eq x.1 y.1 ⋏ ZT.eq x.2 y.2

def add (x y : Element n) : Element n := (x.1 + y.1, x.2 + y.2)
def sub (x y : Element n) : Element n := (x.1 - y.1, x.2 - y.2)

/-- Multiplication reduced using `t² = 1 + t`. -/
def mul (x y : Element n) : Element n :=
  (x.1 * y.1 + x.2 * y.2, x.1 * y.2 + x.2 * y.1 + x.2 * y.2)

def scalar (a : ZT n) : Element n := (a, ZT.natLit 0)
def root : Element n := (ZT.natLit 0, ZT.natLit 1)
def conjugateRoot : Element n := (ZT.natLit 1, -(ZT.natLit 1))

private abbrev linearStep : PTm 3 := var 1 + var 2

/-- The constant coefficient of `t^m`. -/
abbrev constantCoeff (m : PTm n) : PTm n :=
  sim₁ (k := 0) one zero (var 2) linearStep m Fin.elim0

/-- The coefficient of `t` in `t^m`. -/
abbrev linearCoeff (m : PTm n) : PTm n :=
  sim₂ (k := 0) one zero (var 2) linearStep m Fin.elim0

@[simp] theorem subst_constantCoeff {k : ℕ} (σ : Fin n → PTm k) (m : PTm n) :
    Syn.subst σ (constantCoeff m) = constantCoeff (Syn.subst σ m) := by
  simp only [constantCoeff, subst_sim₁]
  congr 1
  funext i
  exact i.elim0

@[simp] theorem subst_linearCoeff {k : ℕ} (σ : Fin n → PTm k) (m : PTm n) :
    Syn.subst σ (linearCoeff m) = linearCoeff (Syn.subst σ m) := by
  simp only [linearCoeff, subst_sim₂]
  congr 1
  funext i
  exact i.elim0

theorem constant_zero : Γ ⊢[PRAAx] constantCoeff (zero : PTm n) ≐ one := by
  simpa using sim₁_zero (k := 0) (Γ := Γ) one zero (var 2) linearStep Fin.elim0

theorem linear_zero : Γ ⊢[PRAAx] linearCoeff (zero : PTm n) ≐ zero := by
  simpa using sim₂_zero (k := 0) (Γ := Γ) one zero (var 2) linearStep Fin.elim0

theorem constant_succ (m : PTm n) : Γ ⊢[PRAAx] constantCoeff (succ m) ≐ linearCoeff m := by
  simpa using sim₁_succ (k := 0) (Γ := Γ) one zero (var 2) linearStep Fin.elim0 m

theorem linear_succ (m : PTm n) :
    Γ ⊢[PRAAx] linearCoeff (succ m) ≐ constantCoeff m + linearCoeff m := by
  simpa using sim₂_succ (k := 0) (Γ := Γ) one zero (var 2) linearStep Fin.elim0 m

/-- The actual primitive-recursive power of `t`. -/
def power (m : PTm n) : Element n :=
  (ZT.ofNat (constantCoeff m), ZT.ofNat (linearCoeff m))

/-- Evaluate the same coefficient pair at `1 − t`. -/
def conjugatePower (m : PTm n) : Element n :=
  (ZT.ofNat (constantCoeff m + linearCoeff m), -(ZT.ofNat (linearCoeff m)))

theorem power_zero : Γ ⊢[PRAAx] coordEq (power zero) (scalar (ZT.natLit 1)) := by
  unfold coordEq power scalar
  exact .andI (by ipra_lc natEq (constant_zero (Γ := Γ)))
    (by ipra_lc natEq (linear_zero (Γ := Γ)))

theorem power_succ (m : PTm n) : Γ ⊢[PRAAx] coordEq (power (succ m)) (mul root (power m)) := by
  unfold coordEq power mul root
  exact .andI (by ipra_lc natEq (constant_succ (Γ := Γ) m))
    (by ipra_lc natEq (linear_succ (Γ := Γ) m))

theorem conjugate_power_zero :
    Γ ⊢[PRAAx] coordEq (conjugatePower zero) (scalar (ZT.natLit 1)) := by
  unfold coordEq conjugatePower scalar
  exact .andI (by ipra_lc natEq (constant_zero (Γ := Γ)) + natEq (linear_zero (Γ := Γ)))
    (by ipra_lc -natEq (linear_zero (Γ := Γ)))

theorem conjugate_power_succ (m : PTm n) :
    Γ ⊢[PRAAx] coordEq (conjugatePower (succ m)) (mul conjugateRoot (conjugatePower m)) := by
  unfold coordEq conjugatePower mul conjugateRoot
  exact .andI (by ipra_lc natEq (constant_succ (Γ := Γ) m) + natEq (linear_succ (Γ := Γ) m))
    (by ipra_lc -natEq (linear_succ (Γ := Γ) m))

def coefficientFormula (m : PTm n) : Fm PTm n :=
  (constantCoeff m + linearCoeff m ≐ fibS m) ⋏ (linearCoeff m ≐ fib m)

private theorem coefficients_open : ([] : List (Fm PTm 1)) ⊢[PRAAx] coefficientFormula (var 0) := by
  unfold coefficientFormula
  ipra_ind (⟨trivial, trivial⟩) [subst_constantCoeff, subst_linearCoeff, subst_fibS, subst_fib]
  · exact .andI
      ((congrAdd constant_zero linear_zero).eqTrans ((add_zero _).eqTrans fibS_zero.eqSymm))
      (linear_zero.eqTrans fib_zero.eqSymm)
  · have prior : [coefficientFormula (var 0 : PTm 1)] ⊢[PRAAx] coefficientFormula (var 0) := Prf.hyp0
    have next := (linear_succ (Γ := [coefficientFormula (var 0)]) (var 0)).eqTrans (Prf.andE₁ prior)
    exact .andI
      ((congrAdd ((constant_succ _).eqTrans (Prf.andE₂ prior)) next).eqTrans
        ((add_comm _ _).eqTrans (fibS_succ _).eqSymm))
      (next.eqTrans (fib_succ _).eqSymm)

theorem coefficients (m : PTm n) : Γ ⊢[PRAAx] coefficientFormula m := by
  have h := inst (Γ := Γ) coefficients_open (![m] : Fin 1 → PTm n)
  simp only [coefficientFormula, Fm.subst_and, Fm.subst_eq, PTm.subst_add, subst_constantCoeff,
    subst_linearCoeff, subst_fibS, subst_fib, Syn.subst_var] at h
  exact h

def rootsFormula : Fm PTm n :=
  coordEq (mul root root) (add root (scalar (ZT.natLit 1))) ⋏
    (coordEq (mul conjugateRoot conjugateRoot) (add conjugateRoot (scalar (ZT.natLit 1))) ⋏
      coordEq (mul (sub root conjugateRoot) (sub root conjugateRoot)) (scalar (ZT.natLit 5)))

/-- Both roots satisfy `X² = X + 1` and their difference squares to five. -/
theorem algebraic_roots_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] rootsFormula := by
  unfold rootsFormula coordEq mul add scalar root conjugateRoot sub
  refine .andI (.andI ?_ ?_) (.andI (.andI ?_ ?_) (.andI ?_ ?_)) <;> ipra_lc

/-- The two Binet identities in the integral basis. -/
def binetFormula (m : PTm n) : Fm PTm n :=
  coordEq (add (power m) (conjugatePower m)) (scalar (ZT.ofNat (luc m))) ⋏
    coordEq (sub (power m) (conjugatePower m))
      (mul (sub root conjugateRoot) (scalar (ZT.ofNat (fib m))))

theorem binet (m : PTm n) : Γ ⊢[PRAAx] binetFormula m := by
  have coeffs := coefficients (Γ := Γ) m
  have linear := natEq (Prf.andE₂ coeffs)
  unfold binetFormula coordEq add sub power conjugatePower scalar root conjugateRoot mul
  refine .andI (.andI ?_ ?_) (.andI ?_ ?_)
  · ipra_lc 2 * natEq (Prf.andE₁ coeffs) - linear - natEq (luc_eq (Γ := Γ) m)
  · ipra_lc
  · ipra_lc -linear
  · ipra_lc 2 * linear

/-- For all `m`, `t^m + (1 − t)^m = L_m` and
`t^m − (1 − t)^m = (2t − 1)F_m` in `ℤ[t]/(t² − t − 1)`. -/
theorem algebraic_binet_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1 (binetFormula (var 0)) :=
  closeUniv 1 (binet (var 0))

end LeanProofs.IPRA.Combinatorics.FibonacciBinet
