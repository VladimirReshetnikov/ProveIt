import Mathlib

/-!
Finite definitions for the zeta/iPRA research package.
STATUS: uncompiled Lean 4 candidate, targeted at ProveIt's Lean 4.32.0.
These definitions and small ambient lemmas are not object-theory iPRA proofs.
The manuscript specifies every analytic error contract; the roadmap specifies
which PR symbols and Prf PRAAx derivations still have to be constructed.
-/
namespace ZetaIPRA

structure CQ where
  re : ℚ
  im : ℚ
  deriving DecidableEq

def cq (q : ℚ) : CQ := ⟨q, 0⟩
def add (z w : CQ) : CQ := ⟨z.re + w.re, z.im + w.im⟩
def neg (z : CQ) : CQ := ⟨-z.re, -z.im⟩
def sub (z w : CQ) : CQ := add z (neg w)
def mul (z w : CQ) : CQ :=
  ⟨z.re*w.re-z.im*w.im, z.re*w.im+z.im*w.re⟩
def scale (q : ℚ) (z : CQ) : CQ := ⟨q*z.re, q*z.im⟩
def norm1 (z : CQ) : ℚ := |z.re| + |z.im|
def inv (z : CQ) : CQ :=
  let d := z.re*z.re+z.im*z.im
  ⟨z.re/d, -z.im/d⟩
-- `inv 0` is totalized by rational arithmetic. Analytic uses require apartness.
def div (z w : CQ) : CQ := mul z (inv w)

def csum (f : ℕ → CQ) : ℕ → CQ
  | 0 => cq 0
  | n+1 => add (csum f n) (f n)

def cpow (z : CQ) : ℕ → CQ
  | 0 => cq 1
  | n+1 => mul (cpow z n) z

def rising (z : CQ) : ℕ → CQ
  | 0 => cq 1
  | n+1 => mul (rising z n) (add z (cq n))

def eps (k : ℕ) : ℚ := (2 : ℚ)^(- (k : ℤ))
abbrev Name := ℕ → CQ

def Regular (a : Name) : Prop :=
  ∀ k l, norm1 (sub (a k) (a l)) ≤ eps k + eps l

def Same (a b : Name) : Prop :=
  ∀ k l, norm1 (sub (a k) (b l)) ≤ eps k + eps l

def Apart (a : Name) (d : ℚ) : Prop :=
  0 < d ∧ ∀ k, d ≤ norm1 (a k) + eps k

structure Ball where
  center : CQ
  radius : ℚ
  nonneg : 0 ≤ radius

def Contains (b : Ball) (z : CQ) : Prop :=
  norm1 (sub z b.center) ≤ b.radius

def dirichletInteger (r N : ℕ) : ℚ :=
  ∑ n ∈ Finset.range N, ((n+1 : ℕ) : ℚ)^(- (r : ℤ))

def expPolynomial (z : CQ) (N : ℕ) : CQ :=
  csum (fun j => scale ((j.factorial : ℚ)⁻¹) (cpow z j)) (N+1)

def logPolynomial (q : ℚ) (L : ℕ) : ℚ :=
  let v := (q-1)/(q+1)
  2 * ∑ j ∈ Finset.range L, v^(2*j+1)/(2*j+1 : ℚ)

-- Convention B_1=-1/2. Finite list recursion, not a universal PR interpreter.
def bernoulliTable : ℕ → List ℚ
  | 0 => [1]
  | n+1 =>
    let bs := bernoulliTable n
    let next := -(∑ j ∈ Finset.range (n+1),
        ((n+2).choose j : ℚ) * bs.getD j 0)/(n+2 : ℚ)
    bs ++ [next]

def bernoulli (n : ℕ) : ℚ := (bernoulliTable n).getD n 0

def bernoulliPolynomial (n : ℕ) (x : ℚ) : ℚ :=
  ∑ j ∈ Finset.range (n+1),
    (n.choose j : ℚ) * bernoulli j * x^(n-j)

def bernoulliMajorant (n : ℕ) : ℚ :=
  ∑ j ∈ Finset.range (n+1), (n.choose j : ℚ) * |bernoulli j|

-- Domain bounds and rational data are inputs, rather than discovered by search.
structure Chart where
  leftBound : ℕ
  radiusBound : ℕ
  poleDistance : ℚ
  distance_pos : 0 < poleDistance

/-- Rational-input EM expression. `powApprox` and `logApprox` are fixed
programs to be ported from code/zeta_certificates.py with their error proofs.
The branch at 1 is a decidable equality of exact rational inputs only. -/
def emRegularApprox
    (powApprox : ℚ → CQ → ℕ → CQ)
    (logApprox : ℚ → ℕ → ℚ)
    (s : CQ) (N m k : ℕ) : CQ :=
  let qN : ℚ := N
  let first := csum (fun j => powApprox (j+1) (neg s) k) (N-1)
  let poleRemoved := if s = cq 1 then cq (-logApprox qN k)
    else div (sub (powApprox qN (sub (cq 1) s) k) (cq 1)) (sub s (cq 1))
  let half := scale (1/2) (powApprox qN (neg s) k)
  let corrections := csum (fun j =>
    let r := j+1
    scale (bernoulli (2*r) / ((2*r).factorial : ℚ))
      (mul (rising s (2*r-1))
        (powApprox qN (sub (cq (1-2*(r : ℚ))) s) k))) m
  add (add first poleRemoved) (add half corrections)

/-- Finite Euler--Hasse numerator approximants for exact rational input. -/
def hasseDifference (powApprox : ℚ → CQ → ℕ → CQ)
    (s : CQ) (n prec : ℕ) : CQ :=
  csum (fun j => scale (((-1 : ℚ)^j) * (n.choose j : ℚ))
    (powApprox (j+1) (neg s) prec)) (n+1)

def hassePartial (powApprox : ℚ → CQ → ℕ → CQ)
    (s : CQ) (N prec : ℕ) : CQ :=
  csum (fun n => scale ((2 : ℚ)^(-((n+1 : ℕ) : ℤ)))
    (hasseDifference powApprox s n prec)) (N+1)

-- Small finite lemmas included as proposed proof scripts. They have not
-- been checked by a Lean executable in this preparation environment.
theorem csum_succ (f : ℕ → CQ) (n : ℕ) :
    csum f (n+1) = add (csum f n) (f n) := rfl

theorem rational_telescoping (f : ℕ → ℚ) (N : ℕ) :
    (∑ n ∈ Finset.range N, (f (n+1)-f n)) = f N-f 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    ring

end ZetaIPRA
