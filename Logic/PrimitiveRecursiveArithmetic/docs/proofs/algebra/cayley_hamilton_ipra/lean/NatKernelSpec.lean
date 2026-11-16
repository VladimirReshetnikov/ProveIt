import Std

/-!
# A concrete natural-number specification of the Cayley--Hamilton checker

STATUS: uncompiled specification, not a Lean-checked proof.
There are no axioms, sorries, Classical declarations, or noncomputable
definitions in this file.

Every value manipulated by the definitions below is a natural number.
The functions passed to folds/tabulate are fixed helper bodies; they are
meta-language conveniences for fixed primitive-recursive definitions.
The remaining formalization must:
* construct the corresponding PR syntax values in ConciseIPRA;
* prove all defining-equation and representation lemmas internally;
* prove Prf PRAAx [] (checkStatement chCheckCode).

In particular, the definition chCheck is NOT accompanied by an assertion
that it always returns 1. That assertion is the mathematical theorem to
formalize.

The dense representation is intentionally simple and extremely inefficient.
The list code uses exponentiation. Do not mistake this specification for a
practical numerical implementation; the Python artifact is suitable for
small regression calculations.

Main definitions:
* zadd/zneg/zmul: canonical signed integer codes.
* padd/pneg/pmul: bounded dense polynomial coefficients.
* mAdd/mMul/mPow: matrices of those polynomial codes.
* determinant/adjugate: explicit bounded Leibniz operations.
* charCoeff: coefficient of t^k in det(tI-X).
* cayleyResidual: evaluation of the characteristic polynomial at X.
* chCheck: bounded test that every residual coefficient is zero.

The polynomial variable t is stored as variable zero in v+1 variables,
and the n^2 matrix variables occupy the other positions. The extracted
coefficient has v=n^2 variables. This is equivalent to a separate
coefficient array in t, as in FORMALIZATION_PLAN.md.
-/

namespace CayleyHamiltonNatSpec

/-- Iteration with an explicit counter, starting at counter zero. -/
def fold (count : Nat) (step : Nat → Nat → Nat) (initial : Nat) : Nat :=
  Nat.rec initial (fun i a => step i a) count

/-- 1 means all tests return 1. The empty conjunction is 1. -/
def allN (count : Nat) (predicate : Nat → Nat) : Nat :=
  fold count (fun i a => if predicate i = 1 then a else 0) 1

/-! ## Finite array coding -/

/-- Code 0 is nil; a cons code is strictly positive. -/
def cons (a b : Nat) : Nat := 2 ^ a * (2 * b + 1)

def head (a : Nat) : Nat :=
  if a = 0 then 0 else
    fold (a + 1) (fun i found => if a % (2 ^ i) = 0 then i else found) 0

def tail (a : Nat) : Nat :=
  if a = 0 then 0 else (a / (2 ^ head a) - 1) / 2

/-- Missing entries have value 0. -/
def lookup (a i : Nat) : Nat :=
  head (fold i (fun _ r => tail r) a)

def tabulate : Nat → (Nat → Nat) → Nat
  | 0, _ => 0
  | k + 1, f => cons (f 0) (tabulate k (fun i => f (i + 1)))

/-! ## Signed integer codes

Code 2m represents m. Code 2m+1 represents -(m+1).
-/

def zmag (a : Nat) : Nat :=
  if a % 2 = 0 then a / 2 else (a + 1) / 2

/-- The sign input is used modulo 2. -/
def zmake (sign magnitude : Nat) : Nat :=
  if magnitude = 0 then 0 else
    if sign % 2 = 0 then 2 * magnitude else 2 * magnitude - 1

def zone : Nat := 2

def zneg (a : Nat) : Nat :=
  if a = 0 then 0 else if a % 2 = 0 then a - 1 else a + 1

def zadd (a b : Nat) : Nat :=
  if a % 2 = b % 2 then
    zmake (a % 2) (zmag a + zmag b)
  else if zmag a ≤ zmag b then
    zmake (b % 2) (zmag b - zmag a)
  else
    zmake (a % 2) (zmag a - zmag b)

def zmul (a b : Nat) : Nat :=
  zmake (a % 2 + b % 2) (zmag a * zmag b)

def zsum (count : Nat) (f : Nat → Nat) : Nat :=
  fold count (fun i a => zadd a (f i)) 0

/-! ## Dense polynomials

There are v variables, each exponent is at most d. Coefficients are
signed codes. An exponent vector is indexed in base d+1, least significant
digit first. Multiplication drops terms outside the exponent box.

A separate support theorem must show that no genuine coefficient is
dropped in the Cayley--Hamilton construction: every relevant generic
polynomial has total degree at most n, and d is n.
-/

def polyLength (v d : Nat) : Nat := (d + 1) ^ v

def digit (base code position : Nat) : Nat :=
  (code / (base ^ position)) % base

def pzero (v d : Nat) : Nat :=
  tabulate (polyLength v d) (fun _ => 0)

def pconst (v d a : Nat) : Nat :=
  tabulate (polyLength v d) (fun e => if e = 0 then a else 0)

def pone (v d : Nat) : Nat := pconst v d zone

def pvar (v d variable : Nat) : Nat :=
  tabulate (polyLength v d)
    (fun e =>
      if variable < v then
        if 0 < d then
          if e = (d + 1) ^ variable then zone else 0
        else 0
      else 0)

def padd (v d a b : Nat) : Nat :=
  tabulate (polyLength v d) (fun e => zadd (lookup a e) (lookup b e))

def pneg (v d a : Nat) : Nat :=
  tabulate (polyLength v d) (fun e => zneg (lookup a e))

def psub (v d a b : Nat) : Nat := padd v d a (pneg v d b)

/-- Whether exponent vector a is componentwise at most exponent vector e. -/
def exponentLe (v d a e : Nat) : Nat :=
  allN v (fun i => if digit (d + 1) a i ≤ digit (d + 1) e i then 1 else 0)

def pmul (v d a b : Nat) : Nat :=
  tabulate (polyLength v d) (fun e =>
    zsum (polyLength v d) (fun u =>
      if exponentLe v d u e = 1 then
        zmul (lookup a u) (lookup b (e - u))
      else 0))

def psum (v d count : Nat) (f : Nat → Nat) : Nat :=
  fold count (fun i a => padd v d a (f i)) (pzero v d)

def pprod (v d count : Nat) (f : Nat → Nat) : Nat :=
  fold count (fun i a => pmul v d a (f i)) (pone v d)

/-! ## Matrices over coded polynomials -/

def entry (n a i j : Nat) : Nat := lookup a (i * n + j)

def mZero (v d n : Nat) : Nat :=
  tabulate (n * n) (fun _ => pzero v d)

def mOne (v d n : Nat) : Nat :=
  tabulate (n * n) (fun ij =>
    if ij / n = ij % n then pone v d else pzero v d)

def mAdd (v d n a b : Nat) : Nat :=
  tabulate (n * n) (fun ij => padd v d (lookup a ij) (lookup b ij))

def mScale (v d n scalar a : Nat) : Nat :=
  tabulate (n * n) (fun ij => pmul v d scalar (lookup a ij))

def mMul (v d n a b : Nat) : Nat :=
  tabulate (n * n) (fun ij =>
    psum v d n (fun k =>
      pmul v d (entry n a (ij / n) k) (entry n b k (ij % n))))

def mPow (v d n a exponent : Nat) : Nat :=
  fold exponent (fun _ r => mMul v d n r a) (mOne v d n)

/-! ## Permutations and determinant -/

def candidateCount (n : Nat) : Nat := if n = 0 then 1 else n ^ n

def permEntry (n code i : Nat) : Nat := digit n code i

/-- Within candidateCount, pairwise distinct digits characterize permutations. -/
def isPermutation (n code : Nat) : Nat :=
  allN (n * n) (fun ij =>
    if ij / n = ij % n then 1 else
      if permEntry n code (ij / n) = permEntry n code (ij % n) then 0 else 1)

def inversionCount (n code : Nat) : Nat :=
  fold (n * n) (fun ij count =>
    if ij / n < ij % n then
      if permEntry n code (ij % n) < permEntry n code (ij / n) then count + 1
      else count
    else count) 0

def determinant (v d n a : Nat) : Nat :=
  psum v d (candidateCount n) (fun code =>
    if isPermutation n code = 1 then
      let term := pprod v d n (fun i => entry n a i (permEntry n code i))
      if inversionCount n code % 2 = 0 then term else pneg v d term
    else pzero v d)

def skip (removed i : Nat) : Nat := if i < removed then i else i + 1

def minor (n a removedRow removedColumn : Nat) : Nat :=
  tabulate ((n - 1) * (n - 1)) (fun ij =>
    entry n a (skip removedRow (ij / (n - 1)))
      (skip removedColumn (ij % (n - 1))))

def adjugate (v d n a : Nat) : Nat :=
  tabulate (n * n) (fun ij =>
    let i := ij / n
    let j := ij % n
    let value := determinant v d (n - 1) (minor n a j i)
    if (i + j) % 2 = 0 then value else pneg v d value)

/-! ## The generic characteristic polynomial and its matrix residual -/

/-- Generic n by n matrix; x_ij is variable i*n+j. -/
def genericMatrix (n : Nat) : Nat :=
  tabulate (n * n) (fun ij => pvar (n * n) n ij)

/-- tI-X, with t variable zero and x_ij variable 1+i*n+j. -/
def characteristicMatrix (n : Nat) : Nat :=
  tabulate (n * n) (fun ij =>
    let x := pvar (n * n + 1) n (ij + 1)
    if ij / n = ij % n then
      psub (n * n + 1) n (pvar (n * n + 1) n 0) x
    else pneg (n * n + 1) n x)

def characteristicPolynomial (n : Nat) : Nat :=
  determinant (n * n + 1) n n (characteristicMatrix n)

/-- Coefficient of t^k, stored as a polynomial in the n^2 matrix variables. -/
def charCoeff (n k : Nat) : Nat :=
  if k ≤ n then
    tabulate (polyLength (n * n) n) (fun e =>
      lookup (characteristicPolynomial n) (k + (n + 1) * e))
  else pzero (n * n) n

/-- Sum of c_k X^k for k=0,...,n; this includes the leading term. -/
def cayleyResidual (n : Nat) : Nat :=
  let v := n * n
  let a := genericMatrix n
  fold (n + 1) (fun k r =>
    mAdd v n n r (mScale v n n (charCoeff n k) (mPow v n n a k)))
    (mZero v n n)

/-- Concrete uniform numerical predicate whose iPRA derivation is the target. -/
def chCheck (n : Nat) : Nat :=
  let length := polyLength (n * n) n
  let residual := cayleyResidual n
  allN (n * n * length) (fun index =>
    if lookup (lookup residual (index / length)) (index % length) = 0 then 1 else 0)

/-- Host-level statement only, recorded as a target, not proved here.
Connecting this predicate to ObjectLanguageTargets.checkStatement requires
constructing the specific chCheckCode : PR 1 and proving its representation
equations. A proof of this host proposition alone would still not be a term
of Prf PRAAx [] (checkStatement chCheckCode). -/
def MainArithmeticTarget : Prop := ∀ n : Nat, chCheck n = 1

end CayleyHamiltonNatSpec

