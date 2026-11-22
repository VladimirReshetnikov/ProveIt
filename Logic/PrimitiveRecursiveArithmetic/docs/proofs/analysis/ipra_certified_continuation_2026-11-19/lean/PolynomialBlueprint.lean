import Mathlib

/-!
# Executable finite polynomial blueprint for certified implicit equations

STATUS: UNCOMPILED host-Lean candidate, not an embedded-iPRA derivation.

The definitions below give finite algorithms, not postulated functions. Main
claims are named Prop-valued definitions and fields of a `ProofObligations`
structure. No inhabitant of that structure is asserted; no axiom or unfinished
proof is introduced. The object-theory port must replace these host rationals
and finite functions by the repository's PR numerical codes and return
`Prf PRAAx` derivations. See OBJECT_PORT.md and STATUS.md.

Polynomial lengths, coefficients, exponents and dimension are finite data.
This evaluator does not evaluate arbitrary primitive-recursive program codes.
-/

namespace PolynomialBlueprint

abbrev Vec (d : Nat) := Fin d → ℚ
abbrev Mat (d : Nat) := Fin d → Fin d → ℚ
abbrev Exponent (d : Nat) := Fin d → Nat
abbrev Term (d : Nat) := ℚ × Exponent d
abbrev Polynomial (d : Nat) := List (Term d)
abbrev System (d : Nat) := Fin d → Polynomial d

def indices (d : Nat) : List (Fin d) := List.ofFn (fun i : Fin d => i)

def allFin (d : Nat) (f : Fin d → Bool) : Bool :=
  (indices d).all f

def zeroExponent (d : Nat) : Exponent d := fun _ => 0

def unitExponent {d : Nat} (j : Fin d) : Exponent d :=
  fun i => if i = j then 1 else 0

def sameExponent {d : Nat} (a b : Exponent d) : Bool :=
  allFin d (fun i => decide (a i = b i))

def addExponent {d : Nat} (a b : Exponent d) : Exponent d :=
  fun i => a i + b i

/-- Combine an incoming coefficient with the first matching monomial.
    On a normalized list this preserves uniqueness of the exponent vectors. -/
def insertTerm {d : Nat} (t : Term d) : Polynomial d → Polynomial d
  | [] => if t.1 = 0 then [] else [t]
  | u :: us =>
    if sameExponent t.2 u.2 then
      if t.1 + u.1 = 0 then us else (t.1 + u.1, u.2) :: us
    else u :: insertTerm t us

/-- An explicit finite normalization; no polynomial equality oracle is used. -/
def normalize {d : Nat} (p : Polynomial d) : Polynomial d :=
  p.foldl (fun acc t => insertTerm t acc) []

def constant {d : Nat} (c : ℚ) : Polynomial d :=
  if c = 0 then [] else [(c, zeroExponent d)]

def indeterminate {d : Nat} (j : Fin d) : Polynomial d := [(1, unitExponent j)]

def add {d : Nat} (p q : Polynomial d) : Polynomial d := normalize (p ++ q)

def scale {d : Nat} (c : ℚ) (p : Polynomial d) : Polynomial d :=
  normalize (p.map (fun t => (c*t.1, t.2)))

def negate {d : Nat} (p : Polynomial d) : Polynomial d := scale (-1) p

def sub {d : Nat} (p q : Polynomial d) : Polynomial d := add p (negate q)

def multiply {d : Nat} (p q : Polynomial d) : Polynomial d :=
  normalize (p.flatMap (fun t => q.map (fun u =>
    (t.1*u.1, addExponent t.2 u.2))))

def power {d : Nat} (p : Polynomial d) : Nat → Polynomial d
  | 0 => constant 1
  | n+1 => multiply (power p n) p

def sumPolynomials {d : Nat} (ps : List (Polynomial d)) : Polynomial d :=
  ps.foldl add []

def productPolynomials {d : Nat} (ps : List (Polynomial d)) : Polynomial d :=
  ps.foldl multiply (constant 1)

def monomialSubstitute {d e : Nat} (a : Exponent d)
    (replacements : Fin d → Polynomial e) : Polynomial e :=
  productPolynomials ((indices d).map (fun j => power (replacements j) (a j)))

def substitute {d e : Nat} (p : Polynomial d)
    (replacements : Fin d → Polynomial e) : Polynomial e :=
  sumPolynomials (p.map (fun t => scale t.1 (monomialSubstitute t.2 replacements)))

/-- Expanded coefficients for p(center+h), by finite polynomial substitution. -/
def shift {d : Nat} (p : Polynomial d) (center : Vec d) : Polynomial d :=
  substitute p (fun j => add (constant (center j)) (indeterminate j))

def monomialValue {d : Nat} (a : Exponent d) (x : Vec d) : ℚ :=
  ∏ j, x j ^ a j

def eval {d : Nat} (p : Polynomial d) (x : Vec d) : ℚ :=
  (p.map (fun t => t.1 * monomialValue t.2 x)).sum

def evalSystem {d : Nat} (F : System d) (x : Vec d) : Vec d :=
  fun i => eval (F i) x

def zeroVec (d : Nat) : Vec d := fun _ => 0

def addVec {d : Nat} (x y : Vec d) : Vec d := fun i => x i + y i

def subVec {d : Nat} (x y : Vec d) : Vec d := fun i => x i - y i

def matVec {d : Nat} (B : Mat d) (x : Vec d) : Vec d :=
  fun i => ∑ j, B i j * x j

def identity (d : Nat) : Mat d := fun i j => if i = j then 1 else 0

def matMul {d : Nat} (B C : Mat d) : Mat d :=
  fun i j => ∑ k, B i k * C k j

def matrixCombination {d : Nat} (B : Mat d) (P : System d) : System d :=
  fun i => sumPolynomials ((indices d).map (fun j => scale (B i j) (P j)))

/-- The direct fixed rational update h-B F(center+h). -/
def update {d : Nat} (F : System d) (center : Vec d) (B : Mat d) (h : Vec d) : Vec d :=
  subVec h (matVec B (evalSystem F (addVec center h)))

/-- Its expanded, normalized polynomial coefficients, used by the checker. -/
def updatePolynomials {d : Nat} (F : System d) (center : Vec d) (B : Mat d) : System d :=
  let shifted : System d := fun i => shift (F i) center
  let mixed := matrixCombination B shifted
  fun i => sub (indeterminate i) (mixed i)

/-- Monomial coefficient bound on a symmetric box with coordinate radii R. -/
def monomialGain {d : Nat} (a : Exponent d) (R : Vec d) (j : Fin d) : ℚ :=
  if a j = 0 then 0 else
    (a j : ℚ) * R j ^ (a j - 1) *
      ∏ k, if k = j then (1 : ℚ) else R k ^ a k

def gainEntry {d : Nat} (p : Polynomial d) (R : Vec d) (j : Fin d) : ℚ :=
  (p.map (fun t => |t.1| * monomialGain t.2 R j)).sum

def gainMatrix {d : Nat} (P : System d) (R : Vec d) : Mat d :=
  fun i j => gainEntry (P i) R j

/-- A finite maximum with zero default, used only on nonnegative lists in
    the correctness statements. This also defines the empty-dimensional case. -/
def maxZero (xs : List ℚ) : ℚ := xs.foldl max 0

def supNorm {d : Nat} (x : Vec d) : ℚ :=
  maxZero ((indices d).map (fun i => |x i|))

def weightedNorm {d : Nat} (w x : Vec d) : ℚ :=
  maxZero ((indices d).map (fun i => |x i| / w i))

def inBox {d : Nat} (R x : Vec d) : Prop := ∀ i, |x i| ≤ R i

structure Input (d : Nat) where
  F : System d
  center : Vec d
  B : Mat d
  C : Mat d
  radius : ℚ
  weights : Vec d

def radii {d : Nat} (c : Input d) : Vec d := fun i => c.radius * c.weights i

def expandedUpdate {d : Nat} (c : Input d) : System d :=
  updatePolynomials c.F c.center c.B

def gain {d : Nat} (c : Input d) : Mat d :=
  gainMatrix (expandedUpdate c) (radii c)

def initialDisplacement {d : Nat} (c : Input d) : ℚ :=
  weightedNorm c.weights (update c.F c.center c.B (zeroVec d))

def inverseAmplification {d : Nat} (c : Input d) : ℚ :=
  maxZero ((indices d).map (fun i => ∑ j, |c.C i j| * c.weights j))

def maxWeight {d : Nat} (c : Input d) : ℚ :=
  max 1 (maxZero ((indices d).map c.weights))

def inverseBit {d : Nat} (c : Input d) : Bool :=
  allFin d (fun i => allFin d (fun j =>
    decide (matMul c.C c.B i j = identity d i j)))

/-- Entirely decidable finite certificate. The direct and expanded updates
    are both executable; proving their equality is an explicit obligation. -/
def certificateBit {d : Nat} (c : Input d) : Bool :=
  decide (0 < d) && decide (0 < c.radius) &&
  allFin d (fun i => decide (0 < c.weights i)) && inverseBit c &&
  allFin d (fun i =>
    decide (2 * |eval (expandedUpdate c i) (zeroVec d)| ≤ c.radius*c.weights i)) &&
  allFin d (fun i => decide (2*(∑ j, gain c i j * c.weights j) ≤ c.weights i))

def Accepted {d : Nat} (c : Input d) : Prop := certificateBit c = true

def CertificateSpec {d : Nat} (c : Input d) : Prop :=
  0 < d ∧ 0 < c.radius ∧ (∀ i, 0 < c.weights i) ∧
  (∀ i j, matMul c.C c.B i j = identity d i j) ∧
  (∀ i, 2 * |eval (expandedUpdate c i) (zeroVec d)| ≤ c.radius*c.weights i) ∧
  (∀ i, 2*(∑ j, gain c i j * c.weights j) ≤ c.weights i)

def iterate {d : Nat} (c : Input d) : Nat → Vec d
  | 0 => zeroVec d
  | n+1 => update c.F c.center c.B (iterate c n)

def residual {d : Nat} (c : Input d) (n : Nat) : Vec d :=
  evalSystem c.F (addVec c.center (iterate c n))

def roundBound (q : ℚ) : Nat := max 1 (Int.toNat ⌈q⌉)

/-- Bounded dyadic search; total even outside the nonnegative input guard. -/
def dyadicShift (q : ℚ) : Nat :=
  let J := roundBound q
  ((List.range (J+1)).find? (fun k => decide (q ≤ (2 : ℚ)^k))).getD J

/-- Both ordinary coordinate error and polynomial residual are scheduled.
    `maxWeight` is essential when the contraction norm is weighted. -/
def nameClock {d : Nat} (c : Input d) (p : Nat) : Nat :=
  p + dyadicShift (max 1 (max
    (c.radius * maxWeight c)
    (inverseAmplification c * initialDisplacement c))) + 2

def solutionName {d : Nat} (c : Input d) (p : Nat) : Vec d :=
  addVec c.center (iterate c (nameClock c p))

/-! ## Named propositions still requiring proofs

These are definitions of mathematical statements. Nothing below asserts
an inhabitant. This form lets the blueprint compile without concealing the
missing algebra or the still-distinct iPRA port behind axioms.
-/

def NormalizeCorrect (d : Nat) : Prop :=
  ∀ (p : Polynomial d) (x : Vec d), eval (normalize p) x = eval p x

def AddCorrect (d : Nat) : Prop :=
  ∀ (p q : Polynomial d) (x : Vec d), eval (add p q) x = eval p x + eval q x

def ScaleCorrect (d : Nat) : Prop :=
  ∀ (a : ℚ) (p : Polynomial d) (x : Vec d), eval (scale a p) x = a * eval p x

def MultiplyCorrect (d : Nat) : Prop :=
  ∀ (p q : Polynomial d) (x : Vec d), eval (multiply p q) x = eval p x * eval q x

def PowerCorrect (d : Nat) : Prop :=
  ∀ (p : Polynomial d) (n : Nat) (x : Vec d), eval (power p n) x = eval p x ^ n

def SubstitutionCorrect (d e : Nat) : Prop :=
  ∀ (p : Polynomial d) (replacements : Fin d → Polynomial e) (x : Vec e),
    eval (substitute p replacements) x = eval p (fun j => eval (replacements j) x)

def ShiftCorrect (d : Nat) : Prop :=
  ∀ (p : Polynomial d) (center h : Vec d), eval (shift p center) h = eval p (addVec center h)

def UpdateCorrect (d : Nat) : Prop :=
  ∀ (c : Input d) (h : Vec d) (i : Fin d),
    eval (expandedUpdate c i) h = update c.F c.center c.B h i

def MonomialDifferenceCorrect (d : Nat) : Prop :=
  ∀ (a : Exponent d) (R x y : Vec d), (∀ j, 0 < R j) → inBox R x → inBox R y →
    |monomialValue a x - monomialValue a y| ≤
      ∑ j, monomialGain a R j * |x j-y j|

def PolynomialGainCorrect (d : Nat) : Prop :=
  ∀ (p : Polynomial d) (R x y : Vec d), (∀ j, 0 < R j) → inBox R x → inBox R y →
    |eval p x-eval p y| ≤ ∑ j, gainEntry p R j * |x j-y j|

def CertificateCorrect (d : Nat) : Prop :=
  ∀ c : Input d, Accepted c ↔ CertificateSpec c

def FiniteBounds {d : Nat} (c : Input d) : Prop :=
  (∀ n, inBox (radii c) (iterate c n)) ∧
  (∀ n, weightedNorm c.weights (subVec (iterate c (n+1)) (iterate c n)) ≤
    initialDisplacement c * (1/2 : ℚ)^n) ∧
  (∀ n j, weightedNorm c.weights (subVec (iterate c (n+j)) (iterate c n)) ≤
    2 * initialDisplacement c * (1/2 : ℚ)^n * (1-(1/2 : ℚ)^j)) ∧
  (∀ n, supNorm (residual c n) ≤
    inverseAmplification c * initialDisplacement c * (1/2 : ℚ)^n)

def FiniteBoundsCorrect (d : Nat) : Prop :=
  ∀ c : Input d, Accepted c → FiniteBounds c

def DyadicShiftCorrect : Prop :=
  ∀ q : ℚ, 0 ≤ q → q ≤ (2 : ℚ)^(dyadicShift q)

def NameCorrect (d : Nat) : Prop :=
  ∀ c : Input d, Accepted c →
    (∀ p q, p ≤ q →
      supNorm (subVec (solutionName c p) (solutionName c q)) ≤ (1/2 : ℚ)^(p+2)) ∧
    (∀ p, supNorm (evalSystem c.F (solutionName c p)) ≤ (1/2 : ℚ)^(p+2))

def APosterioriCorrect (d : Nat) : Prop :=
  ∀ (c : Input d), Accepted c → ∀ (z : Vec d), inBox (radii c) z → ∀ n,
    weightedNorm c.weights (subVec z (iterate c n)) ≤
      c.radius * (1/2 : ℚ)^n +
        2 * weightedNorm c.weights (subVec z (update c.F c.center c.B z))

/-- Required proof inventory; it is deliberately not instantiated. -/
structure ProofObligations (d : Nat) : Prop where
  normalization : NormalizeCorrect d
  addition : AddCorrect d
  scaling : ScaleCorrect d
  multiplication : MultiplyCorrect d
  powering : PowerCorrect d
  substitution : SubstitutionCorrect d d
  shifting : ShiftCorrect d
  update_expansion : UpdateCorrect d
  monomial_difference : MonomialDifferenceCorrect d
  polynomial_gain : PolynomialGainCorrect d
  certificate : CertificateCorrect d
  finite_bounds : FiniteBoundsCorrect d
  clock : DyadicShiftCorrect
  name : NameCorrect d
  a_posteriori : APosterioriCorrect d

/-! ## Concrete coupled example, executable once this file is compiled -/

def exampleT : System 2 := fun i =>
  if i = 0 then
    add (add (constant (1/10)) (indeterminate 1)) (scale (1/100) (power (indeterminate 0) 2))
  else
    add (add (constant (1/20)) (scale (1/32) (indeterminate 0)))
      (scale (1/100) (power (indeterminate 1) 2))

def exampleInput : Input 2 where
  F := fun i => sub (indeterminate i) (exampleT i)
  center := zeroVec 2
  B := identity 2
  C := identity 2
  radius := 1/4
  weights := ![4,1]

-- Expected value: true. This is a computation, not an iPRA derivation.
#eval certificateBit exampleInput

end PolynomialBlueprint
