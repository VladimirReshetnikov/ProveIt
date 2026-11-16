import Mathlib

/-!
# Executable finite data and explicit theorem targets

This module is an uncompiled Lean 4 blueprint. Its declarations define finite
computations and propositions; they do not prove the analytic targets or their
derivability in the embedded iPRA theory. All loops below have numerical bounds.
Do not evaluate `dirichletY` or `boundedPrimeWitness` at the theoretical bound.
The separate object-language bridge must supply primitive recursive codes and
correctness proofs for these definitions. Higher-order sum/max helpers are
metalevel templates; compile their fixed instantiations, not arbitrary functions.
-/

namespace IPRAPrimeDistribution

def sumNat (N : ℕ) (f : ℕ → ℕ) : ℕ :=
  (List.range (N + 1)).foldl (fun acc n => acc + f n) 0

def sumRat (N : ℕ) (f : ℕ → ℚ) : ℚ :=
  (List.range (N + 1)).foldl (fun acc n => acc + f n) 0

/-- Used only on nonnegative entries; the initial value is zero. -/
def maxRat (N : ℕ) (f : ℕ → ℚ) : ℚ :=
  (List.range (N + 1)).foldl (fun acc n => max acc (f n)) 0

def primeBool (n : ℕ) : Bool :=
  decide (2 ≤ n) && (List.range n).all (fun d =>
    decide (d < 2) || decide (n % d ≠ 0))

def piAP (X q a : ℕ) : ℕ :=
  sumNat X (fun p =>
    if primeBool p && decide (p % q = a % q) then 1 else 0)

def phi (q : ℕ) : ℕ :=
  (List.range q).foldl
    (fun acc a => if Nat.gcd a q = 1 then acc + 1 else acc) 0

def squarefreeBool (n : ℕ) : Bool :=
  decide (0 < n) && (List.range (n + 1)).all (fun d =>
    decide (d < 2) || decide (n % (d * d) ≠ 0))

def omega (n : ℕ) : ℕ :=
  sumNat n (fun p =>
    if primeBool p && decide (n % p = 0) then 1 else 0)

def mobius (n : ℕ) : ℤ :=
  if squarefreeBool n then (-1 : ℤ) ^ omega n else 0

def harmonic (z : ℕ) : ℚ :=
  sumRat z (fun n => if 0 < n then 1 / (n : ℚ) else 0)

def sieveG (q z : ℕ) : ℚ :=
  sumRat z (fun d =>
    if squarefreeBool d && decide (Nat.gcd d q = 1)
    then 1 / (phi d : ℚ) else 0)

/-- Finite atanh series; its intended analytic domain is `1 ≤ u`. -/
def logPartial (u : ℚ) (M : ℕ) : ℚ :=
  let w := (u - 1) / (u + 1)
  2 * (List.range M).foldl
    (fun acc j => acc + w ^ (2 * j + 1) / ((2 * j + 1 : ℕ) : ℚ)) 0

/-- For `1 ≤ n`, the paper proves error at most `2⁻ˢ`. -/
def logLower (n s : ℕ) : ℚ :=
  logPartial (n : ℚ) (n * (n + s + 3))

/-- Zero is the default if `n` is not a positive prime power. -/
def primePowerBase (n : ℕ) : ℕ :=
  ((List.range (n + 1)).find? (fun p => primeBool p &&
    (List.range (n + 1)).any (fun j =>
      decide (1 ≤ j) && decide (p ^ j = n)))).getD 0

def lambdaApprox (n s : ℕ) : ℚ :=
  let p := primePowerBase n
  if p = 0 then 0 else logLower p s

def psiApprox (X q a s : ℕ) : ℚ :=
  sumRat X (fun n => if n % q = a % q then lambdaApprox n s else 0)

/-- Integer endpoints and canonical reduced residues only. -/
def errorApprox (X q s : ℕ) : ℚ :=
  maxRat X (fun y => maxRat (q - 1) (fun a =>
    if a < q ∧ Nat.gcd a q = 1
    then |psiApprox y q a s - (y : ℚ) / (phi q : ℚ)| else 0))

def totalErrorApprox (X Q s : ℕ) : ℚ :=
  sumRat Q (fun q => if 0 < q then errorApprox X q s else 0)

/-- Bounded implementations; no real logarithm or square root is used. -/
def floorLogTwo (X : ℕ) : ℕ :=
  (List.range (X + 1)).foldl
    (fun best j => if 2 ^ j ≤ X then j else best) 0

def integerSqrt (t : ℕ) : ℕ :=
  (List.range (t + 1)).foldl
    (fun best j => if j * j ≤ t then j else best) 0

def ceilDiv (x q : ℕ) : ℕ := (x + q - 1) / q

def bvRange (B t : ℕ) : ℕ := 2 ^ (t / 2) / t ^ B

/-- Natural-valued absolute difference, with both subtractions truncated. -/
def natDistance (a b : ℕ) : ℕ := (a - b) + (b - a)

def dirichletD (q : ℕ) : ℕ := 2 ^ 25 * (q + 1) ^ 2
def dirichletC (q : ℕ) : ℕ := 1 + 16 * q ^ 2 * 2 ^ dirichletD q
def dirichletT (q B : ℕ) : ℕ := 8 * q * (B + dirichletC q + q + 4)
def dirichletY (q B : ℕ) : ℕ :=
  2 ^ (dirichletT q B * 2 ^ dirichletT q B)

def scaledPrimeReciprocal (X q a : ℕ) : ℕ :=
  sumNat X (fun p =>
    if primeBool p && decide (p % q = a % q)
    then Nat.factorial X / p else 0)

/-- A total bounded search; zero means no successful candidate was found. -/
def boundedPrimeWitness (q a B : ℕ) : ℕ :=
  let modulus := max q 1
  (List.range (dirichletY q B + 1)).foldl (fun found p =>
    if found = 0 then
      if primeBool p && decide (B < p) && decide (p % modulus = a % modulus)
      then p else 0
    else found) 0

/-! The next declarations are propositions to prove, not proved theorems. -/

def DirichletIntegerTarget : Prop :=
  ∀ q a B : ℕ, 1 ≤ q → Nat.gcd a q = 1 →
    (B + 1) * Nat.factorial (dirichletY q B) <
      scaledPrimeReciprocal (dirichletY q B) q a

def DirichletWitnessTarget : Prop :=
  ∀ q a B : ℕ, 1 ≤ q → Nat.gcd a q = 1 →
    let p := boundedPrimeWitness q a B
    B < p ∧ p ≤ dirichletY q B ∧ primeBool p = true ∧ p % q = a % q

def FiniteSieveTarget : Prop :=
  ∀ X q a z : ℕ, 1 ≤ q → 1 ≤ z → Nat.gcd a q = 1 →
    let first := (X : ℚ) / ((q : ℚ) * sieveG q z) + (z : ℚ) ^ 2 + (z : ℚ)
    let second := (X : ℚ) / ((phi q : ℚ) * harmonic z) + (z : ℚ) ^ 2 + (z : ℚ)
    (piAP X q a : ℚ) ≤ first ∧ first ≤ second

def asymptoticBTThreshold (k : ℕ) : ℕ := (48 * k ^ 2) ^ (16 * k)

def AsymptoticBTTarget : Prop :=
  ∀ r k q a X : ℕ, 1 ≤ k → 1 ≤ q → Nat.gcd a q = 1 →
    q * asymptoticBTThreshold k ≤ X →
    (k : ℚ) * (phi q : ℚ) * (piAP X q a : ℚ) *
        logPartial ((X : ℚ) / (q : ℚ)) (2 ^ r * ceilDiv X q) ≤
      ((2 * k + 1 : ℕ) : ℚ) * (X : ℚ)

/-- Exact lower-logarithm formulation of the sharp all-range theorem.
The package gives its human proof; this declaration remains a Lean target.
For `q < X`, the truncation length is positive and its log error is at most
`2⁻ʳ`. Quantifying over every `r` recovers the closed sharp inequality. -/
def SharpBrunTitchmarshTarget : Prop :=
  ∀ r q a X : ℕ, 1 ≤ q → q < X → Nat.gcd a q = 1 →
    (phi q : ℚ) * (piAP X q a : ℚ) *
        logPartial ((X : ℚ) / (q : ℚ)) (2 ^ r * ceilDiv X q) ≤
      2 * (X : ℚ)

/-- Positive existential witnesses precede every endpoint and precision. -/
def SiegelWalfiszTarget : Prop :=
  ∀ D : ℕ, 1 ≤ D → ∃ K C T : ℕ,
    1 ≤ K ∧ 1 ≤ C ∧ 1 ≤ T ∧
    ∀ X s q a : ℕ, 2 ^ T ≤ X → 1 ≤ q →
      q ≤ floorLogTwo X ^ D → a < q → Nat.gcd a q = 1 →
      |psiApprox X q a s - (X : ℚ) / (phi q : ℚ)| ≤
        (C : ℚ) * (X : ℚ) / (2 : ℚ) ^ (integerSqrt (floorLogTwo X) / K) +
          (X : ℚ) / (2 : ℚ) ^ s

/-- The last term retains the aggregate `Q * X * 2⁻ˢ` approximation error. -/
def BombieriVinogradovTarget : Prop :=
  ∀ A : ℕ, 1 ≤ A → ∃ B C T : ℕ,
    1 ≤ C ∧ 1 ≤ T ∧
    ∀ t s : ℕ, T ≤ t →
      totalErrorApprox (2 ^ t) (bvRange B t) s ≤
        (C : ℚ) * (2 : ℚ) ^ t / (t : ℚ) ^ A +
          (bvRange B t : ℚ) * (2 : ℚ) ^ t / (2 : ℚ) ^ s

/-!
Chebotarev interfaces below are for fixed supplied primitive recursive counting
programs. The surrounding Lean function parameters are metalanguage notation;
they are not object-language quantification over all functions. Their connection
to unramified prime ideals and Frobenius classes must be proved separately.
-/

def ChebotarevDensityTarget (groupOrder classSize : ℕ)
    (selected total : ℕ → ℕ) : Prop :=
  1 ≤ groupOrder ∧ classSize ≤ groupOrder ∧
  (∀ X : ℕ, selected X ≤ total X) ∧
  ∀ k : ℕ, 1 ≤ k → ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
    0 < total X ∧
    k * natDistance (groupOrder * selected X) (classSize * total X) ≤
      groupOrder * total X

def ChebotarevWithModulus (groupOrder classSize : ℕ)
    (selected total modulus : ℕ → ℕ) : Prop :=
  1 ≤ groupOrder ∧ classSize ≤ groupOrder ∧
  (∀ X : ℕ, selected X ≤ total X) ∧
  ∀ k X : ℕ, 1 ≤ k → modulus k ≤ X →
    0 < total X ∧
    k * natDistance (groupOrder * selected X) (classSize * total X) ≤
      groupOrder * total X

/-!
Documentation-only implementation plan (these modules are not supplied here):

* FiniteArithmetic: PR codes and internal proofs for bounded lists and rationals.
* RationalAnalysis: finite log/exp tails, arithmetic laws, and rational gaps.
* FiniteCharacters, LFunctionJets, DirichletMargin, DirichletWitness:
  internalize the quantitative Dirichlet human proof and its bounded selector.
* SelbergFinite, BrunTitchmarshSharp: internalize the finite sieve and the
  additional sharp all-range argument; export the exact target above.
* VaughanFinite, GramFinite: finite convolution and sum-of-squares derivations.
* SWBVTargets, ChebotarevTargets: retain the quantified statements and disclose
  every missing analytic premise; the full three density theorems remain open
  obligations in this package, not asserted consequences of these definitions.
* ObjectAssembly: construct the embedded `Prf PRAAx` terms, then transport them.
-/

end IPRAPrimeDistribution
