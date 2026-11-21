import IPRADerivations.AnalyticNumberTheory.Riemann.DirichletData

/-! Imported from the packet `analytic-number-theory/riemann_hypotheses_ipra_2026-11-20`,
`ERHData.lean`: the namespace is placed under `LeanProofs.IPRA.AnalyticNumberTheory.Riemann`, the imports
are rewritten to the library, and axioms are audited in `Checks/Axioms.lean`. -/

/-!
Executable local Euler factors attached to a monic integer polynomial.
All public family parameters are natural numbers. Lists below are finite
work vectors; their length is bounded by the inputs of the corresponding loop.
-/
namespace LeanProofs.IPRA.AnalyticNumberTheory.Riemann.ERHData

/-- Number of successive divisions by p, with an explicit fuel bound. -/
private def valLoop (p : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, n =>
    if n != 0 && n % p == 0 then 1 + valLoop p fuel (n / p) else 0

def valuation (p n : Nat) : Nat := valLoop p n n

/-- Inverse to (a,b) ↦ 2^a (2b+1) − 1. -/
def unpack (u : Nat) : Nat × Nat :=
  let a := valuation 2 (u + 1)
  (a, (u + 1) / (2^a) / 2)

def degree (f : Nat) : Nat := (unpack f).1 + 1

private def digit (base code j : Nat) : Nat := code / base^j % base

/-- The jth signed coefficient, in order 0,-1,1,-2,2,..., reduced modulo p. -/
def lowerResidue (f p j : Nat) : Nat :=
  let t := unpack (unpack f).2
  let a := digit (t.1 + 2) t.2 j
  if a % 2 == 0 then a / 2 % p else (p - ((a / 2 + 1) % p)) % p

/-- Base-p code of the lower coefficients of F mod p. -/
def reduction (f p : Nat) : Nat :=
  (List.range (degree f)).foldl (fun v j => v + lowerResidue f p j * p^j) 0

private def monicCoeff (p d code j : Nat) : Nat :=
  if j == d then 1 else if j < d then digit p code j else 0

/-- Compare the polynomial product of two monic candidates with a dividend. -/
private def sameProduct (p d a h b target : Nat) : Bool :=
  (List.range (d + h + 1)).all fun j =>
    let c := (List.range (j + 1)).foldl (fun acc i =>
      acc + monicCoeff p d a i * monicCoeff p h b (j-i)) 0
    c % p == monicCoeff p (d+h) target j

/-- Both codes omit the leading 1. The candidate quotient is also monic. -/
def dividesMonic (p d a D target : Nat) : Bool :=
  decide (d ≤ D) && (List.range (p^(D-d))).any (fun b =>
    sameProduct p d a (D-d) b target)

/-- Exhaust all proper monic factors of positive degree. -/
def irreducible (p d a : Nat) : Bool :=
  decide (0 < d) && (List.range (d-1)).all (fun j =>
    (List.range (p^(j+1))).all (fun b => !(dividesMonic p (j+1) b d a)))

/-- Multiply a coefficient vector by 1-T^d, retaining terms through T^e. -/
private def addFactor (e d : Nat) (v : List Int) : List Int :=
  (List.range (e+1)).map fun j =>
    (v[j]?).getD 0 - (if d ≤ j then (v[j-d]?).getD 0 else 0)

/-- Coefficient of T^e in the product over distinct residue-field factors. -/
def localCoeff (f p e : Nat) : Int :=
  let D := degree f
  let target := reduction f p
  let v := (List.range D).foldl (fun acc j =>
    let d := j + 1
    (List.range (p^d)).foldl (fun coeffs a =>
      if irreducible p d a && dividesMonic p d a D target then
        addFactor e d coeffs
      else coeffs) acc) ([1] : List Int)
  (v[e]?).getD 0

/-- Multiplicative coefficient; only primes dividing the argument contribute. -/
def coefficient (f n : Nat) : Int :=
  if n == 0 then 0 else
    (List.range (n+1)).foldl (fun acc p =>
      if RHData.primeTest p && n % p == 0 then acc * localCoeff f p (valuation p n)
      else acc) 1

def polynomialSum (f : Nat) : Nat → Int
  | 0 => 0
  | x + 1 => polynomialSum f x + coefficient f (x+1)

/-- For code 0, F=X, every local inverse factor is 1-T. -/
def mertens (f x : Nat) : Int :=
  if f == 0 then RHData.mertens x else polynomialSum f x

theorem mertens_zero_code (x : Nat) : mertens 0 x = RHData.mertens x := by
  rfl

theorem polynomialSum_succ (f x : Nat) :
    polynomialSum f (x + 1) = polynomialSum f x + coefficient f (x+1) := rfl

-- Code 37 names X²+1. Its factors have degrees 1 at 2 and 2 at 3.
example : degree 37 = 2 := by decide
example : reduction 37 3 = 1 := by decide
example : localCoeff 37 2 1 = -1 := by decide
example : localCoeff 37 3 1 = 0 := by decide
example : localCoeff 37 3 2 = -1 := by decide

example : localCoeff 37 5 1 = -2 := by decide
example : localCoeff 37 5 2 = 1 := by decide

-- Code 19453 names X²−5. The nonmaximal order changes the p=2 factor.
example : lowerResidue 19453 7 0 = 2 := by decide
example : localCoeff 19453 2 1 = -1 := by decide

end LeanProofs.IPRA.AnalyticNumberTheory.Riemann.ERHData
