import GRHArticle.SingularModuli.HeckeSeriesPrefixArithmetic

/-!
# Preparing the level-59 coefficient witnesses

The witness generator uses the pentagonal form of the Euler product and
ordinary exact coefficient division. The separate kernel certificates
check the outputs against the modular forms.
-/

namespace GRHArticle.SingularModuli.Prime59

/-- The first coefficients of the pentagonal series. -/
def pentagonalPrefix (N : ℕ) : List ℤ := Id.run do
  let mut a := (Array.replicate N (0 : ℤ)).setIfInBounds 0 1
  for k in [1:N] do
    let low := k*(3*k-1)/2
    if N ≤ low then break
    let sign := if k % 2 = 0 then 1 else -1
    a := a.setIfInBounds low sign
    a := a.setIfInBounds (k*(3*k+1)/2) sign
  return a.toList

/-- Generate the normalized discriminant witness. -/
def discriminantWitness (N : ℕ) : List ℤ :=
  let s := pentagonalPrefix N
  let mul := multiplyPackedIntegerPolynomial N
  let s2 := mul s s
  let s4 := mul s2 s2
  let s8 := mul s4 s4
  let s16 := mul s8 s8
  mul s16 s8

/-- Generate divisor sums by adding each divisor's power to its multiples. -/
def divisorPowerWitness (N k : ℕ) : List ℕ := Id.run do
  let mut a := Array.replicate N (0 : ℕ)
  for d in [1:N] do
    let value := d^k
    for v in [1:((N-1)/d)+1] do
      let i := d*v
      a := a.setIfInBounds i (a[i]! + value)
  return a.toList

/-- Compute the quotient of the two coefficient prefixes, for a unit divisor. -/
def divideUnitPrefixes (N : ℕ) (num den : List ℤ) : List ℤ := Id.run do
  let a := num.toArray
  let b := den.toArray
  let mut q := #[]
  for n in [:N] do
    let mut r := a[n]!
    for i in [:n] do
      r := r - b[i+1]! * q[n-i-1]!
    q := q.push r
  return q.toList

/-- Generate the normalized modular invariant witness. -/
def invariantWitness (N : ℕ) (den : List ℤ) : List ℤ :=
  let e4 := (divisorPowerWitness N 3).mapIdx fun i s ↦ if i = 0 then 1 else 240*(s : ℤ)
  let mul := multiplyPackedIntegerPolynomial N
  divideUnitPrefixes N (mul (mul e4 e4) e4) den

end GRHArticle.SingularModuli.Prime59
