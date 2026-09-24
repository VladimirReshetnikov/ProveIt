import Diophantine.Paper1982.Master1

/-!
# Jones 1982, §5: the shorter coding system

The intended exponential equation is retained at this stage. The later
Pell subsystem is needed before it may be eliminated. The represented
polynomial has degree at most four and `L = 5^(ν+1)`; witness positivity
is supplied separately.
-/

namespace Jones1982

/-- The larger base in (D2), replacing `b^5` from §4. -/
def shortBase (ν z b : ℕ) : ℕ := 2 * b ^ 4 * (2 * z) ^ (L4 ν + 1)

/-- The shorter geometric sum used in (D7). -/
def shortLam (ν B : ℕ) : ℕ := ∑ i ∈ Finset.range (L4 ν), B ^ i

/-- The signed third block (D12), (D15). -/
def shortS3 (z B c e Q lam : ℕ) : ℤ :=
  -2 * (c : ℤ) ^ 4 * (z * (lam + Q) - e) + B * lam * (1 + Q)

/-- The coding equations (D1), (D2), (D6)–(D10), with `Q = B^L` retained.
The transfer equations use ordinary integer subtraction. -/
structure ShortEqs (ν : ℕ) (x z u y b B c e g l m Q t lam ε : ℕ) : Prop where
  D1 : b = ε + x
  D2 : B = shortBase ν z b
  power : Q = B ^ (L4 ν)
  D6 : c = 1 + x * B + g
  D7 : Q = 1 + lam * (B - 1)
  D8 : e + 2 * z * b * l + 2 * z * B * c ^ 4 < 2 * z * Q
  D9 : (l : ℤ) = u + t * ((B : ℤ) - 2 * z)
  D10 : (e : ℤ) = y + m * ((B : ℤ) - 2 * z)

end Jones1982
