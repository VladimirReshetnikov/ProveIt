import Std

/-!
# Executable finite foundations for the gamma/iPRA development

This file imports only `Std`. It contains executable rational constructions,
kernel-checked finite arithmetic lemmas, and explicit **uninstantiated
certificate interfaces** for the remaining analysis. No analysis theorem is asserted by
an axiom, and no proof uses `sorry`, `admit`, or `native_decide`.

`Name` below is a host-Lean interface, not an object-language quantification
over primitive recursive programs. To establish the iPRA result, each fixed
primitive recursive implementation and each finite estimate still has to be
compiled into the repository's object theory. Kernel checking this file alone
does not perform that compilation and does not prove gamma analysis in iPRA.
-/

namespace GammaIPRA

/-! ## Natural-number operations and proved identities -/

/-- A structurally recursive factorial, since `Std` does not export Mathlib's. -/
def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

/-- The finite rising product `a(a+1)...(a+n-1)`; the empty product is one. -/
def rising (a : Nat) : Nat → Nat
  | 0 => 1
  | n + 1 => rising a n * (a + n)

/-- A distributivity proof using only induction and equality substitution. -/
theorem natMulAdd (a b c : Nat) : a * (b + c) = a * b + a * c := by
  induction c with
  | zero => rfl
  | succ c ih =>
    change a * (b + c) + a = a * b + (a * c + a)
    exact (congrArg (fun x => x + a) ih).trans (Nat.add_assoc _ _ _)

/-- Avoids the propositional-extensionality dependency of Std's simp proof. -/
theorem natMulAssoc (a b c : Nat) : (a * b) * c = a * (b * c) := by
  induction c with
  | zero => rfl
  | succ c ih =>
    change (a * b) * c + a * b = a * (b * c + b)
    exact (congrArg (fun x => x + a * b) ih).trans (natMulAdd a (b * c) b).symm

theorem factorial_pos (n : Nat) : 0 < factorial n := by
  induction n with
  | zero => decide
  | succ n ih =>
    exact Nat.mul_pos (Nat.succ_pos n) ih

theorem rising_one (n : Nat) : rising 1 n = factorial n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    calc
      rising 1 (n + 1) = rising 1 n * (1 + n) := rfl
      _ = factorial n * (1 + n) := congrArg (fun x => x * (1 + n)) ih
      _ = factorial n * (n + 1) := congrArg (fun x => factorial n * x) (Nat.add_comm 1 n)
      _ = (n + 1) * factorial n := Nat.mul_comm _ _
      _ = factorial (n + 1) := rfl

/-- Splitting a finite rising product at an arbitrary position. -/
theorem rising_add (a m n : Nat) :
    rising a (m + n) = rising a m * rising (a + m) n := by
  induction n with
  | zero => exact (Nat.mul_one (rising a m)).symm
  | succ n ih =>
    change rising a (m + n) * (a + (m + n)) =
      rising a m * (rising (a + m) n * ((a + m) + n))
    calc
      rising a (m + n) * (a + (m + n)) =
          (rising a m * rising (a + m) n) * (a + (m + n)) :=
        congrArg (fun x => x * (a + (m + n))) ih
      _ = rising a m * (rising (a + m) n * (a + (m + n))) :=
        natMulAssoc _ _ _
      _ = rising a m * (rising (a + m) n * ((a + m) + n)) :=
        congrArg (fun x => rising a m * (rising (a + m) n * x))
          (Nat.add_assoc a m n).symm

/-- The factorial quotient identity with all divisions cleared. -/
theorem factorial_add (m n : Nat) :
    factorial (m + n) = factorial m * rising (m + 1) n := by
  calc
    factorial (m + n) = rising 1 (m + n) := (rising_one _).symm
    _ = rising 1 m * rising (1 + m) n := rising_add 1 m n
    _ = factorial m * rising (1 + m) n :=
      congrArg (fun x => x * rising (1 + m) n) (rising_one m)
    _ = factorial m * rising (m + 1) n :=
      congrArg (fun x => factorial m * rising x n) (Nat.add_comm 1 m)

theorem factorial_dvd_add (m n : Nat) : factorial m ∣ factorial (m + n) := by
  exact ⟨rising (m + 1) n, factorial_add m n⟩

theorem rising_pos (a n : Nat) (ha : 0 < a) : 0 < rising a n := by
  induction n with
  | zero => exact Nat.zero_lt_one
  | succ n ih =>
    exact Nat.mul_pos ih (Nat.lt_of_lt_of_le ha (Nat.le_add_right a n))

/-! ## Rational complex arithmetic

Lean's `Rat` is an exact normalized fraction. Its arithmetic is executable.
Primitive recursive implementations of fraction normalization can use bounded
gcd and division; their object-iPRA certificates are not yet supplied here.
-/

def qabs (x : Rat) : Rat := if x < 0 then -x else x

structure CQ where
  re : Rat
  im : Rat
  deriving Repr, DecidableEq

namespace CQ

def zero : CQ := ⟨0, 0⟩
def one : CQ := ⟨1, 0⟩
def ofRat (x : Rat) : CQ := ⟨x, 0⟩
def ofNat (n : Nat) : CQ := ofRat (n : Rat)
def add (z w : CQ) : CQ := ⟨z.re + w.re, z.im + w.im⟩
def neg (z : CQ) : CQ := ⟨-z.re, -z.im⟩
def sub (z w : CQ) : CQ := add z (neg w)
def mul (z w : CQ) : CQ :=
  ⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩
def scale (r : Rat) (z : CQ) : CQ := ⟨r * z.re, r * z.im⟩
def conj (z : CQ) : CQ := ⟨z.re, -z.im⟩
def normSq (z : CQ) : Rat := z.re * z.re + z.im * z.im
def norm1 (z : CQ) : Rat := qabs z.re + qabs z.im

def pow (z : CQ) : Nat → CQ
  | 0 => one
  | n + 1 => mul (pow z n) z

/-- Checked input failure, rather than silently treating division by zero as valid. -/
def inverse? (z : CQ) : Option CQ :=
  if normSq z = 0 then none
  else some ⟨z.re / normSq z, -z.im / normSq z⟩

def sum (f : Nat → CQ) : Nat → CQ
  | 0 => zero
  | n + 1 => add (sum f n) (f n)

def product (f : Nat → CQ) : Nat → CQ
  | 0 => one
  | n + 1 => mul (product f n) (f n)

end CQ

def qsum (f : Nat → Rat) : Nat → Rat
  | 0 => 0
  | n + 1 => qsum f n + f n

def dyadic (p : Nat) : Rat := mkRat 1 (2 ^ p)

/-! ## Finite elementary approximants

`terms` is a count: the exponential includes exponents `0,...,terms-1`.
The following definitions do not by themselves assert their error estimates.
The paper proves those estimates; transferring them to Lean and object-iPRA
is a remaining formalization task.
-/

def expTaylor (z : CQ) (terms : Nat) : CQ :=
  CQ.sum (fun k => CQ.scale (mkRat 1 (factorial k)) (CQ.pow z k)) terms

/-- Finite atanh expansion for log(x), intended for x>0. -/
def logAtanhTaylor (x : Rat) (terms : Nat) : Rat :=
  let w := (x - 1) / (x + 1)
  2 * qsum (fun j => w ^ (2 * j + 1) / ((2 * j + 1 : Nat) : Rat)) terms

def positiveLog? (x : Rat) (terms : Nat) : Option Rat :=
  if 0 < x then some (logAtanhTaylor x terms) else none

/-- A generous exponential-tail budget for norm1(z)≤T; its proof is pending. -/
def expTermBudget (T p : Nat) : Nat := 4 * T + p + 7

/-- If |w|≤1-1/D and D≥1, this gives a generous atanh-tail budget. -/
def logTermBudget (D p : Nat) : Nat := D * (p + 2 * D + 4)

def positiveLogAt? (x : Rat) (p : Nat) : Option Rat :=
  if 0 < x then
    let w := (x - 1) / (x + 1)
    some (logAtanhTaylor x (logTermBudget w.den p))
  else none

def harmonic (N : Nat) : Rat := qsum (fun k => mkRat 1 (k + 1)) N

def harmonicPower (m N : Nat) : Rat :=
  qsum (fun k => mkRat 1 ((k + 1) ^ m)) N

/-- The finite harmonic-minus-log approximant to Euler's constant. -/
def eulerConstantApprox? (N logTerms : Nat) : Option Rat :=
  (positiveLog? (N : Rat) logTerms).map (fun l => harmonic N - l)

/-- `z ∏_{k=1}^N (1+z/k)`, evaluated exactly. -/
def eulerHead (N : Nat) (z : CQ) : CQ :=
  CQ.mul z (CQ.product
    (fun k => CQ.add CQ.one (CQ.scale (mkRat 1 (k + 1)) z)) N)

/--
A fully rational finite approximation to Q_N(z).
N=0 is rejected. Logarithm and exponential truncation lengths are explicit.
-/
def eulerReciprocalApprox? (N logTerms expTerms : Nat) (z : CQ) : Option CQ :=
  (positiveLog? (N : Rat) logTerms).map fun l =>
    CQ.mul (eulerHead N z) (expTaylor (CQ.scale (-l) z) expTerms)

/-- Invert the rational reciprocal approximant, rejecting a zero approximation. -/
def eulerGammaApprox? (N logTerms expTerms : Nat) (z : CQ) : Option CQ := do
  let q ← eulerReciprocalApprox? N logTerms expTerms z
  CQ.inverse? q

/-! ## Natural budgets from the proof

`lowerDenominator R D` is 1/λ when δ=1/(D+1). These are closed natural
expressions. The budget inequalities proved below concern those expressions;
they do not yet prove the analytic error claims for gamma.
-/

def diskMajorant (R : Nat) : Nat :=
  R * (1 + R) ^ (2 * R) * 3 ^ (2 * R * R + 2 * R)

def diskB (R : Nat) : Nat := R * R + R

def lowerDenominator (R D : Nat) : Nat :=
  (D + 1) ^ (2 * R + 1) * factorial (2 * R) * 3 ^ (2 * R * R + 2 * R)

def poleLowerBound (R D : Nat) : Rat := mkRat 1 (lowerDenominator R D)

def reciprocalCutoff (R p : Nat) : Nat :=
  max (2 * R) (max (diskB R) (3 * diskMajorant R * diskB R * 2 ^ (p + 2)))

def gammaCutoff (R D p : Nat) : Nat :=
  max (2 * R) (max (diskB R)
    (3 * diskMajorant R * diskB R * lowerDenominator R D ^ 2 * 2 ^ (p + 2)))

theorem lowerDenominator_pos (R D : Nat) : 0 < lowerDenominator R D := by
  exact Nat.mul_pos
    (Nat.mul_pos (Nat.pow_pos (Nat.succ_pos D)) (factorial_pos (2 * R)))
    (Nat.pow_pos (by decide))

theorem natLeMaxLeft (a b : Nat) : a ≤ max a b := by
  change a ≤ if a ≤ b then b else a
  split
  next h => exact h
  next _ => exact Nat.le_refl a

theorem natLeMaxRight (a b : Nat) : b ≤ max a b := by
  change b ≤ if a ≤ b then b else a
  split
  next _ => exact Nat.le_refl b
  next h => exact Nat.le_of_lt (Nat.lt_of_not_ge h)

theorem reciprocalCutoff_ge_disk (R p : Nat) : 2 * R ≤ reciprocalCutoff R p := by
  exact natLeMaxLeft _ _

theorem reciprocalCutoff_ge_B (R p : Nat) : diskB R ≤ reciprocalCutoff R p := by
  exact Nat.le_trans (natLeMaxLeft _ _) (natLeMaxRight _ _)

theorem gammaCutoff_ge_error_budget (R D p : Nat) :
    3 * diskMajorant R * diskB R * lowerDenominator R D ^ 2 * 2 ^ (p + 2)
      ≤ gammaCutoff R D p := by
  exact Nat.le_trans (natLeMaxRight _ _) (natLeMaxRight _ _)

/-! ## Host-level certificate interfaces

These are definitions and contracts. No value of `DiskAnalyticCertificate`
or `DerivativeRemainderCertificate` for gamma is constructed in this file.
Quantification over arbitrary `Name` values is confined to this metatheory
interface; the iPRA theorem scheme instantiates fixed primitive recursive
names with certified arithmetic implementations.
-/

abbrev Name := Nat → CQ

/-- The regular-name convention used in the paper. -/
def Regular (a : Name) : Prop :=
  ∀ p q, CQ.norm1 (CQ.sub (a p) (a q)) ≤ dyadic p + dyadic q

/-- Equality of the represented values, with slack for regular-name errors. -/
def NameEq (a b : Name) : Prop :=
  ∀ p, CQ.norm1 (CQ.sub (a (p + 2)) (b (p + 2))) ≤ dyadic p

/-- One finite witness sufficient to certify separation from zero. -/
def ApartAt (a : Name) (p : Nat) : Prop :=
  (2 * dyadic p) ^ 2 < CQ.normSq (a p)

def Apart (a : Name) : Prop := ∃ p, ApartAt a p

def Disk (center z : CQ) (radius : Rat) : Prop :=
  CQ.norm1 (CQ.sub z center) ≤ radius

/-- A decidable finite pole-separation test on a rational input. -/
def rationalPoleTest (z : CQ) (R D : Nat) : Bool :=
  (List.range (2 * R + 1)).all fun k =>
    decide ((mkRat 1 (D + 1)) ^ 2 ≤ CQ.normSq (CQ.add z (CQ.ofNat k)))

def namePolynomial (coeff : Nat → Name) (center z : CQ)
    (degreeCount precision : Nat) : CQ :=
  CQ.sum (fun n => CQ.mul (coeff n precision)
    (CQ.pow (CQ.sub z center) n)) degreeCount

/--
A power-series contract on a rational disk with a strictly larger coefficient
majorant radius. The outer radius prevents arbitrary polynomial approximation
from being mistaken for analyticity. All `Prop` fields remain obligations.
-/
structure DiskAnalyticCertificate (F : CQ → Name) (center : CQ) (radius : Rat) where
  radius_pos : 0 < radius
  outerRadius : Rat
  radius_lt_outer : radius < outerRadius
  majorant : Rat
  majorant_nonneg : 0 ≤ majorant
  coeff : Nat → Name
  coeff_regular : ∀ n, Regular (coeff n)
  value_regular : ∀ z, Disk center z radius → Regular (F z)
  coeff_bound : ∀ n p,
    CQ.norm1 (coeff n p) ≤ majorant / outerRadius ^ n + dyadic p
  degreeCount : Nat → Nat
  coefficientPrecision : Nat → Nat
  degree_grows : ∀ p, p < degreeCount p
  coefficient_precision_grows : ∀ p, p ≤ coefficientPrecision p
  coefficient_roundoff_budget : ∀ p,
    dyadic (coefficientPrecision p) *
      qsum (fun n => radius ^ n) (degreeCount p) ≤ dyadic p
  expansion_bound : ∀ p z, Disk center z radius →
    CQ.norm1 (CQ.sub (F z (p + 2))
      (namePolynomial coeff center z (degreeCount p) (coefficientPrecision p)))
      ≤ dyadic p

/-- Uniform continuity contract, used to extend rational-input operators to names. -/
structure ContinuityCertificate (F : CQ → Name) (center : CQ) (radius : Rat) where
  radius_pos : 0 < radius
  modulus : Nat → Nat
  value_regular : ∀ z, Disk center z radius → Regular (F z)
  continuity_bound : ∀ p z w,
    Disk center z radius → Disk center w radius →
    CQ.norm1 (CQ.sub z w) ≤ dyadic (modulus p) →
    CQ.norm1 (CQ.sub (F z (p + 3)) (F w (p + 3))) ≤ dyadic p

/--
A direct first-order Taylor remainder contract. Quadratic control in h,
together with arbitrarily small rational output error, supplies a derivative
modulus without a classical uniform-limit differentiation theorem.
-/
structure DerivativeRemainderCertificate
    (F DF : CQ → Name) (center : CQ) (radius : Rat) where
  radius_pos : 0 < radius
  quadraticConstant : Rat
  constant_nonneg : 0 ≤ quadraticConstant
  value_regular : ∀ z, Disk center z radius → Regular (F z)
  derivative_regular : ∀ z, Disk center z radius → Regular (DF z)
  evaluationPrecision : Nat → Nat
  precision_grows : ∀ p, p ≤ evaluationPrecision p
  remainder_bound : ∀ p z h,
    Disk center z radius → Disk center (CQ.add z h) radius →
    CQ.norm1 (CQ.sub
      (CQ.sub (F (CQ.add z h) (evaluationPrecision p)) (F z (evaluationPrecision p)))
      (CQ.mul h (DF z (evaluationPrecision p))))
      ≤ quadraticConstant * CQ.norm1 h ^ 2 + dyadic p

/-- A certificate for the precise kind of O(1/N) Euler estimate used in the paper. -/
structure EulerErrorCertificate (target : CQ → Name) (R D : Nat) where
  radius_pos : 0 < R
  logTerms : Nat → Nat → Nat
  expTerms : Nat → Nat → Nat
  rationalApprox : Nat → Nat → CQ → CQ
  implements_euler : ∀ N p z, 0 < N →
    CQ.norm1 z ≤ (R : Rat) → rationalPoleTest z R D = true →
    eulerGammaApprox? N (logTerms N p) (expTerms N p) z =
      some (rationalApprox N p z)
  target_regular : ∀ z, CQ.norm1 z ≤ (R : Rat) →
    rationalPoleTest z R D = true → Regular (target z)
  finite_error : ∀ p z,
    CQ.norm1 z ≤ (R : Rat) → rationalPoleTest z R D = true →
    CQ.norm1 (CQ.sub (rationalApprox (gammaCutoff R D p) p z)
      (target z (p + 2))) ≤ dyadic p

/-! ## Small reproducible computations and proof-dependency audit -/

example : factorial 6 = 720 := by decide
example : rising 3 4 = 360 := by decide

#eval factorial 10
#eval rising 3 4
#eval expTaylor (CQ.ofRat (mkRat 1 2)) 6
#eval positiveLog? 2 5
#eval eulerReciprocalApprox? 3 5 8 (CQ.ofRat (mkRat 1 2))
#eval rationalPoleTest (CQ.ofNat 1) 1 0
#eval CQ.inverse? CQ.zero

#print axioms factorial_pos
#print axioms natMulAdd
#print axioms natMulAssoc
#print axioms rising_one
#print axioms rising_add
#print axioms factorial_add
#print axioms factorial_dvd_add
#print axioms rising_pos
#print axioms lowerDenominator_pos
#print axioms natLeMaxLeft
#print axioms natLeMaxRight
#print axioms reciprocalCutoff_ge_disk
#print axioms reciprocalCutoff_ge_B
#print axioms gammaCutoff_ge_error_budget

end GammaIPRA
