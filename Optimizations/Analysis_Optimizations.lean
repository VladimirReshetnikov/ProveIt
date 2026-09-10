import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

set_option linter.missingDocs true
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true

/-!
  VladMath Optimization & Clean Extraction Suite
  Specialist Domain: Analysis (Wave 2)

  Audited & Formalized Components:
  1. The Quadratic Arctangent Identity (ArctanSquareIdentity.lean)
     - 4D lattice linearization in u = π/4, a = arctan(1/2), b = arctan(2/3), c = arctan(1/4)
     - Clean, golfed 11-term quadratic identity with vanishing Gram matrix
  2. Golfed Trigonometric Identities (TrigGoldenRatio.lean)
     - Sum-to-product identities (sin 21° + sin 39° = cos 9°, sin 9° + cos 9° = √2 cos 36°)
     - Elimination of 30-line verbose calc blocks via concise ring/linarith reasoning
     - Exact golden-ratio identity: sin 9° + sin 21° + sin 39° = φ / √2
  3. Clean, Kernel-Decidable Power and Exponential Certificates
     - Continued-fraction power certificates for log 3 / log 2 ladder
     - Pure kernel-decidable power tower evaluations (OEIS A002845)
     - Two-base integer exponent trap certificates (Leonidas Alaoglu & Paul Erdős 1944)
       purged of native_decide / Lean.ofReduceBool (strictly standard Lean 4 kernel)

  Author: Analysis Specialist (ProveIt Swarm / Wave 2)
-/

namespace VladMath

/-! ============================================================================
    1. THE QUADRATIC ARCTANGENT IDENTITY: 4D LATTICE LINEARIZATION & VANISHING SUM
   ============================================================================ -/

namespace ArctanSquare

noncomputable section

open Real

/-- Base lattice direction `u = π / 4`. -/
abbrev u : ℝ := Real.pi / 4

/-- Base lattice direction `a = arctan (1 / 2)`. -/
abbrev a : ℝ := Real.arctan ((1 : ℝ) / 2)

/-- Base lattice direction `b = arctan (2 / 3)`. -/
abbrev b : ℝ := Real.arctan ((2 : ℝ) / 3)

/-- Base lattice direction `c = arctan (1 / 4)`. -/
abbrev c : ℝ := Real.arctan ((1 : ℝ) / 4)

/-- Express `π / 2` in terms of the base lattice unit `u = π / 4`: `π / 2 = 2 * u`. -/
lemma pi_div_two_eq_two_mul_u : Real.pi / 2 = 2 * u := by
  change Real.pi / 2 = 2 * (Real.pi / 4)
  ring

/-- The arctangent addition law aimed at a stated target argument. -/
lemma arctan_add_eq {x y z : ℝ} (hxy : x * y < 1)
    (h : (x + y) / (1 - x * y) = z) :
    Real.arctan x + Real.arctan y = Real.arctan z := by
  rw [Real.arctan_add hxy, h]

/-- The arctangent duplication law aimed at a stated target argument. -/
lemma two_mul_arctan_eq {x z : ℝ} (h₁ : -1 < x) (h₂ : x < 1)
    (h : 2 * x / (1 - x ^ 2) = z) :
    2 * Real.arctan x = Real.arctan z := by
  rw [Real.two_mul_arctan h₁ h₂, h]

/-- `arctan 1` in `u = π / 4` units. -/
lemma arctan_one_eq_u : Real.arctan 1 = u := Real.arctan_one

/-- Reciprocal complement in `u = π / 4` units: `arctan (1/x) = 2*u - arctan x`. -/
lemma arctan_inv_compl {x : ℝ} (hx : 0 < x) :
    Real.arctan (1 / x) = 2 * u - Real.arctan x := by
  rw [one_div, Real.arctan_inv_of_pos hx, pi_div_two_eq_two_mul_u]

-- Linearizations of the 11 arctangent values in the (u, a, b, c) lattice:

/-- Linearization certificate: `arctan 2 = 2 * u - a`. -/
lemma arctan_two : Real.arctan (2 : ℝ) = 2 * u - a := by
  linarith [arctan_inv_compl (x := 2) (by norm_num)]

/-- Linearization certificate: `arctan 3 = u + a`. -/
lemma arctan_three : Real.arctan (3 : ℝ) = u + a := by
  have h := arctan_add_eq (x := 1) (y := 1 / 2) (z := 3) (by norm_num) (by norm_num)
  rw [arctan_one_eq_u] at h
  linarith

/-- Linearization certificate: `arctan 4 = 2 * u - c`. -/
lemma arctan_four : Real.arctan (4 : ℝ) = 2 * u - c := by
  linarith [arctan_inv_compl (x := 4) (by norm_num)]

/-- Linearization certificate: `arctan 5 = u + b`. -/
lemma arctan_five : Real.arctan (5 : ℝ) = u + b := by
  have h := arctan_add_eq (x := 1) (y := 2 / 3) (z := 5) (by norm_num) (by norm_num)
  rw [arctan_one_eq_u] at h
  linarith

/-- Linearization certificate: `arctan 7 = 3 * u - 2 * a`. -/
lemma arctan_seven : Real.arctan (7 : ℝ) = 3 * u - 2 * a := by
  have hinv' : 2 * a - Real.arctan (1 / 7) = u := by
    simpa [a, u, one_div] using Real.two_mul_arctan_inv_2_sub_arctan_inv_7
  linarith [arctan_inv_compl (x := 7) (by norm_num)]

/-- Linearization certificate: `arctan 8 = 2 * u + a - b`. -/
lemma arctan_eight : Real.arctan (8 : ℝ) = 2 * u + a - b := by
  have hsum := arctan_add_eq (x := 1 / 2) (y := 1 / 8) (z := 2 / 3) (by norm_num) (by norm_num)
  linarith [arctan_inv_compl (x := 8) (by norm_num)]

/-- Linearization certificate: `arctan 13 = u + a + c`. -/
lemma arctan_thirteen : Real.arctan (13 : ℝ) = u + a + c := by
  linarith [arctan_add_eq (x := 3) (y := 1 / 4) (z := 13) (by norm_num) (by norm_num), arctan_three]

/-- Linearization certificate: `arctan 18 = 2 * a + b`. -/
lemma arctan_eighteen : Real.arctan (18 : ℝ) = 2 * a + b := by
  have h2a := two_mul_arctan_eq (x := 1 / 2) (z := 4 / 3) (by norm_num) (by norm_num) (by norm_num)
  have hsum := arctan_add_eq (x := 4 / 3) (y := 2 / 3) (z := 18) (by norm_num) (by norm_num)
  linarith

/-- Linearization certificate: `arctan 21 = 3 * u - b - c`. -/
lemma arctan_twenty_one : Real.arctan (21 : ℝ) = 3 * u - b - c := by
  have huinv := arctan_add_eq (x := 1) (y := 1 / 21) (z := 11 / 10) (by norm_num) (by norm_num)
  rw [arctan_one_eq_u] at huinv
  have hbc := arctan_add_eq (x := 2 / 3) (y := 1 / 4) (z := 11 / 10) (by norm_num) (by norm_num)
  linarith [arctan_inv_compl (x := 21) (by norm_num)]

/-- Linearization certificate: `arctan 38 = 2 * u + a - 2 * c`. -/
lemma arctan_thirty_eight : Real.arctan (38 : ℝ) = 2 * u + a - 2 * c := by
  have h2c := two_mul_arctan_eq (x := 1 / 4) (z := 8 / 15) (by norm_num) (by norm_num) (by norm_num)
  have hsum := arctan_add_eq (x := 1 / 2) (y := 1 / 38) (z := 8 / 15) (by norm_num) (by norm_num)
  linarith [arctan_inv_compl (x := 38) (by norm_num)]

/-- Linearization certificate: `arctan 47 = 3 * u - a - b + c`. -/
lemma arctan_forty_seven : Real.arctan (47 : ℝ) = 3 * u - a - b + c := by
  have hab := arctan_add_eq (x := 1 / 2) (y := 2 / 3) (z := 7 / 4) (by norm_num) (by norm_num)
  have huc := arctan_add_eq (x := 1) (y := 1 / 4) (z := 5 / 3) (by norm_num) (by norm_num)
  rw [arctan_one_eq_u] at huc
  have hsum := arctan_add_eq (x := 5 / 3) (y := 1 / 47) (z := 7 / 4) (by norm_num) (by norm_num)
  linarith [arctan_inv_compl (x := 47) (by norm_num)]

/-- **The Quadratic Arctangent Identity**:
    The sum of the squares of the 11 linearized arctangents vanishes with exact integer coefficients:
    2939 arctan(2)^2 - 1250 arctan(3)^2 - 252 arctan(4)^2 - 360 arctan(5)^2 - 870 arctan(7)^2 +
    450 arctan(8)^2 + 84 arctan(13)^2 + 330 arctan(18)^2 - 210 arctan(21)^2 + 147 arctan(38)^2 -
    210 arctan(47)^2 = 0. -/
theorem arctan_square_identity :
    (2939 : ℝ) * Real.arctan (2 : ℝ) ^ 2 -
      1250 * Real.arctan (3 : ℝ) ^ 2 -
      252 * Real.arctan (4 : ℝ) ^ 2 -
      360 * Real.arctan (5 : ℝ) ^ 2 -
      870 * Real.arctan (7 : ℝ) ^ 2 +
      450 * Real.arctan (8 : ℝ) ^ 2 +
      84 * Real.arctan (13 : ℝ) ^ 2 +
      330 * Real.arctan (18 : ℝ) ^ 2 -
      210 * Real.arctan (21 : ℝ) ^ 2 +
      147 * Real.arctan (38 : ℝ) ^ 2 -
      210 * Real.arctan (47 : ℝ) ^ 2 = 0 := by
  rw [arctan_two, arctan_three, arctan_four, arctan_five, arctan_seven, arctan_eight,
    arctan_thirteen, arctan_eighteen, arctan_twenty_one, arctan_thirty_eight,
    arctan_forty_seven]
  ring

end

end ArctanSquare

/-! ============================================================================
    2. GOLFED TRIGONOMETRIC IDENTITIES: SUM-TO-PRODUCT & GOLDEN RATIO
   ============================================================================ -/

namespace TrigGoldenRatio

noncomputable section

open Real
open scoped goldenRatio

/-- The two off-center sine terms collapse by the sum-to-product formula:
    `sin 21° + sin 39° = cos 9°`.
    Golfed from a 15-line calc block to direct equational ring reduction. -/
lemma sin_twenty_one_add_sin_thirty_nine :
    Real.sin (7 * Real.pi / 60) + Real.sin (13 * Real.pi / 60) =
      Real.cos (Real.pi / 20) := by
  have h1 : (7 * Real.pi / 60 + 13 * Real.pi / 60) / 2 = Real.pi / 6 := by ring
  have h2 : (7 * Real.pi / 60 - 13 * Real.pi / 60) / 2 = -(Real.pi / 20) := by ring
  rw [Real.sin_add_sin, h1, h2, Real.sin_pi_div_six, Real.cos_neg]
  ring

/-- `sin 9° + cos 9° = √2 cos 36°`.
    Golfed from an 18-line calc block into a concise angle-addition reduction. -/
lemma sin_nine_add_cos_nine :
    Real.sin (Real.pi / 20) + Real.cos (Real.pi / 20) =
      √2 * Real.cos (Real.pi / 5) := by
  have hsum : Real.sin (Real.pi / 20) + Real.cos (Real.pi / 20) =
      √2 * Real.sin (Real.pi / 20 + Real.pi / 4) := by
    rw [Real.sin_add, Real.sin_pi_div_four, Real.cos_pi_div_four]
    ring_nf
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  have harg : Real.pi / 20 + Real.pi / 4 = Real.pi / 2 - Real.pi / 5 := by ring
  rw [hsum, harg, Real.sin_pi_div_two_sub]

/-- `√2 cos 36° = φ / √2`, using Mathlib's exact value for `cos (π / 5)`. -/
lemma sqrt_two_mul_cos_thirty_six :
    √2 * Real.cos (Real.pi / 5) = φ / √2 := by
  rw [Real.cos_pi_div_five, Real.goldenRatio]
  field_simp [ne_of_gt (Real.sqrt_pos_of_pos (by norm_num : (0 : ℝ) < 2))]
  ring_nf
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

/-- The golden-ratio trigonometric identity:
    `sin 9° + sin 21° + sin 39° = φ / √2`.
    Golfed from a verbose multi-step calc block into concise ring rewriting. -/
theorem sin_deg9_add_sin_deg21_add_sin_deg39 :
    Real.sin (9 * Real.pi / 180) +
        Real.sin (21 * Real.pi / 180) +
        Real.sin (39 * Real.pi / 180) = φ / √2 := by
  have h9 : 9 * Real.pi / 180 = Real.pi / 20 := by ring
  have h21 : 21 * Real.pi / 180 = 7 * Real.pi / 60 := by ring
  have h39 : 39 * Real.pi / 180 = 13 * Real.pi / 60 := by ring
  rw [h9, h21, h39, add_assoc, sin_twenty_one_add_sin_thirty_nine,
    sin_nine_add_cos_nine, sqrt_two_mul_cos_thirty_six]

end

end TrigGoldenRatio

/-! ============================================================================
    3. CLEAN, KERNEL-DECIDABLE POWER & EXPONENTIAL CERTIFICATES
   ============================================================================ -/

namespace ExponentialCertificates

set_option exponentiation.threshold 1000
set_option maxRecDepth 200000

/-- Continued fraction convergent lower bound for `log 3 / log 2` (Level 0): `2^1 < 3^1`. -/
theorem two_pow_1_lt_three_pow_1 : 2 ^ 1 < 3 ^ 1 := by decide

/-- Continued fraction convergent upper bound for `log 3 / log 2` (Level 0): `3^1 < 2^2`. -/
theorem three_pow_1_lt_two_pow_2 : 3 ^ 1 < 2 ^ 2 := by decide

/-- Continued fraction convergent upper bound for `log 3 / log 2` (Level 1): `3^5 < 2^8`. -/
theorem three_pow_5_lt_two_pow_8 : 3 ^ 5 < 2 ^ 8 := by decide

/-- Continued fraction convergent lower bound for `log 3 / log 2` (Level 2): `2^19 < 3^12`. -/
theorem two_pow_19_lt_three_pow_12 : 2 ^ 19 < 3 ^ 12 := by decide

/-- Continued fraction convergent upper bound for `log 3 / log 2` (Level 3): `3^41 < 2^65`. -/
theorem three_pow_41_lt_two_pow_65 : 3 ^ 41 < 2 ^ 65 := by decide

/-- Continued fraction convergent lower bound for `log 3 / log 2` (Level 4): `2^84 < 3^53`. -/
theorem two_pow_84_lt_three_pow_53 : 2 ^ 84 < 3 ^ 53 := by decide

/-- Tight two-base exponent lower bound (`569/359 < log 3 / log 2`)
    from the Alaoglu-Erdős (1944) integer exponent verification ladder: `2^569 < 3^359`. -/
theorem two_pow_569_lt_three_pow_359 : 2 ^ 569 < 3 ^ 359 := by decide

/-- Tight two-base exponent upper bound (`log 3 / log 2 < 485/306`)
    from the Alaoglu-Erdős (1944) integer exponent verification ladder: `3^306 < 2^485`. -/
theorem three_pow_306_lt_two_pow_485 : 3 ^ 306 < 2 ^ 485 := by decide

/-- Explicit certificate checker for two-base integer exponent trapping (Alaoglu & Erdős 1944):
    Verifies that rational enclosures `(Lp, Lq)` and `(Up, Uq)` trap `m ^ (log 3 / log 2)`
    strictly in `(a, a + 1)`, establishing that `m ^ (log 3 / log 2)` is strictly non-integral.
    Evaluated by standard Lean 4 kernel reduction without non-standard axioms. -/
def checkTrap (m a Lp Lq Up Uq : Nat) : Bool :=
  (2 ^ Lp < 3 ^ Lq) &&
  (3 ^ Uq < 2 ^ Up) &&
  (a ^ Lq < m ^ Lp) &&
  (m ^ Up < (a + 1) ^ Uq)

/-- Certified kernel-decidable non-integrality trap for `m = 3` with integer floor candidate `a = 5`. -/
theorem trap_m3 : checkTrap 3 5 19 12 8 5 = true := by decide

/-- Certified kernel-decidable non-integrality trap for `m = 5` with integer floor candidate `a = 12`. -/
theorem trap_m5 : checkTrap 5 12 19 12 65 41 = true := by decide

/-- Certified kernel-decidable non-integrality trap for `m = 6` with integer floor candidate `a = 17`. -/
theorem trap_m6 : checkTrap 6 17 19 12 65 41 = true := by decide

/-- Certified kernel-decidable non-integrality trap for `m = 7` with integer floor candidate `a = 21`. -/
theorem trap_m7 : checkTrap 7 21 19 12 65 41 = true := by decide

/-- Certified kernel-decidable non-integrality trap for `m = 10` with integer floor candidate `a = 38`. -/
theorem trap_m10 : checkTrap 10 38 19 12 65 41 = true := by decide

/-- Certified kernel-decidable non-integrality trap for `m = 100` with integer floor candidate `a = 1478`. -/
theorem trap_m100 : checkTrap 100 1478 569 359 485 306 = true := by decide

/-- Certified kernel-decidable non-integrality trap for `m = 255` with integer floor candidate `a = 6520`. -/
theorem trap_m255 : checkTrap 255 6520 569 359 485 306 = true := by decide

/-- Binary parenthesization AST for power towers. -/
inductive Expr where
  /-- Base leaf atom of a power tower expression. -/
  | atom : Expr
  /-- Binary exponentiation node combining base and exponent expressions. -/
  | pow  : Expr → Expr → Expr
deriving Repr, DecidableEq

/-- Size of a power tower expression (total number of atom leaves). -/
def Expr.size : Expr → Nat
  | atom => 1
  | pow a b => size a + size b

/-- Evaluate an expression with natural exponentiation with base 2. -/
def Expr.eval2 : Expr → Nat
  | atom => 2
  | pow a b => (eval2 a) ^ (eval2 b)

/-- Complete list of parenthesized power towers with 1 atom. -/
def p1 : List Expr := [Expr.atom]

/-- Complete list of parenthesized power towers with 2 atoms. -/
def p2 : List Expr := [Expr.pow Expr.atom Expr.atom]

/-- Complete list of parenthesized power towers with 3 atoms. -/
def p3 : List Expr := [
  Expr.pow Expr.atom (Expr.pow Expr.atom Expr.atom),
  Expr.pow (Expr.pow Expr.atom Expr.atom) Expr.atom
]

/-- Complete list of parenthesized power towers with 4 atoms. -/
def p4 : List Expr := [
  Expr.pow Expr.atom (Expr.pow Expr.atom (Expr.pow Expr.atom Expr.atom)),
  Expr.pow Expr.atom (Expr.pow (Expr.pow Expr.atom Expr.atom) Expr.atom),
  Expr.pow (Expr.pow Expr.atom Expr.atom) (Expr.pow Expr.atom Expr.atom),
  Expr.pow (Expr.pow (Expr.pow Expr.atom Expr.atom) Expr.atom) Expr.atom,
  Expr.pow (Expr.pow Expr.atom (Expr.pow Expr.atom Expr.atom)) Expr.atom
]

/-- Distinct evaluation values for length 1 power tower: `{2}`. -/
theorem p1_eval : (p1.map Expr.eval2).eraseDups = [2] := by decide

/-- Distinct evaluation values for length 2 power tower: `{4}`. -/
theorem p2_eval : (p2.map Expr.eval2).eraseDups = [4] := by decide

/-- Distinct evaluation values for length 3 power tower: `{16}`. -/
theorem p3_eval : (p3.map Expr.eval2).eraseDups = [16] := by decide

/-- Distinct evaluation values for length 4 power tower: `{65536, 256}`. -/
theorem p4_eval : (p4.map Expr.eval2).eraseDups = [65536, 256] := by decide

/-- Value count OEIS A002845(4) = 2 distinct parenthesized power tower evaluations,
    verified by standard Lean 4 kernel reduction without non-standard axioms. -/
theorem a002845_four_card : ((p4.map Expr.eval2).eraseDups).length = 2 := by decide

end ExponentialCertificates

end VladMath
