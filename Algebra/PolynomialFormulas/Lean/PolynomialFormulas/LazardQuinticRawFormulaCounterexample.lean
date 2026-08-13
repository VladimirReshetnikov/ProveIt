import PolynomialFormulas.LazardQuinticPrimitiveFifthRoot
import PolynomialFormulas.LazardQuinticVieta

/-!
# A counterexample to the raw Lazard factorization contracts

`InvariantRelations` is an equation-only interface.  On a singular Figure-3
system it can admit a tuple which is not the tuple obtained from an ordering
of the roots.  This file completes the logical audit of the old raw contracts:
the extra tuple already recorded in `LazardQuinticInvariantSystem` extends to
a genuine `RadicalCertificate` over `ℂ`, but its four computed Fourier modes
do not have the required quadratic cyclic invariant.  Consequently both
`FormulaFactors` and `RationalFormulaFactors` are false.

The non-equality is exact.  It is checked by taking the norm down the two
quadratic equations for `epsilon` and `T`; no numerical approximation or
native evaluation is used.

This conclusion must not be reversed into a proof about the pointwise
contracts.  A failed five-factor identity does not by itself imply that one
of the five displayed values is not a root: repetitions could also destroy a
multiplicity-sensitive factorization.  Thus the theorems below settle the two
`...Factors` propositions; a separate exact root-value certificate is still
needed before asserting `¬ FormulaSound` or `¬ RationalFormulaSound`.
-/

open Polynomial

namespace LeanProofs.PolynomialFormulas.LazardQuintic

set_option autoImplicit false
set_option maxRecDepth 10000

noncomputable section

private noncomputable def chosenPowRoot (n : ℕ) (hn : 0 < n) (z : ℂ) : ℂ :=
  Classical.choose (IsAlgClosed.exists_pow_nat_eq z hn)

private theorem chosenPowRoot_pow (n : ℕ) (hn : 0 < n) (z : ℂ) :
    chosenPowRoot n hn z ^ n = z :=
  Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq z hn)

/-! ## A small exact norm lemma -/

private theorem linear_ne_zero_of_sq
    {e N a b : ℂ} (he : e ^ 2 = N)
    (hnorm : a ^ 2 - N * b ^ 2 ≠ 0) :
    a + b * e ≠ 0 := by
  intro h
  apply hnorm
  calc
    a ^ 2 - N * b ^ 2 = (a - b * e) * (a + b * e) := by
      linear_combination b ^ 2 * he
    _ = 0 := by rw [h, mul_zero]

/-- A nonzero iterated quadratic norm certifies that a four-term expression
in the basis `1,e,t,e*t` is nonzero.  This is also useful for auditing the
individual root-value contracts for the same raw certificate. -/
theorem quadraticTowerLinear_ne_zero
    {e t N m0 m1 a0 a1 b0 b1 : ℂ}
    (he : e ^ 2 = N) (ht : t ^ 2 = m0 + m1 * e)
    (hnorm :
      let c0 := b0 ^ 2 + N * b1 ^ 2
      let c1 := 2 * b0 * b1
      let z0 := a0 ^ 2 + N * a1 ^ 2 - (c0 * m0 + N * c1 * m1)
      let z1 := 2 * a0 * a1 - (c0 * m1 + c1 * m0)
      z0 ^ 2 - N * z1 ^ 2 ≠ 0) :
    (a0 + a1 * e) + (b0 + b1 * e) * t ≠ 0 := by
  intro h
  let A := a0 + a1 * e
  let B := b0 + b1 * e
  let c0 := b0 ^ 2 + N * b1 ^ 2
  let c1 := 2 * b0 * b1
  let z0 := a0 ^ 2 + N * a1 ^ 2 - (c0 * m0 + N * c1 * m1)
  let z1 := 2 * a0 * a1 - (c0 * m1 + c1 * m0)
  have hab : A + B * t = 0 := by simpa [A, B] using h
  have hsquare : A ^ 2 - B ^ 2 * t ^ 2 = 0 := by
    linear_combination (A - B * t) * hab
  have hreduce : A ^ 2 - B ^ 2 * (m0 + m1 * e) = z0 + z1 * e := by
    dsimp [A, B, c0, c1, z0, z1]
    linear_combination
      (a1 ^ 2 - 2 * b0 * b1 * m1 - b1 ^ 2 * m0 -
        b1 ^ 2 * m1 * e) * he
  have hz : z0 + z1 * e = 0 := by
    rw [← hreduce, ← ht]
    exact hsquare
  apply hnorm
  calc
    z0 ^ 2 - N * z1 ^ 2 = (z0 - z1 * e) * (z0 + z1 * e) := by
      linear_combination z1 ^ 2 * he
    _ = 0 := by rw [hz, mul_zero]

/-! ## The singular raw certificate -/

/-- The rational depressed quintic before extension to `ℂ`. -/
def rawFormulaCounterexampleDepressedRat : DepressedQuintic ℚ :=
  ⟨-1, 2, 3, 1⟩

/-- The extraneous Figure-3 solution over `ℚ`. -/
def rawFormulaCounterexampleInvariantsRat : Invariants ℚ :=
  ⟨-4, -199 / 30, -79 / 30, 6, 109 / 15⟩

/-- The extraneous rational tuple exactly satisfies every raw invariant
equation. -/
theorem rawFormulaCounterexample_relations_rat :
    InvariantRelations rawFormulaCounterexampleDepressedRat
      rawFormulaCounterexampleInvariantsRat := by
  constructor <;>
    norm_num [rawFormulaCounterexampleDepressedRat,
      rawFormulaCounterexampleInvariantsRat, resolventEval, resolventCore,
      discriminant, i4SquareRhs, i4CubeRhs, i4FourthRhs, i4FifthRhs]

/-- The monic general quintic whose depressed part is the existing singular
example `X⁵ - X³ + 2X² + 3X + 1`. -/
def rawFormulaCounterexampleQuintic : GeneralQuintic ℂ :=
  ⟨1, 0, -1, 2, 3, 1⟩

/-- The extraneous invariant tuple, now viewed in the radical field. -/
def rawFormulaCounterexampleInvariants : Invariants ℂ :=
  rawFormulaCounterexampleInvariantsRat.map (algebraMap ℚ ℂ)

@[simp] theorem depress_rawFormulaCounterexampleQuintic :
    depress rawFormulaCounterexampleQuintic =
      rawFormulaCounterexampleDepressedRat.map (algebraMap ℚ ℂ) := by
  norm_num [rawFormulaCounterexampleQuintic,
    rawFormulaCounterexampleDepressedRat, depress, DepressedQuintic.map]

theorem rawFormulaCounterexample_relations :
    InvariantRelations (depress rawFormulaCounterexampleQuintic)
      rawFormulaCounterexampleInvariants := by
  rw [depress_rawFormulaCounterexampleQuintic]
  exact rawFormulaCounterexample_relations_rat.map (algebraMap ℚ ℂ)

/-- Exact values of the four derived invariants used by the radical stage. -/
theorem rawFormulaCounterexample_invariant_values :
    invariantD (depress rawFormulaCounterexampleQuintic)
          rawFormulaCounterexampleInvariants = 5449 ∧
      invariantE (depress rawFormulaCounterexampleQuintic)
          rawFormulaCounterexampleInvariants = -229 / 2 ∧
      invariantF (depress rawFormulaCounterexampleQuintic)
          rawFormulaCounterexampleInvariants = -8257 / 2 ∧
      invariantG (depress rawFormulaCounterexampleQuintic)
          rawFormulaCounterexampleInvariants = 18443 / 2 := by
  norm_num [rawFormulaCounterexampleQuintic,
    rawFormulaCounterexampleInvariants,
    rawFormulaCounterexampleInvariantsRat,
    Invariants.map, depress, invariantD, invariantE, invariantF, invariantG]

/-- The first square root.  Its square is `5D=27245`. -/
def rawFormulaCounterexampleEpsilon : ℂ :=
  chosenPowRoot 2 (by norm_num) 27245

theorem rawFormulaCounterexampleEpsilon_sq :
    rawFormulaCounterexampleEpsilon ^ 2 = 27245 :=
  chosenPowRoot_pow 2 (by norm_num) 27245

theorem rawFormulaCounterexampleEpsilon_ne_zero :
    rawFormulaCounterexampleEpsilon ≠ 0 := by
  intro h
  have he := rawFormulaCounterexampleEpsilon_sq
  rw [h] at he
  norm_num at he

private theorem rawFormulaCounterexampleEpsilon_cube :
    rawFormulaCounterexampleEpsilon ^ 3 =
      27245 * rawFormulaCounterexampleEpsilon := by
  calc
    rawFormulaCounterexampleEpsilon ^ 3 =
        rawFormulaCounterexampleEpsilon ^ 2 *
          rawFormulaCounterexampleEpsilon := by ring
    _ = 27245 * rawFormulaCounterexampleEpsilon := by
      rw [rawFormulaCounterexampleEpsilon_sq]

private theorem rawFormulaCounterexampleEpsilon_fourth :
    rawFormulaCounterexampleEpsilon ^ 4 = 27245 ^ 2 := by
  calc
    rawFormulaCounterexampleEpsilon ^ 4 =
        (rawFormulaCounterexampleEpsilon ^ 2) ^ 2 := by ring
    _ = 27245 ^ 2 := by rw [rawFormulaCounterexampleEpsilon_sq]

private theorem rawFormulaCounterexampleEpsilon_fifth :
    rawFormulaCounterexampleEpsilon ^ 5 =
      27245 ^ 2 * rawFormulaCounterexampleEpsilon := by
  calc
    rawFormulaCounterexampleEpsilon ^ 5 =
        (rawFormulaCounterexampleEpsilon ^ 2) ^ 2 *
          rawFormulaCounterexampleEpsilon := by ring
    _ = 27245 ^ 2 * rawFormulaCounterexampleEpsilon := by
      rw [rawFormulaCounterexampleEpsilon_sq]

private theorem rawFormulaCounterexampleEpsilon_sixth :
    rawFormulaCounterexampleEpsilon ^ 6 = 27245 ^ 3 := by
  calc
    rawFormulaCounterexampleEpsilon ^ 6 =
        (rawFormulaCounterexampleEpsilon ^ 2) ^ 3 := by ring
    _ = 27245 ^ 3 := by rw [rawFormulaCounterexampleEpsilon_sq]

private theorem rawFormulaCounterexampleF_div :
    (-8257 / 2 : ℂ) / rawFormulaCounterexampleEpsilon =
      (-8257 / 54490) * rawFormulaCounterexampleEpsilon := by
  have he := rawFormulaCounterexampleEpsilon_sq
  have he0 := rawFormulaCounterexampleEpsilon_ne_zero
  apply (div_eq_iff he0).2
  calc
    (-8257 / 2 : ℂ) = (-8257 / 54490) * 27245 := by norm_num
    _ = ((-8257 / 54490) * rawFormulaCounterexampleEpsilon) *
        rawFormulaCounterexampleEpsilon := by
      rw [← he]
      ring

private theorem rawFormulaCounterexample_plus_ne_zero :
    (-229 / 2 : ℂ) + (-8257 / 2) / rawFormulaCounterexampleEpsilon ≠ 0 := by
  rw [rawFormulaCounterexampleF_div]
  apply linear_ne_zero_of_sq rawFormulaCounterexampleEpsilon_sq
  norm_num

/-- The chosen square root survives Lazard's branch correction unchanged. -/
theorem rawFormulaCounterexample_correctEpsilon :
    correctEpsilon (depress rawFormulaCounterexampleQuintic)
        rawFormulaCounterexampleInvariants rawFormulaCounterexampleEpsilon =
      rawFormulaCounterexampleEpsilon := by
  rcases rawFormulaCounterexample_invariant_values with ⟨_, hE, hF, _⟩
  simp only [correctEpsilon, hE, hF]
  rw [if_neg rawFormulaCounterexample_plus_ne_zero]

/-- The second square root, chosen in `ℂ`.  The radicand has already been
reduced to the quadratic basis `1,epsilon`. -/
def rawFormulaCounterexampleT : ℂ :=
  chosenPowRoot 2 (by norm_num)
    (-1145 / 4 - (8257 / 21796) * rawFormulaCounterexampleEpsilon)

theorem rawFormulaCounterexampleT_sq :
    rawFormulaCounterexampleT ^ 2 =
      (-1145 / 4 : ℂ) +
        (-8257 / 21796) * rawFormulaCounterexampleEpsilon := by
  calc
    rawFormulaCounterexampleT ^ 2 =
        -1145 / 4 - (8257 / 21796) * rawFormulaCounterexampleEpsilon :=
      chosenPowRoot_pow 2 (by norm_num)
        (-1145 / 4 - (8257 / 21796) * rawFormulaCounterexampleEpsilon)
    _ = (-1145 / 4 : ℂ) +
        (-8257 / 21796) * rawFormulaCounterexampleEpsilon := by ring

private theorem rawFormulaCounterexampleT_cube :
    rawFormulaCounterexampleT ^ 3 =
      ((-1145 / 4 : ℂ) +
          (-8257 / 21796) * rawFormulaCounterexampleEpsilon) *
        rawFormulaCounterexampleT := by
  calc
    rawFormulaCounterexampleT ^ 3 = rawFormulaCounterexampleT ^ 2 *
        rawFormulaCounterexampleT := by ring
    _ = ((-1145 / 4 : ℂ) +
          (-8257 / 21796) * rawFormulaCounterexampleEpsilon) *
        rawFormulaCounterexampleT := by
      rw [rawFormulaCounterexampleT_sq]

private theorem rawFormulaCounterexampleT_radicand_ne_zero :
    (-1145 / 4 : ℂ) +
        (-8257 / 21796) * rawFormulaCounterexampleEpsilon ≠ 0 := by
  apply linear_ne_zero_of_sq rawFormulaCounterexampleEpsilon_sq
  norm_num

theorem rawFormulaCounterexampleT_ne_zero :
    rawFormulaCounterexampleT ≠ 0 := by
  intro h
  apply rawFormulaCounterexampleT_radicand_ne_zero
  rw [← rawFormulaCounterexampleT_sq, h]
  norm_num

private theorem rawFormulaCounterexampleT_square_formula :
    rawFormulaCounterexampleT ^ 2 =
      (5 / 2) *
        (invariantE (depress rawFormulaCounterexampleQuintic)
            rawFormulaCounterexampleInvariants +
          invariantF (depress rawFormulaCounterexampleQuintic)
              rawFormulaCounterexampleInvariants /
            correctEpsilon (depress rawFormulaCounterexampleQuintic)
              rawFormulaCounterexampleInvariants
              rawFormulaCounterexampleEpsilon) := by
  rcases rawFormulaCounterexample_invariant_values with ⟨_, hE, hF, _⟩
  rw [rawFormulaCounterexampleT_sq,
    rawFormulaCounterexample_correctEpsilon, hE, hF,
    rawFormulaCounterexampleF_div]
  ring

/-- The exact `1,epsilon` coefficient form of `U`. -/
theorem rawFormulaCounterexampleU_normal :
    radicalU (depress rawFormulaCounterexampleQuintic)
        rawFormulaCounterexampleInvariants rawFormulaCounterexampleEpsilon
        rawFormulaCounterexampleT =
      ((8257 / 36886 : ℂ) -
          (229 / 36886) * rawFormulaCounterexampleEpsilon) *
        rawFormulaCounterexampleT := by
  rcases rawFormulaCounterexample_invariant_values with ⟨_, _, _, hG⟩
  rw [radicalU, hG]
  apply (div_eq_iff (mul_ne_zero rawFormulaCounterexampleT_ne_zero
    rawFormulaCounterexampleEpsilon_ne_zero)).2
  ring_nf
  rw [rawFormulaCounterexampleT_sq]
  ring_nf
  rw [rawFormulaCounterexampleEpsilon_cube,
    rawFormulaCounterexampleEpsilon_sq]
  ring

private theorem rawFormulaCounterexampleU_square_formula :
    (radicalU (depress rawFormulaCounterexampleQuintic)
        rawFormulaCounterexampleInvariants rawFormulaCounterexampleEpsilon
        rawFormulaCounterexampleT) ^ 2 =
      (5 / 2) *
        (invariantE (depress rawFormulaCounterexampleQuintic)
            rawFormulaCounterexampleInvariants -
          invariantF (depress rawFormulaCounterexampleQuintic)
              rawFormulaCounterexampleInvariants /
            correctEpsilon (depress rawFormulaCounterexampleQuintic)
              rawFormulaCounterexampleInvariants
              rawFormulaCounterexampleEpsilon) := by
  rcases rawFormulaCounterexample_invariant_values with ⟨_, hE, hF, _⟩
  rw [rawFormulaCounterexampleU_normal,
    rawFormulaCounterexample_correctEpsilon, hE, hF,
    rawFormulaCounterexampleF_div]
  rw [mul_pow, rawFormulaCounterexampleT_sq]
  ring_nf
  rw [rawFormulaCounterexampleEpsilon_cube,
    rawFormulaCounterexampleEpsilon_sq]
  ring

/-- The initial coherent quadratic triple used by the counterexample. -/
def rawFormulaCounterexampleInitial : QuadraticTriple ℂ :=
  ⟨rawFormulaCounterexampleEpsilon, rawFormulaCounterexampleT,
    radicalU (depress rawFormulaCounterexampleQuintic)
      rawFormulaCounterexampleInvariants rawFormulaCounterexampleEpsilon
      rawFormulaCounterexampleT⟩

set_option maxHeartbeats 1000000 in
/-- The exact quadratic-tower normal form of the selected fifth-power
radicand. -/
theorem rawFormulaCounterexample_q1_normal :
    q1 (depress rawFormulaCounterexampleQuintic)
        rawFormulaCounterexampleInvariants rawFormulaCounterexampleInitial =
      ((-1525 / 3 : ℂ) +
          (154025 / 65388) * rawFormulaCounterexampleEpsilon) +
        ((395597225 / 50681364 : ℂ) +
            (26335 / 221316) * rawFormulaCounterexampleEpsilon) *
          rawFormulaCounterexampleT := by
  rw [rawFormulaCounterexampleInitial, q1, rawFormulaCounterexampleU_normal]
  norm_num [rawFormulaCounterexampleQuintic,
    rawFormulaCounterexampleInvariants,
    rawFormulaCounterexampleInvariantsRat,
    Invariants.map, depress, invariantE, invariantH, invariantI, invariantJ,
    invariantK]
  field_simp [rawFormulaCounterexampleEpsilon_ne_zero]
  ring_nf
  rw [rawFormulaCounterexampleEpsilon_sq]
  ring

set_option maxHeartbeats 1000000 in
private theorem rawFormulaCounterexample_q1_ne_zero :
    q1 (depress rawFormulaCounterexampleQuintic)
        rawFormulaCounterexampleInvariants rawFormulaCounterexampleInitial ≠ 0 := by
  rw [rawFormulaCounterexample_q1_normal]
  apply quadraticTowerLinear_ne_zero
    rawFormulaCounterexampleEpsilon_sq rawFormulaCounterexampleT_sq
  norm_num

/-- A fifth root of the selected nonzero radicand. -/
def rawFormulaCounterexampleP1 : ℂ :=
  chosenPowRoot 5 (by norm_num)
    (q1 (depress rawFormulaCounterexampleQuintic)
      rawFormulaCounterexampleInvariants rawFormulaCounterexampleInitial)

theorem rawFormulaCounterexampleP1_pow :
    rawFormulaCounterexampleP1 ^ 5 =
      q1 (depress rawFormulaCounterexampleQuintic)
        rawFormulaCounterexampleInvariants rawFormulaCounterexampleInitial :=
  chosenPowRoot_pow 5 (by norm_num) _

theorem rawFormulaCounterexampleP1_ne_zero :
    rawFormulaCounterexampleP1 ≠ 0 := by
  intro h
  apply rawFormulaCounterexample_q1_ne_zero
  rw [← rawFormulaCounterexampleP1_pow, h]
  norm_num

/-- All fields of `RadicalCertificate` are genuinely inhabited; the defect is
not a missing radical but the extraneous invariant tuple admitted upstream. -/
def rawFormulaCounterexampleRadicalCertificate :
    RadicalCertificate (depress rawFormulaCounterexampleQuintic)
      rawFormulaCounterexampleInvariants where
  epsilon0 := rawFormulaCounterexampleEpsilon
  epsilon0_square := by
    rcases rawFormulaCounterexample_invariant_values with ⟨hD, _, _, _⟩
    rw [hD, rawFormulaCounterexampleEpsilon_sq]
    norm_num
  epsilon0_nonzero := rawFormulaCounterexampleEpsilon_ne_zero
  epsilon_branches := Or.inl (by
    rcases rawFormulaCounterexample_invariant_values with ⟨_, hE, hF, _⟩
    simpa only [hE, hF] using rawFormulaCounterexample_plus_ne_zero)
  t := rawFormulaCounterexampleT
  t_square := rawFormulaCounterexampleT_square_formula
  u_square := by
    simpa only [rawFormulaCounterexample_correctEpsilon] using
      rawFormulaCounterexampleU_square_formula
  invariantE_nonzero := by
    rcases rawFormulaCounterexample_invariant_values with ⟨_, hE, _, _⟩
    rw [hE]
    norm_num
  branch := .base
  branch_nonzero := by
    change q1 (depress rawFormulaCounterexampleQuintic)
      rawFormulaCounterexampleInvariants
      (branchTriple
        ⟨correctEpsilon (depress rawFormulaCounterexampleQuintic)
            rawFormulaCounterexampleInvariants rawFormulaCounterexampleEpsilon,
          rawFormulaCounterexampleT,
          radicalU (depress rawFormulaCounterexampleQuintic)
            rawFormulaCounterexampleInvariants
            (correctEpsilon (depress rawFormulaCounterexampleQuintic)
              rawFormulaCounterexampleInvariants
              rawFormulaCounterexampleEpsilon)
            rawFormulaCounterexampleT⟩ .base) ≠ 0
    rw [rawFormulaCounterexample_correctEpsilon]
    simpa [branchTriple, rawFormulaCounterexampleInitial] using
      rawFormulaCounterexample_q1_ne_zero
  p1 := rawFormulaCounterexampleP1
  p1_power := by
    rw [rawFormulaCounterexample_correctEpsilon]
    simpa [branchTriple, rawFormulaCounterexampleInitial] using
      rawFormulaCounterexampleP1_pow

/-- The primitive fifth root used to expose all five inverse-Fourier outputs. -/
def rawFormulaCounterexampleOmega : FifthRootOfUnity ℂ :=
  ⟨squareRadicalPrimitiveFifthRoot,
    squareRadicalPrimitiveFifthRoot_primitive⟩

/-! ## The failed cyclic identity -/

set_option maxHeartbeats 4000000 in
/-- The exact quadratic-tower normal form of
`(fourierCyclic2 - 5) * p1^5`. -/
theorem rawFormulaCounterexample_cyclicCross_normal :
    let d := rawFormulaCounterexampleRadicalCertificate
    let a := d.p1
    let b := fourierP2 (depress rawFormulaCounterexampleQuintic)
      rawFormulaCounterexampleInvariants d.chosen d.p1
    let c := fourierP3 (depress rawFormulaCounterexampleQuintic)
      rawFormulaCounterexampleInvariants d.chosen d.p1
    let e4 := fourierP4 (depress rawFormulaCounterexampleQuintic)
      rawFormulaCounterexampleInvariants d.chosen d.p1
    (fourierCyclic2 a b c e4 - 5) * d.p1 ^ 5 =
      ((-38098429355 / 59895408 : ℂ) +
          (152610097075 / 20574072648) *
            rawFormulaCounterexampleEpsilon) +
        ((-52370841005 / 304088184 : ℂ) +
            (-61060513463 / 552325504872) *
              rawFormulaCounterexampleEpsilon) *
          rawFormulaCounterexampleT := by
  dsimp
  simp only [rawFormulaCounterexampleRadicalCertificate,
    RadicalCertificate.chosen, RadicalCertificate.initial, branchTriple,
    rawFormulaCounterexample_correctEpsilon]
  rw [rawFormulaCounterexampleP1_pow,
    rawFormulaCounterexample_q1_normal]
  rw [rawFormulaCounterexampleU_normal]
  norm_num [rawFormulaCounterexampleQuintic,
    rawFormulaCounterexampleInvariants,
    rawFormulaCounterexampleInvariantsRat,
    Invariants.map, depress, fourierCyclic2, fourierP2, fourierP3, fourierP4,
    p21, p22, p23, p24, p31, p32, p33, p34, p41, p42, invariantE]
  field_simp [rawFormulaCounterexampleEpsilon_ne_zero,
    rawFormulaCounterexampleT_ne_zero,
    rawFormulaCounterexampleP1_ne_zero,
    rawFormulaCounterexample_q1_ne_zero]
  rw [rawFormulaCounterexampleP1_pow,
    rawFormulaCounterexample_q1_normal]
  ring_nf
  rw [rawFormulaCounterexampleT_cube]
  ring_nf
  rw [rawFormulaCounterexampleEpsilon_sixth,
    rawFormulaCounterexampleEpsilon_fifth,
    rawFormulaCounterexampleEpsilon_fourth,
    rawFormulaCounterexampleEpsilon_cube,
    rawFormulaCounterexampleEpsilon_sq]
  ring_nf
  rw [rawFormulaCounterexampleT_sq]
  ring_nf
  rw [rawFormulaCounterexampleEpsilon_sq]
  ring

set_option maxHeartbeats 1000000 in
/-- The displayed normal form of `(fourierCyclic2 - 5) * p1^5` is nonzero. -/
theorem rawFormulaCounterexample_cyclicCross_ne_zero :
    ((-38098429355 / 59895408 : ℂ) +
        (152610097075 / 20574072648) *
          rawFormulaCounterexampleEpsilon) +
      ((-52370841005 / 304088184 : ℂ) +
          (-61060513463 / 552325504872) *
            rawFormulaCounterexampleEpsilon) *
        rawFormulaCounterexampleT ≠ 0 := by
  -- Clear the harmless common scalar before applying the exact tower norm.
  suffices
      ((-10050177832905 : ℂ) +
          117198809950 * rawFormulaCounterexampleEpsilon) +
        ((-2721135732910 : ℂ) +
            (-1746729102) * rawFormulaCounterexampleEpsilon) *
          rawFormulaCounterexampleT ≠ 0 by
    intro h
    apply this
    linear_combination (758895243694128 / 48031 : ℂ) * h
  apply quadraticTowerLinear_ne_zero
    rawFormulaCounterexampleEpsilon_sq rawFormulaCounterexampleT_sq
  norm_num

theorem rawFormulaCounterexample_not_cyclic2 :
    let d := rawFormulaCounterexampleRadicalCertificate
    fourierCyclic2 d.p1
        (fourierP2 (depress rawFormulaCounterexampleQuintic)
          rawFormulaCounterexampleInvariants d.chosen d.p1)
        (fourierP3 (depress rawFormulaCounterexampleQuintic)
          rawFormulaCounterexampleInvariants d.chosen d.p1)
        (fourierP4 (depress rawFormulaCounterexampleQuintic)
          rawFormulaCounterexampleInvariants d.chosen d.p1) ≠ 5 := by
  dsimp
  intro h
  apply rawFormulaCounterexample_cyclicCross_ne_zero
  rw [← rawFormulaCounterexample_cyclicCross_normal, h]
  ring

/-! ## Refuting the two factorization contracts -/

private theorem coeff_three_prod_linear (r : Fin 5 → ℂ) :
    (∏ k : Fin 5, (X - C (r k))).coeff 3 = fiveESymm2 r := by
  have hpoly :
      ∏ k : Fin 5, (X - C (r k)) =
        X ^ 5 - C (fiveESymm1 r) * X ^ 4 +
          C (fiveESymm2 r) * X ^ 3 -
          C (fiveESymm3 r) * X ^ 2 +
          C (fiveESymm4 r) * X - C (fiveESymm5 r) := by
    rw [Fin.prod_univ_five]
    simp only [fiveESymm1, fiveESymm2, fiveESymm3, fiveESymm4,
      fiveESymm5, map_add, map_mul]
    ring
  rw [hpoly]
  simp

private theorem rawFormulaCounterexample_factorization_false
    (h : rawFormulaCounterexampleQuintic.polynomial =
      C rawFormulaCounterexampleQuintic.a *
        ∏ k : Fin 5,
          (X - C (solveGeneral rawFormulaCounterexampleQuintic
            rawFormulaCounterexampleInvariants
            rawFormulaCounterexampleRadicalCertificate
            rawFormulaCounterexampleOmega k))) : False := by
  let d := rawFormulaCounterexampleRadicalCertificate
  let a := d.p1
  let b := fourierP2 (depress rawFormulaCounterexampleQuintic)
    rawFormulaCounterexampleInvariants d.chosen d.p1
  let c := fourierP3 (depress rawFormulaCounterexampleQuintic)
    rawFormulaCounterexampleInvariants d.chosen d.p1
  let e4 := fourierP4 (depress rawFormulaCounterexampleQuintic)
    rawFormulaCounterexampleInvariants d.chosen d.p1
  have hcoeff := congrArg (fun p : ℂ[X] => p.coeff 3) h
  have hleft : rawFormulaCounterexampleQuintic.polynomial.coeff 3 = -1 := by
    norm_num [rawFormulaCounterexampleQuintic,
      GeneralQuintic.polynomial, Polynomial.coeff_one]
  have hright :
      (C rawFormulaCounterexampleQuintic.a *
          ∏ k : Fin 5,
            (X - C (solveGeneral rawFormulaCounterexampleQuintic
              rawFormulaCounterexampleInvariants d
              rawFormulaCounterexampleOmega k))).coeff 3 =
        fiveESymm2 (solveGeneral rawFormulaCounterexampleQuintic
          rawFormulaCounterexampleInvariants d
          rawFormulaCounterexampleOmega) := by
    rw [show C rawFormulaCounterexampleQuintic.a = (1 : ℂ[X]) by
      norm_num [rawFormulaCounterexampleQuintic]]
    rw [one_mul]
    exact coeff_three_prod_linear _
  have hesymm :
      fiveESymm2 (solveGeneral rawFormulaCounterexampleQuintic
        rawFormulaCounterexampleInvariants d rawFormulaCounterexampleOmega) =
        -1 := by
    calc
      fiveESymm2 (solveGeneral rawFormulaCounterexampleQuintic
          rawFormulaCounterexampleInvariants d rawFormulaCounterexampleOmega) =
          (C rawFormulaCounterexampleQuintic.a *
            ∏ k : Fin 5,
              (X - C (solveGeneral rawFormulaCounterexampleQuintic
                rawFormulaCounterexampleInvariants d
                rawFormulaCounterexampleOmega k))).coeff 3 := hright.symm
      _ = rawFormulaCounterexampleQuintic.polynomial.coeff 3 := hcoeff.symm
      _ = -1 := hleft
  have hinverse :
      solveGeneral rawFormulaCounterexampleQuintic
          rawFormulaCounterexampleInvariants d rawFormulaCounterexampleOmega =
        fun k => inverseFourier rawFormulaCounterexampleOmega.value a b c e4 k := by
    funext k
    simp only [solveGeneral, rawFormulaCounterexampleQuintic]
    norm_num
    exact solveDepressed_eq_inverseFourier
      (depress rawFormulaCounterexampleQuintic)
      rawFormulaCounterexampleInvariants d rawFormulaCounterexampleOmega k
  have hvieta := inverseFourier_esymm2 rawFormulaCounterexampleOmega a b c e4
  rw [hinverse] at hesymm
  have hcyclic : fourierCyclic2 a b c e4 = 5 := by
    rw [hesymm] at hvieta
    linear_combination (5 : ℂ) * hvieta
  exact rawFormulaCounterexample_not_cyclic2 hcyclic

/-- The raw field-generic factorization proposition is false. -/
theorem not_FormulaFactors_complex :
    ¬ FormulaFactors (K := ℂ) := by
  intro h
  exact rawFormulaCounterexample_factorization_false
    (h rawFormulaCounterexampleQuintic (by norm_num [rawFormulaCounterexampleQuintic])
      rawFormulaCounterexampleInvariants rawFormulaCounterexample_relations
      rawFormulaCounterexampleRadicalCertificate rawFormulaCounterexampleOmega)

/-- Rational coefficients and a genuinely rational invariant certificate do
not repair the omitted root-origin/Fourier premise. -/
theorem not_RationalFormulaFactors :
    ¬ RationalFormulaFactors.{0} := by
  intro h
  let cQ : GeneralQuintic ℚ := ⟨1, 0, -1, 2, 3, 1⟩
  let w : RationalInvariantCertificate cQ :=
    ⟨rawFormulaCounterexampleInvariantsRat, by
      simpa [cQ, depress, rawFormulaCounterexampleDepressedRat] using
        rawFormulaCounterexample_relations_rat⟩
  have hc : cQ.map (algebraMap ℚ ℂ) = rawFormulaCounterexampleQuintic := by
    norm_num [cQ, GeneralQuintic.map, rawFormulaCounterexampleQuintic]
  have hw : w.values.map (algebraMap ℚ ℂ) =
      rawFormulaCounterexampleInvariants := by
    rfl
  have hC := h (L := ℂ) cQ (by norm_num [cQ]) w
  simp only [solveRational] at hC
  rw [hc, hw] at hC
  have hfac := hC rawFormulaCounterexampleRadicalCertificate
    rawFormulaCounterexampleOmega
  apply rawFormulaCounterexample_factorization_false
  simpa [cQ, rawFormulaCounterexampleQuintic] using hfac

end

end LeanProofs.PolynomialFormulas.LazardQuintic
