import PolynomialFormulas.LazardQuinticRawFormulaCounterexample

/-!
# A pointwise counterexample to the raw Lazard formula contracts

The equation-only `InvariantRelations` interface admits a singular extraneous
tuple.  The companion module constructs all of its radicals and proves that
the resulting inverse-Fourier tuple has the wrong second elementary symmetric
coefficient.  That already refutes factorization, but it does not alone refute
pointwise soundness because five roots may be repeated.

Here the stronger failure is proved exactly.  If all five displayed values
annihilated `X⁵ - X³ + 2X² + 3X + 1`, then the sum of those five
evaluations would vanish.  Newton's identities and the inverse-Fourier Vieta
formulas reduce that sum to

`C₅/625 + C₂*C₃/25 - 3*C₃/25 + 4*C₂/5 + 5`,

where `C₂,C₃,C₅` are the cyclic Fourier expressions.  After clearing
the nonzero fifth-root radicand, this element lies in the four-dimensional
quadratic tower `ℚ(epsilon,T)`.  An explicit iterated norm proves it nonzero.
No floating-point calculation or native evaluation is used.
-/

namespace LeanProofs.PolynomialFormulas.LazardQuintic

set_option autoImplicit false
set_option maxRecDepth 10000

noncomputable section

/-! ## A generic sum-of-evaluations identity -/

/-- Newton's identities specialized to a depressed monic quintic and five
values.  This fully expanded form is independent of any root hypothesis. -/
theorem sum_depressedQuintic_eval_five
    (c : DepressedQuintic ℂ) (r : Fin 5 → ℂ) :
    ∑ k : Fin 5, c.eval (r k) =
      fiveESymm1 r ^ 5 -
        5 * fiveESymm1 r ^ 3 * fiveESymm2 r +
        5 * fiveESymm1 r ^ 2 * fiveESymm3 r +
        5 * fiveESymm1 r * fiveESymm2 r ^ 2 -
        5 * fiveESymm1 r * fiveESymm4 r -
        5 * fiveESymm2 r * fiveESymm3 r +
        5 * fiveESymm5 r +
        c.p * (fiveESymm1 r ^ 3 -
          3 * fiveESymm1 r * fiveESymm2 r + 3 * fiveESymm3 r) +
        c.q * (fiveESymm1 r ^ 2 - 2 * fiveESymm2 r) +
        c.r * fiveESymm1 r + 5 * c.s := by
  rw [show (∑ k : Fin 5, c.eval (r k)) =
      c.eval (r 0) + c.eval (r 1) + c.eval (r 2) +
        c.eval (r 3) + c.eval (r 4) by
    exact Fin.sum_univ_five _]
  simp only [DepressedQuintic.eval, fiveESymm1, fiveESymm2,
    fiveESymm3, fiveESymm4, fiveESymm5]
  ring

/-- The preceding Newton identity in cyclic-Fourier coordinates for the
concrete depressed polynomial used by the counterexample. -/
theorem sum_rawFormulaCounterexample_inverseFourier_eval
    (omega : FifthRootOfUnity ℂ) (a b c d : ℂ) :
    let roots := fun k ↦ inverseFourier omega.value a b c d k
    ∑ k : Fin 5,
        (depress rawFormulaCounterexampleQuintic).eval (roots k) =
      fourierCyclic5 a b c d / 625 +
        fourierCyclic2 a b c d * fourierCyclic3 a b c d / 25 -
        3 * fourierCyclic3 a b c d / 25 +
        4 * fourierCyclic2 a b c d / 5 + 5 := by
  dsimp only
  rw [sum_depressedQuintic_eval_five,
    inverseFourier_esymm1, inverseFourier_esymm2,
    inverseFourier_esymm3, inverseFourier_esymm5]
  norm_num [rawFormulaCounterexampleQuintic, depress]
  ring

/-! ## Exact reduction inside the quadratic tower -/

private def soundCounterexampleQ : ℂ :=
  ((-1525 / 3 : ℂ) +
      (154025 / 65388) * rawFormulaCounterexampleEpsilon) +
    ((395597225 / 50681364 : ℂ) +
        (26335 / 221316) * rawFormulaCounterexampleEpsilon) *
      rawFormulaCounterexampleT

private def soundCounterexampleB : ℂ :=
  ((-145 / 2 : ℂ) +
      (9543 / 21796) * rawFormulaCounterexampleEpsilon) +
    ((18821615 / 25340682 : ℂ) -
        (395 / 36886) * rawFormulaCounterexampleEpsilon) *
      rawFormulaCounterexampleT

private def soundCounterexampleC : ℂ :=
  ((-25 / 2 : ℂ) -
      (2423 / 65388) * rawFormulaCounterexampleEpsilon) +
    ((-1171838 / 12670341 : ℂ) -
        (278 / 55329) * rawFormulaCounterexampleEpsilon) *
      rawFormulaCounterexampleT

private def soundCounterexampleD : ℂ :=
  (5 / 2 : ℂ) -
    (5093 / 163470) * rawFormulaCounterexampleEpsilon

private theorem soundCounterexampleQ_eq :
    q1 (depress rawFormulaCounterexampleQuintic)
        rawFormulaCounterexampleInvariants rawFormulaCounterexampleInitial =
      soundCounterexampleQ := by
  exact rawFormulaCounterexample_q1_normal

set_option maxHeartbeats 2000000 in
private theorem soundCounterexampleBCD_eq :
    let d := rawFormulaCounterexampleRadicalCertificate
    let v := d.chosen
    let p1 := d.p1
    fourierP2 (depress rawFormulaCounterexampleQuintic)
          rawFormulaCounterexampleInvariants v p1 * p1 ^ 3 =
        soundCounterexampleB ∧
      fourierP3 (depress rawFormulaCounterexampleQuintic)
          rawFormulaCounterexampleInvariants v p1 * p1 ^ 2 =
        soundCounterexampleC ∧
      fourierP4 (depress rawFormulaCounterexampleQuintic)
          rawFormulaCounterexampleInvariants v p1 * p1 =
        soundCounterexampleD := by
  dsimp
  simp only [RadicalCertificate.chosen,
    rawFormulaCounterexampleRadicalCertificate,
    RadicalCertificate.initial, rawFormulaCounterexample_correctEpsilon,
    branchTriple]
  change
    fourierP2 (depress rawFormulaCounterexampleQuintic)
          rawFormulaCounterexampleInvariants rawFormulaCounterexampleInitial
          rawFormulaCounterexampleP1 * rawFormulaCounterexampleP1 ^ 3 =
        soundCounterexampleB ∧
      fourierP3 (depress rawFormulaCounterexampleQuintic)
          rawFormulaCounterexampleInvariants rawFormulaCounterexampleInitial
          rawFormulaCounterexampleP1 * rawFormulaCounterexampleP1 ^ 2 =
        soundCounterexampleC ∧
      fourierP4 (depress rawFormulaCounterexampleQuintic)
          rawFormulaCounterexampleInvariants rawFormulaCounterexampleInitial
          rawFormulaCounterexampleP1 * rawFormulaCounterexampleP1 =
        soundCounterexampleD
  unfold rawFormulaCounterexampleInitial
  rw [rawFormulaCounterexampleU_normal]
  rcases rawFormulaCounterexample_invariant_values with ⟨_, hE, _, _⟩
  norm_num [rawFormulaCounterexampleQuintic,
    rawFormulaCounterexampleInvariants, rawFormulaCounterexampleInvariantsRat,
    Invariants.map, depress, fourierP2, fourierP3, fourierP4,
    p21, p22, p23, p24, p31, p32, p33, p34, p41, p42,
    soundCounterexampleB, soundCounterexampleC, soundCounterexampleD,
    invariantE, hE]
  field_simp [rawFormulaCounterexampleEpsilon_ne_zero,
    rawFormulaCounterexampleP1_ne_zero]
  ring_nf
  rw [rawFormulaCounterexampleEpsilon_sq]
  norm_num
  constructor
  · ring
  · constructor <;> ring

private def soundCounterexampleA2 : ℂ :=
  soundCounterexampleQ * soundCounterexampleD +
    soundCounterexampleB * soundCounterexampleC

private def soundCounterexampleA3 : ℂ :=
  soundCounterexampleQ * soundCounterexampleC ^ 2 * soundCounterexampleD +
    soundCounterexampleQ * soundCounterexampleB * soundCounterexampleD ^ 2 +
    soundCounterexampleQ * soundCounterexampleB ^ 2 +
    soundCounterexampleQ ^ 2 * soundCounterexampleC

private def soundCounterexampleA5 : ℂ :=
  soundCounterexampleQ ^ 3 * soundCounterexampleD ^ 5 +
    soundCounterexampleQ ^ 2 * soundCounterexampleC ^ 5 -
    5 * soundCounterexampleQ ^ 2 * soundCounterexampleB *
      soundCounterexampleC ^ 3 * soundCounterexampleD +
    5 * soundCounterexampleQ ^ 2 * soundCounterexampleB ^ 2 *
      soundCounterexampleC * soundCounterexampleD ^ 2 +
    5 * soundCounterexampleQ ^ 3 * soundCounterexampleC ^ 2 *
      soundCounterexampleD ^ 2 -
    5 * soundCounterexampleQ ^ 3 * soundCounterexampleB *
      soundCounterexampleD ^ 3 +
    soundCounterexampleQ * soundCounterexampleB ^ 5 -
    5 * soundCounterexampleQ ^ 2 * soundCounterexampleB ^ 3 *
      soundCounterexampleC +
    5 * soundCounterexampleQ ^ 3 * soundCounterexampleB *
      soundCounterexampleC ^ 2 +
    5 * soundCounterexampleQ ^ 3 * soundCounterexampleB ^ 2 *
      soundCounterexampleD -
    5 * soundCounterexampleQ ^ 4 * soundCounterexampleC *
      soundCounterexampleD +
    soundCounterexampleQ ^ 5

private theorem soundCounterexample_cyclic_cleared :
    let d := rawFormulaCounterexampleRadicalCertificate
    let a := d.p1
    let b := fourierP2 (depress rawFormulaCounterexampleQuintic)
      rawFormulaCounterexampleInvariants d.chosen d.p1
    let c := fourierP3 (depress rawFormulaCounterexampleQuintic)
      rawFormulaCounterexampleInvariants d.chosen d.p1
    let e4 := fourierP4 (depress rawFormulaCounterexampleQuintic)
      rawFormulaCounterexampleInvariants d.chosen d.p1
    fourierCyclic2 a b c e4 * d.p1 ^ 5 = soundCounterexampleA2 ∧
      fourierCyclic3 a b c e4 * d.p1 ^ 10 = soundCounterexampleA3 ∧
      fourierCyclic5 a b c e4 * d.p1 ^ 20 = soundCounterexampleA5 := by
  dsimp
  simp only [RadicalCertificate.chosen,
    rawFormulaCounterexampleRadicalCertificate,
    RadicalCertificate.initial, rawFormulaCounterexample_correctEpsilon,
    branchTriple]
  rcases soundCounterexampleBCD_eq with ⟨hb, hc, hd⟩
  simp only [RadicalCertificate.chosen,
    rawFormulaCounterexampleRadicalCertificate,
    RadicalCertificate.initial, rawFormulaCounterexample_correctEpsilon,
    branchTriple] at hb hc hd
  have hp5 : rawFormulaCounterexampleP1 ^ 5 = soundCounterexampleQ := by
    rw [rawFormulaCounterexampleP1_pow, soundCounterexampleQ_eq]
  have hp10 : rawFormulaCounterexampleP1 ^ 10 = soundCounterexampleQ ^ 2 := by
    calc
      rawFormulaCounterexampleP1 ^ 10 =
          (rawFormulaCounterexampleP1 ^ 5) ^ 2 := by ring
      _ = soundCounterexampleQ ^ 2 := by rw [hp5]
  have hp20 : rawFormulaCounterexampleP1 ^ 20 = soundCounterexampleQ ^ 4 := by
    calc
      rawFormulaCounterexampleP1 ^ 20 =
          (rawFormulaCounterexampleP1 ^ 5) ^ 4 := by ring
      _ = soundCounterexampleQ ^ 4 := by rw [hp5]
  let v : QuadraticTriple ℂ :=
    { epsilon := rawFormulaCounterexampleEpsilon,
      t := rawFormulaCounterexampleT,
      u := radicalU (depress rawFormulaCounterexampleQuintic)
        rawFormulaCounterexampleInvariants rawFormulaCounterexampleEpsilon
        rawFormulaCounterexampleT }
  let b := fourierP2 (depress rawFormulaCounterexampleQuintic)
    rawFormulaCounterexampleInvariants
    v
    rawFormulaCounterexampleP1
  let c := fourierP3 (depress rawFormulaCounterexampleQuintic)
    rawFormulaCounterexampleInvariants
    v
    rawFormulaCounterexampleP1
  let e4 := fourierP4 (depress rawFormulaCounterexampleQuintic)
    rawFormulaCounterexampleInvariants
    v
    rawFormulaCounterexampleP1
  change b * rawFormulaCounterexampleP1 ^ 3 = soundCounterexampleB at hb
  change c * rawFormulaCounterexampleP1 ^ 2 = soundCounterexampleC at hc
  change e4 * rawFormulaCounterexampleP1 = soundCounterexampleD at hd
  change
    fourierCyclic2 rawFormulaCounterexampleP1 b c e4 *
          rawFormulaCounterexampleP1 ^ 5 = soundCounterexampleA2 ∧
      fourierCyclic3 rawFormulaCounterexampleP1 b c e4 *
          rawFormulaCounterexampleP1 ^ 10 = soundCounterexampleA3 ∧
      fourierCyclic5 rawFormulaCounterexampleP1 b c e4 *
          rawFormulaCounterexampleP1 ^ 20 = soundCounterexampleA5
  simp only [fourierCyclic2, fourierCyclic3, fourierCyclic5,
    soundCounterexampleA2, soundCounterexampleA3, soundCounterexampleA5]
  constructor
  · rw [← hp5, ← hb, ← hc, ← hd]
    ring
  · constructor
    · rw [← hp10, ← hb, ← hc, ← hd]
      rw [← hp5]
      ring
    · rw [← hp20, ← hb, ← hc, ← hd]
      rw [← hp5]
      ring

private def soundCounterexampleClearedResidual : ℂ :=
  soundCounterexampleA5 / 625 +
    soundCounterexampleA2 * soundCounterexampleA3 * soundCounterexampleQ / 25 -
    3 * soundCounterexampleA3 * soundCounterexampleQ ^ 2 / 25 +
    4 * soundCounterexampleA2 * soundCounterexampleQ ^ 3 / 5 +
    5 * soundCounterexampleQ ^ 4

set_option maxHeartbeats 4000000 in
private theorem soundCounterexampleClearedResidual_normal :
    soundCounterexampleClearedResidual =
      48031 *
        (((-8695825893560337126035903987452339404219180819507365 : ℂ) +
            80043022284012852131653745711952954113399179883890 *
              rawFormulaCounterexampleEpsilon) +
          ((4840983852104521663189413257296796193553755186248730 : ℂ) +
              (-23481997476638840295457113522001435501587280476434) *
                rawFormulaCounterexampleEpsilon) *
            rawFormulaCounterexampleT) /
        1443035980821544676189809338350645585595187200 := by
  let R : ℂ := (-1145 / 4 : ℂ) +
    (-8257 / 21796) * rawFormulaCounterexampleEpsilon
  have ht2 : rawFormulaCounterexampleT ^ 2 = R := by
    simpa [R] using rawFormulaCounterexampleT_sq
  have ht3 : rawFormulaCounterexampleT ^ 3 =
      R * rawFormulaCounterexampleT := by
    calc
      rawFormulaCounterexampleT ^ 3 =
          rawFormulaCounterexampleT ^ 2 * rawFormulaCounterexampleT := by ring
      _ = R * rawFormulaCounterexampleT := by rw [ht2]
  have ht4 : rawFormulaCounterexampleT ^ 4 = R ^ 2 := by
    calc
      rawFormulaCounterexampleT ^ 4 =
          (rawFormulaCounterexampleT ^ 2) ^ 2 := by ring
      _ = R ^ 2 := by rw [ht2]
  have ht5 : rawFormulaCounterexampleT ^ 5 =
      R ^ 2 * rawFormulaCounterexampleT := by
    calc
      rawFormulaCounterexampleT ^ 5 =
          rawFormulaCounterexampleT ^ 4 * rawFormulaCounterexampleT := by ring
      _ = R ^ 2 * rawFormulaCounterexampleT := by rw [ht4]
  have ht6 : rawFormulaCounterexampleT ^ 6 = R ^ 3 := by
    calc
      rawFormulaCounterexampleT ^ 6 =
          (rawFormulaCounterexampleT ^ 2) ^ 3 := by ring
      _ = R ^ 3 := by rw [ht2]
  have ht7 : rawFormulaCounterexampleT ^ 7 =
      R ^ 3 * rawFormulaCounterexampleT := by
    calc
      rawFormulaCounterexampleT ^ 7 =
          rawFormulaCounterexampleT ^ 6 * rawFormulaCounterexampleT := by ring
      _ = R ^ 3 * rawFormulaCounterexampleT := by rw [ht6]
  have he3 : rawFormulaCounterexampleEpsilon ^ 3 =
      27245 * rawFormulaCounterexampleEpsilon := by
    calc
      rawFormulaCounterexampleEpsilon ^ 3 =
          rawFormulaCounterexampleEpsilon ^ 2 *
            rawFormulaCounterexampleEpsilon := by ring
      _ = 27245 * rawFormulaCounterexampleEpsilon := by
        rw [rawFormulaCounterexampleEpsilon_sq]
  have he4 : rawFormulaCounterexampleEpsilon ^ 4 = (27245 : ℂ) ^ 2 := by
    calc
      rawFormulaCounterexampleEpsilon ^ 4 =
          (rawFormulaCounterexampleEpsilon ^ 2) ^ 2 := by ring
      _ = (27245 : ℂ) ^ 2 := by
        rw [rawFormulaCounterexampleEpsilon_sq]
  have he5 : rawFormulaCounterexampleEpsilon ^ 5 =
      (27245 : ℂ) ^ 2 * rawFormulaCounterexampleEpsilon := by
    calc
      rawFormulaCounterexampleEpsilon ^ 5 =
          rawFormulaCounterexampleEpsilon ^ 4 *
            rawFormulaCounterexampleEpsilon := by ring
      _ = (27245 : ℂ) ^ 2 * rawFormulaCounterexampleEpsilon := by rw [he4]
  have he6 : rawFormulaCounterexampleEpsilon ^ 6 = (27245 : ℂ) ^ 3 := by
    calc
      rawFormulaCounterexampleEpsilon ^ 6 =
          (rawFormulaCounterexampleEpsilon ^ 2) ^ 3 := by ring
      _ = (27245 : ℂ) ^ 3 := by
        rw [rawFormulaCounterexampleEpsilon_sq]
  have he7 : rawFormulaCounterexampleEpsilon ^ 7 =
      (27245 : ℂ) ^ 3 * rawFormulaCounterexampleEpsilon := by
    calc
      rawFormulaCounterexampleEpsilon ^ 7 =
          rawFormulaCounterexampleEpsilon ^ 6 *
            rawFormulaCounterexampleEpsilon := by ring
      _ = (27245 : ℂ) ^ 3 * rawFormulaCounterexampleEpsilon := by rw [he6]
  have he8 : rawFormulaCounterexampleEpsilon ^ 8 = (27245 : ℂ) ^ 4 := by
    calc
      rawFormulaCounterexampleEpsilon ^ 8 =
          (rawFormulaCounterexampleEpsilon ^ 2) ^ 4 := by ring
      _ = (27245 : ℂ) ^ 4 := by
        rw [rawFormulaCounterexampleEpsilon_sq]
  have he9 : rawFormulaCounterexampleEpsilon ^ 9 =
      (27245 : ℂ) ^ 4 * rawFormulaCounterexampleEpsilon := by
    calc
      rawFormulaCounterexampleEpsilon ^ 9 =
          rawFormulaCounterexampleEpsilon ^ 8 *
            rawFormulaCounterexampleEpsilon := by ring
      _ = (27245 : ℂ) ^ 4 * rawFormulaCounterexampleEpsilon := by rw [he8]
  have he10 : rawFormulaCounterexampleEpsilon ^ 10 = (27245 : ℂ) ^ 5 := by
    calc
      rawFormulaCounterexampleEpsilon ^ 10 =
          (rawFormulaCounterexampleEpsilon ^ 2) ^ 5 := by ring
      _ = (27245 : ℂ) ^ 5 := by
        rw [rawFormulaCounterexampleEpsilon_sq]
  simp only [soundCounterexampleClearedResidual, soundCounterexampleA2,
    soundCounterexampleA3, soundCounterexampleA5, soundCounterexampleQ,
    soundCounterexampleB, soundCounterexampleC, soundCounterexampleD]
  field_simp
  ring_nf
  simp only [ht7, ht6, ht5, ht4, ht3, ht2, R]
  ring_nf
  simp only [he10, he9, he8, he7, he6, he5, he4, he3,
    rawFormulaCounterexampleEpsilon_sq]
  ring

private theorem soundCounterexampleClearedResidual_ne_zero :
    soundCounterexampleClearedResidual ≠ 0 := by
  rw [soundCounterexampleClearedResidual_normal]
  apply div_ne_zero
  · apply mul_ne_zero
    · norm_num
    · apply quadraticTowerLinear_ne_zero
        (N := (27245 : ℂ)) (m0 := (-1145 / 4 : ℂ))
        (m1 := (-8257 / 21796 : ℂ))
        rawFormulaCounterexampleEpsilon_sq rawFormulaCounterexampleT_sq
      norm_num
  · norm_num

private theorem rawFormulaCounterexample_sum_eval_ne_zero :
    ∑ k : Fin 5,
      rawFormulaCounterexampleQuintic.eval
        (solveGeneral rawFormulaCounterexampleQuintic
          rawFormulaCounterexampleInvariants
          rawFormulaCounterexampleRadicalCertificate
          rawFormulaCounterexampleOmega k) ≠ 0 := by
  let d := rawFormulaCounterexampleRadicalCertificate
  let a := d.p1
  let b := fourierP2 (depress rawFormulaCounterexampleQuintic)
    rawFormulaCounterexampleInvariants d.chosen d.p1
  let c := fourierP3 (depress rawFormulaCounterexampleQuintic)
    rawFormulaCounterexampleInvariants d.chosen d.p1
  let e4 := fourierP4 (depress rawFormulaCounterexampleQuintic)
    rawFormulaCounterexampleInvariants d.chosen d.p1
  have hinverse :
      solveGeneral rawFormulaCounterexampleQuintic
          rawFormulaCounterexampleInvariants d rawFormulaCounterexampleOmega =
        fun k ↦ inverseFourier rawFormulaCounterexampleOmega.value a b c e4 k := by
    funext k
    simp only [solveGeneral, rawFormulaCounterexampleQuintic]
    norm_num
    exact solveDepressed_eq_inverseFourier
      (depress rawFormulaCounterexampleQuintic)
      rawFormulaCounterexampleInvariants d rawFormulaCounterexampleOmega k
  have hsum := sum_rawFormulaCounterexample_inverseFourier_eval
    rawFormulaCounterexampleOmega a b c e4
  have hsum' :
      ∑ k : Fin 5,
          rawFormulaCounterexampleQuintic.eval
            (inverseFourier rawFormulaCounterexampleOmega.value a b c e4 k) =
        fourierCyclic5 a b c e4 / 625 +
          fourierCyclic2 a b c e4 * fourierCyclic3 a b c e4 / 25 -
          3 * fourierCyclic3 a b c e4 / 25 +
          4 * fourierCyclic2 a b c e4 / 5 + 5 := by
    simpa [rawFormulaCounterexampleQuintic, GeneralQuintic.eval,
      depress, DepressedQuintic.eval] using hsum
  rw [hinverse]
  rw [hsum']
  intro hzero
  apply soundCounterexampleClearedResidual_ne_zero
  rcases soundCounterexample_cyclic_cleared with ⟨h2, h3, h5⟩
  simp only [soundCounterexampleClearedResidual]
  rw [← h2, ← h3, ← h5,
    ← soundCounterexampleQ_eq, ← rawFormulaCounterexampleP1_pow]
  have hp : d.p1 = rawFormulaCounterexampleP1 := rfl
  rw [← hp]
  field_simp at hzero ⊢
  linear_combination d.p1 ^ 20 * hzero

/-! ## Refuting the pointwise contracts -/

/-- The raw field-generic pointwise proposition is false. -/
theorem not_FormulaSound_complex : ¬ FormulaSound (K := ℂ) := by
  intro h
  have hall := h rawFormulaCounterexampleQuintic
    (by norm_num [rawFormulaCounterexampleQuintic])
    rawFormulaCounterexampleInvariants rawFormulaCounterexample_relations
    rawFormulaCounterexampleRadicalCertificate rawFormulaCounterexampleOmega
  apply rawFormulaCounterexample_sum_eval_ne_zero
  simp only [hall]
  simp

/-- Rational coefficients and a rational invariant certificate do not repair
the omitted root-origin/Fourier premise in the pointwise proposition. -/
theorem not_RationalFormulaSound : ¬ RationalFormulaSound.{0} := by
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
  have hall (k : Fin 5) := hC rawFormulaCounterexampleRadicalCertificate
    rawFormulaCounterexampleOmega k
  apply rawFormulaCounterexample_sum_eval_ne_zero
  have hpoint (k : Fin 5) :
      rawFormulaCounterexampleQuintic.eval
        (solveGeneral rawFormulaCounterexampleQuintic
          rawFormulaCounterexampleInvariants
          rawFormulaCounterexampleRadicalCertificate
          rawFormulaCounterexampleOmega k) = 0 := by
    simpa [cQ, w, solveRational, rawFormulaCounterexampleQuintic,
      rawFormulaCounterexampleInvariants, GeneralQuintic.map,
      Invariants.map] using hall k
  simp only [hpoint]
  simp

end

end LeanProofs.PolynomialFormulas.LazardQuintic
