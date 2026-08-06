import PolynomialFormulas.GaussianPolynomialSolver
import PolynomialFormulas.LazardQuintic

/-!
# A coefficient-only Gaussian-rational quintic dispatcher

This module extends `GaussianPolynomialSolver.solve` by one nominal
coefficient.  When the quintic coefficient is zero, it delegates literally to
the already verified degree-at-most-four solver.

For a genuine quintic, the current Lazard development is certificate-driven:
it does not search for the invariant and radical certificates, and its
soundness theorem is still a stated future target.  The nondegenerate branch
therefore uses classical choice on the existence of a `LazardWitness`.  If one
exists, it runs `LazardQuintic.solveGeneral` in the radical closure of `ℚ` in
`ℂ` and noncomputably reifies the five resulting values as
`RadicalExpression`s.

Lazard's present certificate API deliberately assumes several nonzero
denominators, so it does not cover singular solvable inputs such as `X⁵`.  If
no Lazard witness exists, the dispatcher therefore falls back to a classically
selected `CompleteRadicalSolution`, when one exists.  Only when neither package
exists does it return the separate `Result.unsupported` constructor.  No
correctness claim is made here for candidates from the genuine Lazard branch.

The proved public results in this file are exactly the requested degenerate
ones: at `a₅ = 0`, the result, factorization, and root-set characterization are
those of `GaussianPolynomialSolver.solve`.
-/

namespace LeanProofs.PolynomialFormulas

noncomputable section

namespace GaussianQuinticSolver

/-- Coefficients of `a₅x⁵ + a₄x⁴ + a₃x³ + a₂x² + a₁x + a₀`.

The type also admits the all-zero tuple; the lower-degree solver already has a
precise `identicallyZero` result for that harmless extra input. -/
structure Coefficients where
  a5 : GaussianRat
  a4 : GaussianRat
  a3 : GaussianRat
  a2 : GaussianRat
  a1 : GaussianRat
  a0 : GaussianRat
deriving DecidableEq

/-- Drop the nominal quintic coefficient. -/
def Coefficients.toQuartic (c : Coefficients) :
    GaussianPolynomialSolver.Coefficients :=
  ⟨c.a4, c.a3, c.a2, c.a1, c.a0⟩

/-- Evaluate a degree-at-most-five Gaussian-rational coefficient tuple in
`ℂ`. -/
def Coefficients.eval (c : Coefficients) (x : ℂ) : ℂ :=
  GaussianRat.toComplex c.a5 * x ^ 5 + c.toQuartic.eval x

@[simp]
theorem Coefficients.eval_eq_toQuartic_eval_of_a5_eq_zero
    (c : Coefficients) (h5 : c.a5 = 0) (x : ℂ) :
    c.eval x = c.toQuartic.eval x := by
  simp [Coefficients.eval, h5]

/-! ## Expression-valued adapter for the certificate-driven Lazard formula -/

/-- The field of complex values obtainable from rational constants by field
operations and radicals. -/
abbrev RadicalField := ↥(solvableByRad ℚ ℂ)

noncomputable local instance : DecidableEq RadicalField := Classical.decEq _

/-- Embed a Gaussian rational into the radical closure.  The membership proof
comes from its concrete expression `a + b√(-1)`. -/
def toRadicalField (z : GaussianRat) : RadicalField :=
  ⟨GaussianRat.toComplex z, by
    simpa using (ExplicitRadical.ofGaussian z).expression.eval_mem_solvableByRad⟩

/-- The Gaussian-rational embedding into the radical closure. -/
def gaussianToRadicalField : GaussianRat →+* RadicalField where
  toFun := toRadicalField
  map_zero' := by
    apply Subtype.ext
    simp [toRadicalField]
  map_one' := by
    apply Subtype.ext
    simp [toRadicalField]
  map_add' x y := by
    apply Subtype.ext
    simp [toRadicalField]
  map_mul' x y := by
    apply Subtype.ext
    simp [toRadicalField]

/-- The six coefficients as a general quintic over their coefficient field. -/
def Coefficients.toGaussianLazard (c : Coefficients) :
    LazardQuintic.GeneralQuintic GaussianRat :=
  ⟨c.a5, c.a4, c.a3, c.a2, c.a1, c.a0⟩

/-- The same six coefficients embedded into the radical closure. -/
def Coefficients.toLazard (c : Coefficients) :
    LazardQuintic.GeneralQuintic RadicalField :=
  c.toGaussianLazard.map gaussianToRadicalField

/-- Lazard's invariant tuple is first certified in the Gaussian-rational
coefficient field, before any radical extension is used. -/
structure GaussianInvariantCertificate (c : Coefficients) where
  values : LazardQuintic.Invariants GaussianRat
  relations : LazardQuintic.InvariantRelations
    (LazardQuintic.depress c.toGaussianLazard) values

/-- All non-coefficient inputs required by the existing Lazard formula.

`invariantCertificate` records that the invariant tuple is the intended one;
`radicalCertificate` fixes the coherent square- and fifth-root choices; and
`omega` fixes the primitive fifth root of unity shared by all five outputs.
The present library does not yet construct this witness from coefficients. -/
structure LazardWitness (c : Coefficients) where
  invariantCertificate : GaussianInvariantCertificate c
  radicalCertificate :
    LazardQuintic.RadicalCertificate
      (LazardQuintic.depress c.toLazard)
      (invariantCertificate.values.map gaussianToRadicalField)
  omega : LazardQuintic.FifthRootOfUnity RadicalField

/-- The certified coefficient-field invariants after embedding into the
radical closure. -/
def LazardWitness.invariants {c : Coefficients} (w : LazardWitness c) :
    LazardQuintic.Invariants RadicalField :=
  w.invariantCertificate.values.map gaussianToRadicalField

/-- The invariant relations remain valid after embedding into the radical
closure. -/
theorem LazardWitness.invariantRelations {c : Coefficients}
    (w : LazardWitness c) :
    LazardQuintic.InvariantRelations
      (LazardQuintic.depress c.toLazard) w.invariants := by
  rw [Coefficients.toLazard, LazardQuintic.depress_map]
  exact w.invariantCertificate.relations.map gaussianToRadicalField

/-- Noncomputably choose typed radical syntax witnessing membership in the
radical closure.  The value is exact, but the chosen syntax need not mirror
the surface shape of Lazard's displayed formula. -/
def explicitOfRadicalField (z : RadicalField) : ExplicitRadical :=
  ⟨z.1, Classical.choice
    (RadicalExpression.nonempty_iff_mem_solvableByRad.mpr z.2)⟩

@[simp]
theorem explicitOfRadicalField_value (z : RadicalField) :
    (explicitOfRadicalField z).value = z.1 := rfl

/-- The five explicit radical values obtained by running Lazard's existing
formula with a supplied witness and reifying radical-closure membership.  This
is not a correctness theorem for the formula. -/
def LazardWitness.roots {c : Coefficients} (w : LazardWitness c) :
    Fin 5 → ExplicitRadical :=
  fun k => explicitOfRadicalField
    (LazardQuintic.solveGeneral c.toLazard w.invariants
      w.radicalCertificate w.omega k)

@[simp]
theorem LazardWitness.roots_value {c : Coefficients} (w : LazardWitness c)
    (k : Fin 5) :
    (w.roots k).value =
      (LazardQuintic.solveGeneral c.toLazard w.invariants
        w.radicalCertificate w.omega k).1 := rfl

/-- A complete explicit radical factorization of a genuine quintic.

This package is the fallback for solvable inputs outside the nonzero-
denominator scope of the current Lazard certificate, for example repeated or
singular quintics. -/
structure CompleteRadicalSolution (c : Coefficients) where
  roots : Fin 5 → ExplicitRadical
  factorization : ∀ x : ℂ,
    c.eval x = GaussianRat.toComplex c.a5 *
      ∏ k : Fin 5, (x - (roots k).value)

/-! ## A result type that keeps proved roots separate from candidates -/

/-- Output of the quintic dispatcher.

The constructors deliberately distinguish the verified lower-degree result,
the currently unverified Lazard candidates, a complete explicit fallback, and
the absence of either degree-five package. -/
inductive Result (c : Coefficients) where
  | lowerDegree (leadingZero : c.a5 = 0)
  | lazardCandidates (roots : Fin 5 → ExplicitRadical)
  | completeRadical (solution : CompleteRadicalSolution c)
  | unsupported

namespace Result

/-- Membership in the returned collection.  For `lazardCandidates` this is
only candidate membership until Lazard soundness is proved. -/
def Contains {c : Coefficients} : Result c → ℂ → Prop
  | .lowerDegree _, x => (GaussianPolynomialSolver.solve c.toQuartic).Contains x
  | .lazardCandidates roots, x => ∃ k, (roots k).value = x
  | .completeRadical solution, x => ∃ k, (solution.roots k).value = x
  | .unsupported, _ => False

/-- Number of returned expressions; `none` retains the lower-degree zero
polynomial's “every complex value” result. -/
def rootCount {c : Coefficients} : Result c → Option ℕ
  | .lowerDegree _ => (GaussianPolynomialSolver.solve c.toQuartic).rootCount
  | .lazardCandidates _ => some 5
  | .completeRadical _ => some 5
  | .unsupported => some 0

/-- Product represented by a result and its input coefficients.  The
lower-degree and `completeRadical` cases have proofs; for `lazardCandidates`
this is only the formal candidate product until Lazard soundness is proved. -/
def productValue {c : Coefficients} : Result c → ℂ → ℂ
  | .lowerDegree _, x =>
      (GaussianPolynomialSolver.solve c.toQuartic).productValue x
  | .lazardCandidates roots, x =>
      GaussianRat.toComplex c.a5 * ∏ k : Fin 5, (x - (roots k).value)
  | .completeRadical solution, x =>
      GaussianRat.toComplex c.a5 *
        ∏ k : Fin 5, (x - (solution.roots k).value)
  | .unsupported, _ => 0

/-- The fallback constructor retains its exact factorization proof. -/
theorem productValue_completeRadical {c : Coefficients}
    (solution : CompleteRadicalSolution c) (x : ℂ) :
    (Result.completeRadical solution).productValue x = c.eval x := by
  exact (solution.factorization x).symm

end Result

/-- A genuine-quintic backend has access to the proof that `a₅` is nonzero. -/
abbrev Backend := (c : Coefficients) → c.a5 ≠ 0 → Result c

/-- Prefer Lazard's five candidates.  If its nondegeneracy package is
unavailable, retain a complete explicit radical solution for exceptional
solvable inputs.  Failure is represented separately by `unsupported`. -/
def lazardBackend : Backend := by
  intro c _h5
  classical
  exact if hLazard : Nonempty (LazardWitness c) then
    .lazardCandidates (Classical.choice hLazard).roots
  else if hSolution : Nonempty (CompleteRadicalSolution c) then
    .completeRadical (Classical.choice hSolution)
  else
    .unsupported

/-! ## Total dispatcher and verified lower-degree behavior -/

/-- Compose any genuine-quintic backend with the verified solver through
degree four. -/
def solveWith (backend : Backend) (c : Coefficients) :
    Result c :=
  if h5 : c.a5 = 0 then
    .lowerDegree h5
  else
    backend c h5

/-- The coefficient-only quintic dispatcher. -/
def solve (c : Coefficients) : Result c :=
  solveWith lazardBackend c

@[simp]
theorem solveWith_of_a5_eq_zero (backend : Backend) (c : Coefficients)
    (h5 : c.a5 = 0) :
    solveWith backend c = .lowerDegree h5 := by
  simp [solveWith, h5]

@[simp]
theorem solveWith_of_a5_ne_zero (backend : Backend) (c : Coefficients)
    (h5 : c.a5 ≠ 0) :
    solveWith backend c = backend c h5 := by
  simp [solveWith, h5]

@[simp]
theorem solve_of_a5_eq_zero (c : Coefficients) (h5 : c.a5 = 0) :
    solve c = .lowerDegree h5 := by
  simp [solve, h5]

@[simp]
theorem solve_of_a5_ne_zero (c : Coefficients) (h5 : c.a5 ≠ 0) :
    solve c = lazardBackend c h5 := by
  simp [solve, h5]

/-- A genuine quintic with an available Lazard witness returns five radical
expressions.  This only describes the construction; it does not assert that
the five values are roots. -/
theorem solve_rootCount_of_a5_ne_zero_of_lazardWitness (c : Coefficients)
    (h5 : c.a5 ≠ 0) (h : Nonempty (LazardWitness c)) :
    (solve c).rootCount = some 5 := by
  classical
  simp [solve, solveWith, h5, lazardBackend, h, Result.rootCount]

/-- Every supplied complete radical factorization makes the genuine-quintic
branch return five expressions, including when Lazard's denominator
conditions fail. -/
theorem solve_rootCount_of_a5_ne_zero_of_completeRadicalSolution
    (c : Coefficients) (h5 : c.a5 ≠ 0)
    (h : Nonempty (CompleteRadicalSolution c)) :
    (solve c).rootCount = some 5 := by
  classical
  by_cases hLazard : Nonempty (LazardWitness c)
  · simp [solve, solveWith, h5, lazardBackend, hLazard, Result.rootCount]
  · simp [solve, solveWith, h5, lazardBackend, hLazard, h,
      Result.rootCount]

/-- Only the absence of both a Lazard package and a complete explicit radical
factorization produces the permitted `unsupported` result. -/
theorem solve_rootCount_of_a5_ne_zero_of_no_candidate (c : Coefficients)
    (h5 : c.a5 ≠ 0) (hLazard : ¬ Nonempty (LazardWitness c))
    (hSolution : ¬ Nonempty (CompleteRadicalSolution c)) :
    (solve c).rootCount = some 0 := by
  classical
  simp [solve, solveWith, h5, lazardBackend, hLazard, hSolution,
    Result.rootCount]

/-- At zero quintic coefficient, the combined solver inherits the exact
multiplicity-preserving factorization from the lower-degree solver. -/
theorem solve_factorization_of_a5_eq_zero (c : Coefficients)
    (h5 : c.a5 = 0) (x : ℂ) :
    c.eval x = (solve c).productValue x := by
  rw [c.eval_eq_toQuartic_eval_of_a5_eq_zero h5 x,
    solve_of_a5_eq_zero c h5]
  simpa [Result.productValue] using
    GaussianPolynomialSolver.solve_factorization c.toQuartic x

/-- At zero quintic coefficient, the returned expressions contain exactly
all complex roots. -/
theorem eval_eq_zero_iff_contains_of_a5_eq_zero (c : Coefficients)
    (h5 : c.a5 = 0) (x : ℂ) :
    c.eval x = 0 ↔ (solve c).Contains x := by
  rw [c.eval_eq_toQuartic_eval_of_a5_eq_zero h5 x,
    solve_of_a5_eq_zero c h5]
  simpa [Result.Contains] using
    GaussianPolynomialSolver.eval_eq_zero_iff_contains c.toQuartic x

end GaussianQuinticSolver

end

end LeanProofs.PolynomialFormulas
