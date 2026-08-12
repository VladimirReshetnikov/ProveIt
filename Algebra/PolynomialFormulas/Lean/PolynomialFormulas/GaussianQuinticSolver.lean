import PolynomialFormulas.GaussianPolynomialSolver
import PolynomialFormulas.LazardQuinticVieta
import PolynomialFormulas.LazardQuinticPrimitiveFifthRoot

/-!
# A coefficient-only Gaussian-rational quintic dispatcher

This module extends `GaussianPolynomialSolver.solve` by one nominal
coefficient.  When the quintic coefficient is zero, it delegates literally to
the already verified degree-at-most-four solver.

For a genuine quintic, this legacy dispatcher interface is certificate-driven:
it does not search for the invariant and radical certificates, and their raw
equations do not imply soundness or completeness.  A `LazardWitness` therefore
includes the four compact Fourier identities for its particular certified
invocation of `LazardQuintic.solveGeneral`.  Generic algebraic theorems derive
both pointwise root soundness and the five Vieta identities—and hence exact,
multiplicity-preserving factorization—from those Fourier identities.
The raw invariant relations and `RadicalCertificate` equations alone do not
establish either conclusion; the additional identities are the checked,
instance-specific certificates.
Separate root-origin modules construct those identities from an ordered tuple
of actual roots; their larger proof graph is tracked independently in the
paper-claim crosswalk.
The nondegenerate branch uses classical choice on the existence of such a
witness, runs the formula in the radical closure of `ℚ` in `ℂ`, and
noncomputably reifies the five resulting values as `RadicalExpression`s.

Lazard's present certificate API deliberately assumes several nonzero
denominators, so it does not cover singular solvable inputs such as `X⁵`.  If
no Lazard witness exists, the dispatcher therefore falls back to a classically
selected `CompleteRadicalSolution`, when one exists.  Only when neither package
exists does it return the separate `Result.unsupported` constructor.  Both
five-entry result constructors carry an exact factorization, proving that every
returned value is a root and every root is returned.

At `a₅ = 0`, the result, factorization, and complete root-set characterization
are those of `GaussianPolynomialSolver.solve`.  For every coefficient tuple,
`solve_allReturnedRootsSatisfy` proves pointwise soundness of every expression
the dispatcher returns.  The separate `GaussianQuinticCompleteness` module
states the full root-set and radical-solvability specifications.
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

/-- The four formula-specific identities still required after the generic
inverse-Fourier root calculation has been separated from Lazard's formulas. -/
abbrev LazardFourierRelations (c : Coefficients)
    (i : LazardQuintic.Invariants RadicalField)
    (d : LazardQuintic.RadicalCertificate
      (LazardQuintic.depress c.toLazard) i) : Prop :=
  LazardQuintic.FourierRelations (LazardQuintic.depress c.toLazard)
    d.p1
    (LazardQuintic.fourierP2
      (LazardQuintic.depress c.toLazard) i d.chosen d.p1)
    (LazardQuintic.fourierP3
      (LazardQuintic.depress c.toLazard) i d.chosen d.p1)
    (LazardQuintic.fourierP4
      (LazardQuintic.depress c.toLazard) i d.chosen d.p1)

/-- A fixed primitive fifth root of unity in `ℂ`, using Lazard's two-square-root
expression rather than treating a fifth root of `1` as one radical step. -/
noncomputable def complexPrimitiveFifthRoot : ℂ :=
  squareRadicalPrimitiveFifthRoot

theorem complexPrimitiveFifthRoot_primitive :
    IsPrimitiveRoot complexPrimitiveFifthRoot 5 := by
  exact squareRadicalPrimitiveFifthRoot_primitive

/-- Literal radical syntax for the chosen primitive fifth root, containing
exactly the two square-root constructors in the classical formula. -/
noncomputable def complexPrimitiveFifthRootExpression :
    RadicalExpression complexPrimitiveFifthRoot :=
  squareRadicalPrimitiveFifthRootExpression

/-- The fixed primitive root packaged as an explicit radical expression. -/
noncomputable def explicitPrimitiveFifthRoot : ExplicitRadical :=
  ⟨complexPrimitiveFifthRoot, complexPrimitiveFifthRootExpression⟩

/-- The fixed root of unity belongs to the radical closure of `ℚ`, as a
direct consequence of its displayed expression. -/
theorem complexPrimitiveFifthRoot_mem_solvableByRad :
    complexPrimitiveFifthRoot ∈ solvableByRad ℚ ℂ := by
  exact complexPrimitiveFifthRootExpression.eval_mem_solvableByRad

/-- The canonical primitive fifth root used by every Lazard invocation. -/
noncomputable def radicalFifthRootOfUnity :
    LazardQuintic.FifthRootOfUnity RadicalField where
  value := ⟨complexPrimitiveFifthRoot,
    complexPrimitiveFifthRoot_mem_solvableByRad⟩
  primitive := by
    rw [← IsPrimitiveRoot.coe_submonoidClass_iff]
    exact complexPrimitiveFifthRoot_primitive

/-- All non-coefficient inputs required by the existing Lazard formula.

`invariantCertificate` records the resolvent and linear-system equations
satisfied by the supplied invariant tuple;
`radicalCertificate` fixes the coherent square- and fifth-root choices; and
`fourierRelations` certifies the four cyclic coefficient identities for
the computed Fourier components.  Pointwise soundness, the five Vieta
identities, and exact factorization are derived from that compact certificate
rather than stored as fields.
In particular, the raw invariant and radical relations by themselves are not
treated as evidence that the formula output is a root.
The present library does not yet construct this witness from coefficients. -/
structure LazardWitness (c : Coefficients) where
  invariantCertificate : GaussianInvariantCertificate c
  radicalCertificate :
    LazardQuintic.RadicalCertificate
      (LazardQuintic.depress c.toLazard)
      (invariantCertificate.values.map gaussianToRadicalField)
  fourierRelations :
    LazardFourierRelations c
      (invariantCertificate.values.map gaussianToRadicalField)
      radicalCertificate

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
formula with a supplied proof-carrying witness and reifying radical-closure
membership. -/
def LazardWitness.roots {c : Coefficients} (w : LazardWitness c) :
    Fin 5 → ExplicitRadical :=
  fun k => explicitOfRadicalField
    (LazardQuintic.solveGeneral c.toLazard w.invariants
      w.radicalCertificate radicalFifthRootOfUnity k)

@[simp]
theorem LazardWitness.roots_value {c : Coefficients} (w : LazardWitness c)
    (k : Fin 5) :
    (w.roots k).value =
      (LazardQuintic.solveGeneral c.toLazard w.invariants
        w.radicalCertificate radicalFifthRootOfUnity k).1 := rfl

/-- A nonzero Gaussian-rational leading coefficient remains nonzero after
embedding into the radical closure. -/
theorem Coefficients.toLazard_a_ne_zero {c : Coefficients}
    (h5 : c.a5 ≠ 0) : c.toLazard.a ≠ 0 := by
  intro hzero
  apply h5
  apply GaussianRat.toComplex_injective
  have h := congrArg Subtype.val hzero
  simpa [Coefficients.toLazard, Coefficients.toGaussianLazard,
    LazardQuintic.GeneralQuintic.map, gaussianToRadicalField,
    toRadicalField] using h

/-- Every value reified from a proof-carrying Lazard invocation satisfies the
original Gaussian-rational quintic. -/
theorem LazardWitness.eval_root {c : Coefficients} (w : LazardWitness c)
    (h5 : c.a5 ≠ 0) (k : Fin 5) :
    c.eval (w.roots k).value = 0 := by
  have ha := c.toLazard_a_ne_zero h5
  have hGeneral := LazardQuintic.solveGeneral_root_of_fourierRelations
    c.toLazard ha w.invariants w.radicalCertificate radicalFifthRootOfUnity
      w.fourierRelations k
  have h := congrArg Subtype.val hGeneral
  simp [LazardWitness.roots, Coefficients.eval,
    GaussianPolynomialSolver.Coefficients.eval, quartic,
    Coefficients.toQuartic, Coefficients.toLazard,
    Coefficients.toGaussianLazard, LazardQuintic.GeneralQuintic.map,
    LazardQuintic.GeneralQuintic.eval, gaussianToRadicalField,
    toRadicalField] at h ⊢
  ring_nf at h ⊢
  exact h

/-- The five values reified from a Fourier-certified Lazard invocation give
an exact multiplicity-preserving factorization of the original quintic. -/
theorem LazardWitness.factorization {c : Coefficients} (w : LazardWitness c)
    (h5 : c.a5 ≠ 0) (x : ℂ) :
    c.eval x = GaussianRat.toComplex c.a5 *
      ∏ k : Fin 5, (x - (w.roots k).value) := by
  have hRadical := LazardQuintic.solveGeneral_fiveRootRelations
    c.toLazard (c.toLazard_a_ne_zero h5) w.invariants
      w.radicalCertificate radicalFifthRootOfUnity w.fourierRelations
  have hComplex := hRadical.map (solvableByRad ℚ ℂ).toSubfield.subtype
  have h := hComplex.eval_factorization x
  have hsubtype (z : RadicalField) :
      (solvableByRad ℚ ℂ).toSubfield.subtype z = z.1 := rfl
  simp [Coefficients.toLazard, Coefficients.toGaussianLazard,
    LazardQuintic.GeneralQuintic.map, LazardQuintic.GeneralQuintic.eval,
    Coefficients.eval, Coefficients.toQuartic,
    GaussianPolynomialSolver.Coefficients.eval, quartic,
    LazardWitness.roots, LazardWitness.invariants,
    gaussianToRadicalField, toRadicalField, hsubtype] at h ⊢
  ring_nf at h ⊢
  exact h

/-- A complete explicit radical factorization of a genuine quintic.

This package is the fallback for solvable inputs outside the nonzero-
denominator scope of the current Lazard certificate, for example repeated or
singular quintics. -/
structure CompleteRadicalSolution (c : Coefficients) where
  leading_ne_zero : c.a5 ≠ 0
  roots : Fin 5 → ExplicitRadical
  factorization : ∀ x : ℂ,
    c.eval x = GaussianRat.toComplex c.a5 *
      ∏ k : Fin 5, (x - (roots k).value)

/-- Package a Fourier-certified Lazard invocation as a complete explicit
radical solution. -/
def LazardWitness.completeRadicalSolution {c : Coefficients}
    (w : LazardWitness c) (h5 : c.a5 ≠ 0) : CompleteRadicalSolution c where
  leading_ne_zero := h5
  roots := w.roots
  factorization := w.factorization h5

/-- Each entry of a complete radical factorization is a root. -/
theorem CompleteRadicalSolution.eval_root {c : Coefficients}
    (solution : CompleteRadicalSolution c) (k : Fin 5) :
    c.eval (solution.roots k).value = 0 := by
  rw [solution.factorization]
  apply mul_eq_zero_of_right
  exact Finset.prod_eq_zero (Finset.mem_univ k) (sub_self _)

/-! ## A proof-carrying result type -/

/-- Output of the quintic dispatcher.

The constructors deliberately distinguish the verified lower-degree result,
Fourier-certified Lazard outputs, a complete explicit fallback, and the absence
of either degree-five package.  Both five-entry constructors store an exact
factorization, so even a `Result` built independently of `solve` cannot contain
an incomplete or unsound returned vector. -/
inductive Result (c : Coefficients) where
  | lowerDegree (leadingZero : c.a5 = 0)
  | lazardCandidates (solution : CompleteRadicalSolution c)
  | completeRadical (solution : CompleteRadicalSolution c)
  | unsupported

namespace Result

/-- Membership in the returned collection. -/
def Contains {c : Coefficients} : Result c → ℂ → Prop
  | .lowerDegree _, x => (GaussianPolynomialSolver.solve c.toQuartic).Contains x
  | .lazardCandidates solution, x => ∃ k, (solution.roots k).value = x
  | .completeRadical solution, x => ∃ k, (solution.roots k).value = x
  | .unsupported, _ => False

/-- Number of returned expressions; `none` retains the lower-degree zero
polynomial's “every complex value” result. -/
def rootCount {c : Coefficients} : Result c → Option ℕ
  | .lowerDegree _ => (GaussianPolynomialSolver.solve c.toQuartic).rootCount
  | .lazardCandidates _ => some 5
  | .completeRadical _ => some 5
  | .unsupported => some 0

/-- Product represented by a result and its input coefficients.  Every
constructor that returns a finite vector has an exact factorization proof. -/
def productValue {c : Coefficients} : Result c → ℂ → ℂ
  | .lowerDegree _, x =>
      (GaussianPolynomialSolver.solve c.toQuartic).productValue x
  | .lazardCandidates solution, x =>
      GaussianRat.toComplex c.a5 *
        ∏ k : Fin 5, (x - (solution.roots k).value)
  | .completeRadical solution, x =>
      GaussianRat.toComplex c.a5 *
        ∏ k : Fin 5, (x - (solution.roots k).value)
  | .unsupported, _ => 0

/-- The fallback constructor retains its exact factorization proof. -/
theorem productValue_completeRadical {c : Coefficients}
    (solution : CompleteRadicalSolution c) (x : ℂ) :
    (Result.completeRadical solution).productValue x = c.eval x := by
  exact (solution.factorization x).symm

/-- The Lazard constructor retains its exact factorization proof. -/
theorem productValue_lazardCandidates {c : Coefficients}
    (solution : CompleteRadicalSolution c) (x : ℂ) :
    (Result.lazardCandidates solution).productValue x = c.eval x := by
  exact (solution.factorization x).symm

/-- Pointwise soundness of all expressions represented by a result. -/
def AllReturnedRootsSatisfy {c : Coefficients} (result : Result c) : Prop :=
  ∀ x : ℂ, result.Contains x → c.eval x = 0

/-- Every `Result` is sound by construction.  This includes the delegated
degree-at-most-four result and both five-entry constructors. -/
theorem allReturnedRootsSatisfy {c : Coefficients} (result : Result c) :
    result.AllReturnedRootsSatisfy := by
  cases result with
  | lowerDegree h5 =>
      intro x hx
      rw [c.eval_eq_toQuartic_eval_of_a5_eq_zero h5]
      exact
        (GaussianPolynomialSolver.eval_eq_zero_iff_contains c.toQuartic x).mpr hx
  | lazardCandidates solution =>
      rintro x ⟨k, rfl⟩
      exact solution.eval_root k
  | completeRadical solution =>
      rintro x ⟨k, rfl⟩
      exact solution.eval_root k
  | unsupported =>
      intro _ hx
      exact False.elim hx

/-- Any value contained in a result satisfies the input polynomial. -/
theorem contains_implies_eval_eq_zero {c : Coefficients} (result : Result c)
    {x : ℂ} (hx : result.Contains x) :
    c.eval x = 0 :=
  result.allReturnedRootsSatisfy x hx

end Result

/-- A genuine-quintic backend has access to the proof that `a₅` is nonzero. -/
abbrev Backend := (c : Coefficients) → c.a5 ≠ 0 → Result c

/-- Prefer Lazard's five certified outputs.  If its nondegeneracy package is
unavailable, retain a complete explicit radical solution for exceptional
solvable inputs.  Failure is represented separately by `unsupported`. -/
def lazardBackend : Backend := by
  intro c h5
  classical
  exact if hLazard : Nonempty (LazardWitness c) then
    let w := Classical.choice hLazard
    .lazardCandidates (w.completeRadicalSolution h5)
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
expressions, each carrying a proof that its value is a root. -/
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

/-- Every expression returned by the coefficient-only solver satisfies the
input polynomial, in both the genuine-quintic and lower-degree branches. -/
theorem solve_allReturnedRootsSatisfy (c : Coefficients) :
    (solve c).AllReturnedRootsSatisfy :=
  Result.allReturnedRootsSatisfy (solve c)

/-- Pointwise form of `solve_allReturnedRootsSatisfy`. -/
theorem solve_contains_implies_eval_eq_zero (c : Coefficients) (x : ℂ)
    (hx : (solve c).Contains x) :
    c.eval x = 0 :=
  (solve_allReturnedRootsSatisfy c) x hx

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
