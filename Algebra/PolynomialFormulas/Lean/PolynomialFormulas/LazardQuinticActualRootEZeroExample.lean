import PolynomialFormulas.LazardQuinticRootReductionBridge
import PolynomialFormulas.LazardQuinticCoherentAlternateRadicalTower

/-!
# An actual-root example with Lazard's invariant `E = 0`

The complete coherent-alternate tower is deliberately stated without an
`invariantE != 0` assumption.  This file supplies a concrete reason why that
generality is useful.  The five Gaussian-integer roots below are distinct,
have sum zero, and satisfy

`rootUPrime roots = Complex.I * rootTPrime roots`.

Consequently `-(rootTPrime roots ^ 2 + rootUPrime roots ^ 2) = 0`, which is
exactly Lazard's displayed invariant `E` on a depressed actual-root tuple.
At the same time the epsilon product is nonzero, so the corrected alternate
projection remains available.  The quintic splits over the Gaussian
rationals; this example exercises the general root-level fallback and is not
an irreducible-`F20` example.
-/

namespace LeanProofs.PolynomialFormulas.LazardQuintic

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000

open LeanProofs.PolynomialFormulas.ComputableDummitCoefficients
open LeanProofs.PolynomialFormulas.FrobeniusDummitResolvent

private theorem depressedQuintic_eq_of_fields_eq
    {K : Type*} {a b : DepressedQuintic K}
    (hp : a.p = b.p) (hq : a.q = b.q) (hr : a.r = b.r) (hs : a.s = b.s) :
    a = b := by
  cases a
  cases b
  simp_all

private theorem invariants_eq_of_fields_eq
    {K : Type*} {a b : Invariants K}
    (h4 : a.i4 = b.i4) (h5 : a.i5 = b.i5) (h6 : a.i6 = b.i6)
    (h7 : a.i7 = b.i7) (h8 : a.i8 = b.i8) : a = b := by
  cases a
  cases b
  simp_all

/-- The Gaussian integer `a + b * I`, represented directly in `Complex`. -/
def lazardEZeroGaussianInteger (a b : Int) : Complex :=
  ⟨(a : Real), (b : Real)⟩

/-- An ordered depressed tuple of five distinct Gaussian-integer roots. -/
def lazardEZeroRoots : Fin 5 → Complex :=
  ![lazardEZeroGaussianInteger (-1) 0,
    lazardEZeroGaussianInteger 1 1,
    lazardEZeroGaussianInteger (-2) (-3),
    lazardEZeroGaussianInteger 5 (-2),
    lazardEZeroGaussianInteger (-3) 4]

@[simp] theorem lazardEZeroRoots_zero :
    lazardEZeroRoots 0 = lazardEZeroGaussianInteger (-1) 0 := rfl

@[simp] theorem lazardEZeroRoots_one :
    lazardEZeroRoots 1 = lazardEZeroGaussianInteger 1 1 := rfl

@[simp] theorem lazardEZeroRoots_two :
    lazardEZeroRoots 2 = lazardEZeroGaussianInteger (-2) (-3) := rfl

@[simp] theorem lazardEZeroRoots_three :
    lazardEZeroRoots 3 = lazardEZeroGaussianInteger 5 (-2) := rfl

@[simp] theorem lazardEZeroRoots_four :
    lazardEZeroRoots 4 = lazardEZeroGaussianInteger (-3) 4 := rfl

/-- The monic depressed quintic having `lazardEZeroRoots` as its roots. -/
def lazardEZeroQuintic : DepressedQuintic Complex :=
  ⟨lazardEZeroGaussianInteger (-5) 15,
    lazardEZeroGaussianInteger (-75) 35,
    lazardEZeroGaussianInteger 52 81,
    lazardEZeroGaussianInteger 123 61⟩

/-- The five exact metacyclic invariants of `lazardEZeroRoots`. -/
def lazardEZeroInvariants : Invariants Complex :=
  ⟨lazardEZeroGaussianInteger 194 (-118),
    lazardEZeroGaussianInteger 1195 (-3135),
    lazardEZeroGaussianInteger 2500 (-15250),
    lazardEZeroGaussianInteger 30825 (-47405),
    lazardEZeroGaussianInteger 57768 (-259316)⟩

theorem lazardEZeroRoots_injective : Function.Injective lazardEZeroRoots := by
  intro i j hij
  fin_cases i <;> fin_cases j
  all_goals simp_all [lazardEZeroGaussianInteger, Complex.ext_iff]
  all_goals norm_num at hij

/-- Exact elementary symmetric values.  In particular, the first coordinate
is zero and the tuple is already depressed. -/
theorem lazardEZero_elementaryTuple :
    elementaryTuple lazardEZeroRoots =
      ![0,
        lazardEZeroGaussianInteger (-5) 15,
        lazardEZeroGaussianInteger 75 (-35),
        lazardEZeroGaussianInteger 52 81,
        lazardEZeroGaussianInteger (-123) (-61)] := by
  funext k
  fin_cases k <;>
    apply Complex.ext <;>
      norm_num [elementaryTuple, lazardEZeroGaussianInteger]

theorem lazardEZero_sum : elementaryTuple lazardEZeroRoots 0 = 0 := by
  have h := congrFun lazardEZero_elementaryTuple (0 : Fin 5)
  simpa using h

theorem lazardEZero_depressedOfRoots :
    depressedOfRoots lazardEZeroRoots = lazardEZeroQuintic := by
  apply depressedQuintic_eq_of_fields_eq <;>
    apply Complex.ext <;>
      norm_num [depressedOfRoots, lazardEZero_elementaryTuple,
        lazardEZeroQuintic, lazardEZeroGaussianInteger,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four]

/-- Exact evaluation of all five orbit-sum invariants. -/
theorem lazardEZero_rootInvariants :
    rootInvariants lazardEZeroRoots = lazardEZeroInvariants := by
  apply invariants_eq_of_fields_eq <;>
    apply Complex.ext <;>
      norm_num [rootInvariants, thetaFormula, lazardOrbitFormula,
        lazardEZeroInvariants,
        lazardEZeroGaussianInteger, pow_succ]

theorem lazardEZero_rootTPrime :
    rootTPrime lazardEZeroRoots =
      lazardEZeroGaussianInteger (-3452) 764 := by
  apply Complex.ext <;>
    norm_num [rootTPrime, lazardEZeroGaussianInteger]

theorem lazardEZero_rootUPrime :
    rootUPrime lazardEZeroRoots =
      lazardEZeroGaussianInteger (-764) (-3452) := by
  apply Complex.ext <;>
    norm_num [rootUPrime, lazardEZeroGaussianInteger]

/-- The exact relation forcing Lazard's `E` to vanish. -/
theorem lazardEZero_rootUPrime_eq_I_mul_rootTPrime :
    rootUPrime lazardEZeroRoots =
      Complex.I * rootTPrime lazardEZeroRoots := by
  rw [lazardEZero_rootTPrime, lazardEZero_rootUPrime]
  apply Complex.ext <;>
    norm_num [lazardEZeroGaussianInteger]

theorem lazardEZero_rootTPrime_sq_add_rootUPrime_sq :
    rootTPrime lazardEZeroRoots ^ 2 +
        rootUPrime lazardEZeroRoots ^ 2 = 0 := by
  rw [lazardEZero_rootUPrime_eq_I_mul_rootTPrime, mul_pow, Complex.I_sq]
  ring

theorem lazardEZero_rootEpsilonProduct :
    rootEpsilonProduct lazardEZeroRoots =
      lazardEZeroGaussianInteger (-15625) 15625 := by
  apply Complex.ext <;>
    norm_num [rootEpsilonProduct, lazardEZeroGaussianInteger]

theorem lazardEZero_rootEpsilonProduct_ne_zero :
    rootEpsilonProduct lazardEZeroRoots ≠ 0 := by
  rw [lazardEZero_rootEpsilonProduct]
  intro h
  have him := congrArg Complex.im h
  norm_num [lazardEZeroGaussianInteger] at him

/-- The actual displayed coefficient invariant is zero, not merely the
auxiliary root expression from which it is derived. -/
theorem lazardEZero_invariantE :
    invariantE (depressedOfRoots lazardEZeroRoots)
        (rootInvariants lazardEZeroRoots) = 0 := by
  rw [root_invariantE_eq_neg_rootTPrime_sq_add_rootUPrime_sq]
  · rw [lazardEZero_rootTPrime_sq_add_rootUPrime_sq, neg_zero]
  · exact lazardEZero_sum

/-- Exact values of the other three quadratic-stage root invariants. -/
theorem lazardEZero_invariantD :
    invariantD (depressedOfRoots lazardEZeroRoots)
        (rootInvariants lazardEZeroRoots) =
      lazardEZeroGaussianInteger 0 (-488281250) := by
  rw [root_invariantD_eq_rootEpsilonProduct_sq,
    lazardEZero_rootEpsilonProduct]
  · apply Complex.ext <;>
      norm_num [lazardEZeroGaussianInteger, pow_succ]
  · exact lazardEZero_sum

theorem lazardEZero_invariantF :
    invariantF (depressedOfRoots lazardEZeroRoots)
        (rootInvariants lazardEZeroRoots) =
      lazardEZeroGaussianInteger 1227265000000 (-140355000000) := by
  rw [root_invariantF_eq_root_expression,
    lazardEZero_rootEpsilonProduct, lazardEZero_rootTPrime,
    lazardEZero_rootUPrime]
  · apply Complex.ext <;>
      norm_num [lazardEZeroGaussianInteger, pow_succ]
  · exact lazardEZero_sum

theorem lazardEZero_invariantG :
    invariantG (depressedOfRoots lazardEZeroRoots)
        (rootInvariants lazardEZeroRoots) =
      lazardEZeroGaussianInteger 70177500000 613632500000 := by
  rw [root_invariantG_eq_root_expression,
    lazardEZero_rootEpsilonProduct, lazardEZero_rootTPrime,
    lazardEZero_rootUPrime]
  · apply Complex.ext <;>
      norm_num [lazardEZeroGaussianInteger, pow_succ]
  · exact lazardEZero_sum

/-- The tuple gives an exact, multiplicity-sensitive factorization of the
displayed depressed quintic. -/
theorem lazardEZero_fiveRootRelations :
    DepressedFiveRootRelations lazardEZeroQuintic lazardEZeroRoots := by
  constructor <;>
    apply Complex.ext <;>
      norm_num [fiveESymm1, fiveESymm2, fiveESymm3, fiveESymm4,
        fiveESymm5, lazardEZeroQuintic,
        lazardEZeroGaussianInteger]

theorem lazardEZero_eval_factorization (z : Complex) :
    lazardEZeroQuintic.eval z =
      ∏ k : Fin 5, (z - lazardEZeroRoots k) :=
  lazardEZero_fiveRootRelations.eval_factorization z

/-- Every primitive fifth-root choice gives nonzero epsilon on this tuple. -/
theorem lazardEZero_rootEpsilon_ne_zero
    (omega : FifthRootOfUnity Complex) :
    rootEpsilon omega lazardEZeroRoots ≠ 0 := by
  exact mul_ne_zero (fifthRootDiscriminantFactor_ne_zero omega)
    lazardEZero_rootEpsilonProduct_ne_zero

/-- The standard projection denominator really vanishes on the example. -/
theorem lazardEZero_standardDenominator
    (omega : FifthRootOfUnity Complex) :
    rootT omega lazardEZeroRoots ^ 2 +
        rootFormulaU omega lazardEZeroRoots ^ 2 = 0 := by
  rw [rootFormulaU, neg_sq, rootT_sq_add_rootU_sq,
    lazardEZero_rootTPrime_sq_add_rootUPrime_sq, mul_zero]

/-- Equivalently, Lazard's printed projection matrix is singular on this
tuple. -/
theorem lazardEZero_standardProjectionMatrix_det
    (omega : FifthRootOfUnity Complex) :
    (standardProjectionMatrix (rootEpsilon omega lazardEZeroRoots)
      (rootT omega lazardEZeroRoots)
      (rootFormulaU omega lazardEZeroRoots)).det = 0 := by
  rw [standardProjectionMatrix_det, lazardEZero_standardDenominator, mul_zero]

/-- Nevertheless the convention-safe alternate denominator is nonzero, so
this actual-root tuple genuinely selects the corrected fallback. -/
theorem lazardEZero_coherentAlternateDenominator_ne_zero
    (omega : FifthRootOfUnity Complex) :
    coherentAlternateDenominator (rootT omega lazardEZeroRoots)
        (rootFormulaU omega lazardEZeroRoots) ≠ 0 :=
  root_coherentAlternateDenominator_ne_zero omega
    lazardEZeroRoots_injective

/-- The corrected matrix is genuinely nonsingular on the same tuple. -/
theorem lazardEZero_coherentAlternateProjectionMatrix_det_ne_zero
    (omega : FifthRootOfUnity Complex) :
    (coherentAlternateProjectionMatrix
      (rootEpsilon omega lazardEZeroRoots)
      (rootT omega lazardEZeroRoots)
      (rootFormulaU omega lazardEZeroRoots)).det ≠ 0 :=
  coherentAlternateProjectionMatrix_det_ne_zero
    (rootEpsilon omega lazardEZeroRoots)
    (rootT omega lazardEZeroRoots)
    (rootFormulaU omega lazardEZeroRoots)
    (lazardEZero_rootEpsilon_ne_zero omega)
    (lazardEZero_coherentAlternateDenominator_ne_zero omega)

/-- The root-origin constructor for the complete coherent-alternate
certificate applies to this `E = 0` tuple without any exceptional premise. -/
def lazardEZero_coherentAlternateCertificate
    (omega : FifthRootOfUnity Complex) :
    CoherentAlternateFourierCertificate
      (depressedOfRoots lazardEZeroRoots)
      (rootInvariants lazardEZeroRoots) :=
  rootCoherentAlternateFourierCertificate omega lazardEZeroRoots
    lazardEZero_sum lazardEZeroRoots_injective
    (lazardEZero_rootEpsilon_ne_zero omega)

/-- The complete alternate certificate reconstructs exactly all five roots,
up to the documented sign-branch permutation and Fourier reversal. -/
theorem lazardEZero_coherentAlternate_solve_eq_reversedRoots
    (omega : FifthRootOfUnity Complex) :
    (fun k =>
      (lazardEZero_coherentAlternateCertificate omega).solve omega k) =
      reversedRootTuple
        (rootsForBranch lazardEZeroRoots
          (correctedQuadraticBranch
            (depressedOfRoots lazardEZeroRoots)
            (rootInvariants lazardEZeroRoots)
            (rootQuadraticTriple omega lazardEZeroRoots))) := by
  exact rootCoherentAlternateFourierCertificate_solve_eq_reversedRoots
    omega lazardEZeroRoots lazardEZero_sum lazardEZeroRoots_injective
    (lazardEZero_rootEpsilon_ne_zero omega)

/-- The alternate outputs give an exact multiplicity-sensitive
factorization of the concrete `E = 0` quintic. -/
theorem lazardEZero_coherentAlternate_eval_factorization
    (omega : FifthRootOfUnity Complex) (z : Complex) :
    lazardEZeroQuintic.eval z =
      ∏ k : Fin 5,
        (z - (lazardEZero_coherentAlternateCertificate omega).solve omega k) := by
  rw [← lazardEZero_depressedOfRoots]
  exact rootCoherentAlternateFourierCertificate_eval_factorization
    omega lazardEZeroRoots lazardEZero_sum lazardEZeroRoots_injective
    (lazardEZero_rootEpsilon_ne_zero omega) z

/-- Every value returned by the corrected alternate formula is a root of
the concrete `E = 0` quintic. -/
theorem lazardEZero_coherentAlternate_sound
    (omega : FifthRootOfUnity Complex) (k : Fin 5) :
    lazardEZeroQuintic.eval
        ((lazardEZero_coherentAlternateCertificate omega).solve omega k) = 0 := by
  rw [← lazardEZero_depressedOfRoots]
  exact rootCoherentAlternateFourierCertificate_eval_root
    omega lazardEZeroRoots lazardEZero_sum lazardEZeroRoots_injective
    (lazardEZero_rootEpsilon_ne_zero omega) k

/-- Conversely, every root of the concrete quintic occurs among the five
corrected alternate outputs. -/
theorem lazardEZero_coherentAlternate_root_iff
    (omega : FifthRootOfUnity Complex) (z : Complex) :
    lazardEZeroQuintic.eval z = 0 ↔
      ∃ k : Fin 5,
        z = (lazardEZero_coherentAlternateCertificate omega).solve omega k := by
  rw [← lazardEZero_depressedOfRoots]
  exact rootCoherentAlternateFourierCertificate_eval_eq_zero_iff
    omega lazardEZeroRoots lazardEZero_sum lazardEZeroRoots_injective
    (lazardEZero_rootEpsilon_ne_zero omega) z

end

end LeanProofs.PolynomialFormulas.LazardQuintic
