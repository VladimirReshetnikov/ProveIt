import IPRADerivations.Analysis.Polynomials.Annihilators.GaussianAnnihilatorPolynomialEvaluation
import IPRADerivations.Analysis.RationalArithmetic.Spans.GaussianRationalRowSpan
import IPRADerivations.Analysis.Polynomials.Elimination.Superelliptic.GaussianSuperellipticSubspaceWitness

/-!
# The superelliptic bound from a nonzero null vector

Each point supplies membership in the span of the same matrix.
Membership has an existential finite coefficient vector. The
annihilator evaluates to zero at each point by exact row-span
linearity, and the weighted norm bound applies to the resulting
polynomial. The nonzero null vector is an explicit input here.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianSuperellipticSubspaceFromSpan

open_ipra
open GaussianRationalFiberGrouping (abscissa ordinate)
open GaussianRationalHorner (evaluate qzero)
open GaussianRationalPolynomialDegree (degree)
open GaussianRationalRowElimination (nullRows)
open GaussianRationalRowSpan (membership vectorDot)
open GaussianPolynomialMonicCompanion (values)
open GaussianSuperellipticSubspaceWitness (input points polynomial basisCount zeroWitness)
open GaussianWeightedMonomialBasis (evaluationVector)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def hasCoefficients (A R N v : PTm n) : Fm PTm n := .ex
  ((length (var 0) ≐ Syn.shift R) ⋏ membership (Syn.shift A) (Syn.shift R)
    (Syn.shift N) (var 0) (Syn.shift v))

def pointVector (m d L P i : PTm n) : PTm n := evaluationVector m d L (abscissa P i) (ordinate P i)

def pointMembership (f m c L P A R : PTm n) : Fm PTm n := .all
  (lt (var 0) (length (Syn.shift P)) ⟶ hasCoefficients (Syn.shift A) (Syn.shift R)
    (basisCount (Syn.shift f) (Syn.shift m) (Syn.shift c) (Syn.shift L))
    (pointVector (Syn.shift m) (degree (Syn.shift f) (Syn.shift c)) (Syn.shift L) (Syn.shift P) (var 0)))

ipra_subst hasCoefficients [Syn.subst_shift, Syn.shift_subst]

ipra_subst pointVector

ipra_subst pointMembership [Syn.subst_shift, Syn.shift_subst]

theorem membership_at (f m c L P A R i : PTm n) (h : Γ ⊢[PRAAx] pointMembership f m c L P A R)
    (hi : Γ ⊢[PRAAx] lt i (length P)) : Γ ⊢[PRAAx] hasCoefficients A R (basisCount f m c L)
      (pointVector m (degree f c) L P i) := by
  have rule : Γ ⊢[PRAAx] lt i (length P) ⟶ hasCoefficients A R (basisCount f m c L)
      (pointVector m (degree f c) L P i) := by
    simpa [pointMembership] using h.allE i
  exact .impE rule hi

theorem span_dot_zero (A R N v a : PTm n) (h : Γ ⊢[PRAAx] hasCoefficients A R N v)
    (ha : Γ ⊢[PRAAx] nullRows A R N a) : Γ ⊢[PRAAx] vectorDot N v a ≐ qzero := by
  refine .exE h ?_
  have shifted : Γ.map Fm.shift ⊢[PRAAx] nullRows (Syn.shift A) (Syn.shift R) (Syn.shift N) (Syn.shift a) := by
    simpa [Fm.shift,Syn.shift] using ha.shift
  simpa [Fm.shift,Syn.shift] using
    GaussianRationalRowSpan.membership_zero (Syn.shift A) (Syn.shift R) (Syn.shift N) (var 0)
      (Syn.shift v) (Syn.shift a) (.andE₂ Prf.hyp0) shifted.wk

theorem polynomial_zero_at (f a m c L P A R i : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hA : Γ ⊢[PRAAx] nullRows A R (basisCount f m c L) a) (hP : Γ ⊢[PRAAx] pointMembership f m c L P A R)
    (hi : Γ ⊢[PRAAx] lt i (length P)) : Γ ⊢[PRAAx]
    evaluate (values (polynomial f a m c L) m (abscissa P i)) (ordinate P i) ≐ qzero :=
  (GaussianAnnihilatorPolynomialEvaluation.evaluation_equals_dot a m (degree f c) L
    (abscissa P i) (ordinate P i) hm).eqTrans
    (span_dot_zero A R (basisCount f m c L) (pointVector m (degree f c) L P i) a
      (membership_at f m c L P A R i hP hi) hA)

theorem polynomial_zeros (f a m c L P A R : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hA : Γ ⊢[PRAAx] nullRows A R (basisCount f m c L) a)
    (hP : Γ ⊢[PRAAx] pointMembership f m c L P A R) : Γ ⊢[PRAAx] zeroWitness f a m c L P := by
  refine .allI (.impI ?_)
  have hms : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift m) := by
    simpa [Fm.shift,Syn.shift] using hm.shift
  have hAs : Γ.map Fm.shift ⊢[PRAAx] nullRows (Syn.shift A) (Syn.shift R)
      (basisCount (Syn.shift f) (Syn.shift m) (Syn.shift c) (Syn.shift L)) (Syn.shift a) := by
    simpa [Fm.shift,Syn.shift] using hA.shift
  have hPs : Γ.map Fm.shift ⊢[PRAAx] pointMembership (Syn.shift f) (Syn.shift m) (Syn.shift c)
      (Syn.shift L) (Syn.shift P) (Syn.shift A) (Syn.shift R) := by
    simpa [Fm.shift,Syn.shift] using hP.shift
  simpa [Syn.shift] using polynomial_zero_at (Syn.shift f) (Syn.shift a) (Syn.shift m) (Syn.shift c)
    (Syn.shift L) (Syn.shift P) (Syn.shift A) (Syn.shift R) (var 0) hms.wk hAs.wk hPs.wk Prf.hyp0

theorem subspace_witness_bound (f a m c L P A R : PTm n) (h : Γ ⊢[PRAAx] input f a m c L)
    (hPts : Γ ⊢[PRAAx] points f m P) (hA : Γ ⊢[PRAAx] nullRows A R (basisCount f m c L) a)
    (hP : Γ ⊢[PRAAx] pointMembership f m c L P A R) : Γ ⊢[PRAAx] le (length P) L :=
  GaussianSuperellipticSubspaceWitness.witness_bound f a m c L P h hPts
    (polynomial_zeros f a m c L P A R (.andE₁ (GaussianSuperellipticSubspaceWitness.annihilator_input f a m c L h)) hA hP)

theorem actual_point_polynomial_zeros_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (le one (var 2) ⟶ nullRows (var 6) (var 7) (basisCount (var 0) (var 2) (var 3) (var 4)) (var 1) ⟶
      pointMembership (var 0) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ⟶
      zeroWitness (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) :=
  closeUniv 8 (.impI (.impI (.impI (polynomial_zeros _ _ _ _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

theorem actual_subspace_witness_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (input (var 0) (var 1) (var 2) (var 3) (var 4) ⟶ points (var 0) (var 2) (var 5) ⟶
      nullRows (var 6) (var 7) (basisCount (var 0) (var 2) (var 3) (var 4)) (var 1) ⟶
      pointMembership (var 0) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ⟶ le (length (var 5)) (var 4)) :=
  closeUniv 8 (.impI (.impI (.impI (.impI
    (subspace_witness_bound _ _ _ _ _ _ _ _ Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0)))))

end LeanProofs.IPRA.Analysis.GaussianSuperellipticSubspaceFromSpan
