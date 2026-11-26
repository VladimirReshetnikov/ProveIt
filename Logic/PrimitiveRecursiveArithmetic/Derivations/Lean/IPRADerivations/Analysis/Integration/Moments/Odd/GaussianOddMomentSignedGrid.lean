import IPRADerivations.Analysis.Integration.Moments.Odd.GaussianOddMomentIntegrand
import IPRADerivations.Analysis.Integration.Moments.Even.GaussianEvenMomentSymmetricGrid
import IPRADerivations.Analysis.Integration.CompactGrids.GaussianCompactClientIndependence

/-!
# Signed odd Gaussian quadratures at the computed decay clocks

The positive and negative clients are the original signed odd rows,
with each decay queried at the precision required by its rational
monomial factor. The finite signed sum cancels exactly. The actual
positive quadrature matches the corresponding original quadratic cut.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianOddMomentSignedGrid

open_ipra
open GaussianOddMomentIntegrand (argument clock degree)
open GaussianOddSymmetricQuadrature (fixedData positiveF negativeF)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (qadd qzero)
open GaussianRationalMetric (distanceBounded qnegative)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr)
open GaussianRationalFiniteSum (sum)
open GaussianCompactRiemannName (evaluatorName nameData inside grid sampleBody sampleData quadrature)
open GaussianNameEquivalence (crossEquivalent)
open GaussianCoefficientNameBounds (unit)

variable {n : ℕ} {Γ : List (Fm PTm n)}

abbrev source := @GaussianEvenMomentSymmetricGrid.source

def originalF (negative : Bool) : PR 3 := if negative then negativeF else positiveF
def rowClock (p t x : PTm n) : PTm n := clock p (fstT x) (fstT t) (sndT t) (fstT (sndT x)) (sndT (sndT x))
def evaluatorTerm (negative : Bool) (p t x : PTm n) : PTm n := ap3 (originalF negative) (rowClock p t x) t x
def evaluatorF (negative : Bool) : PR 3 := PTm.toPR (evaluatorTerm negative (var 0) (var 1) (var 2))
def symmetricGrid (p M a C E x : PTm n) : PTm n :=
  qadd (quadrature (evaluatorF false) p M a C E x) (quadrature (evaluatorF true) p M a C E x)

ipra_subst evaluatorTerm [rowClock]
ipra_subst symmetricGrid

theorem evaluator_at (side : Bool) (p t x : PTm n) : Γ ⊢[PRAAx]
    ap3 (evaluatorF side) p t x ≐ evaluatorTerm side p t x := by
  simpa only [evaluatorF,ap3,subst_evaluatorTerm,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]
    using toPR_eq (Γ := Γ) (evaluatorTerm side (var 0) (var 1) (var 2) : PTm 3) ![p,t,x]

theorem reflected_row (p t x : PTm n) : Γ ⊢[PRAAx]
    ap3 (evaluatorF true) p t x ≐ qnegative (ap3 (evaluatorF false) p t x) :=
  (evaluator_at true p t x).eqTrans
    ((GaussianOddSymmetricQuadrature.reflected_row (rowClock p t x) t x).eqTrans
      (GaussianInverseBinomialRows.negative_congr (evaluator_at false p t x).eqSymm))

theorem reflected_cell (i p M a C E x : PTm n) : Γ ⊢[PRAAx]
    inst2 (sampleBody (evaluatorF true)) i (sampleData p M a C E x) ≐
      qnegative (inst2 (sampleBody (evaluatorF false)) i (sampleData p M a C E x)) :=
  (GaussianCompactRiemannName.sample_body_at _ i p M a C E x).eqTrans
    ((reflected_row p (grid i M a C E) x).eqTrans (GaussianInverseBinomialRows.negative_congr
      (GaussianCompactRiemannName.sample_body_at _ i p M a C E x).eqSymm))

theorem reflected_quadrature (p M a C E x : PTm n) : Γ ⊢[PRAAx]
    quadrature (evaluatorF true) p M a C E x ≐ qnegative (quadrature (evaluatorF false) p M a C E x) := by
  have cells : Γ ⊢[PRAAx] GaussianRationalFiniteSum.termsEqual (sampleBody (evaluatorF true))
      (GaussianRationalMatrixFiniteSums.negativeBody (sampleBody (evaluatorF false))) M
      (sampleData p M a C E x) (sampleData p M a C E x) := by
    refine .allI (.impI ?_)
    simpa only [GaussianRationalFiniteSum.termsEqual,GaussianRationalMatrixFiniteSums.negative_body_at,
      GaussianCompactRiemannName.subst_sampleData,Syn.shift] using
      reflected_cell (Γ := _ :: Γ.map Fm.shift) (var 0) (Syn.shift p) (Syn.shift M) (Syn.shift a) (Syn.shift C) (Syn.shift E) (Syn.shift x)
  have values := (GaussianRationalFiniteSum.sum_congr_bounded _ _ _ _ _ cells).eqTrans
    (GaussianRationalMatrixFiniteSums.sum_negative (sampleBody (evaluatorF false)) M (sampleData p M a C E x))
  exact (qmul_congr (.eqRefl _) values).eqTrans (GaussianMomentReflection.negative_right_product _ _)

theorem symmetric_grid_zero (p M a C E x : PTm n) : Γ ⊢[PRAAx] symmetricGrid p M a C E x ≐ qzero :=
  (qadd_congr (.eqRefl _) (reflected_quadrature p M a C E x)).eqTrans (GaussianCoefficientNormOrder.qsub_self _)

theorem literal_positive_at (p t N c d : PTm n) : Γ ⊢[PRAAx]
    ap3 (evaluatorF false) p t (fixedData N c d) ≐
      GaussianMomentReflection.row (clock p N (fstT t) (sndT t) c d) (degree N)
        (fraction (fstT t) (sndT t)) (fstT t) (sndT t) c d := by
  let x := fixedData N c d
  have l : Γ ⊢[PRAAx] fstT x ≐ N := fst_pair N (pairT c d)
  have r : Γ ⊢[PRAAx] sndT x ≐ pairT c d := snd_pair N (pairT c d)
  let tmpl : PTm 6 := GaussianMomentReflection.row
    (clock (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
    (degree (var 1)) (fraction (var 2) (var 3)) (var 2) (var 3) (var 4) (var 5)
  let L : Fin 6 → PTm n := ![p,fstT x,fstT t,sndT t,fstT (sndT x),sndT (sndT x)]
  let R : Fin 6 → PTm n := ![p,N,fstT t,sndT t,c,d]
  have e : Γ ⊢[PRAAx] Syn.subst L tmpl ≐ Syn.subst R tmpl :=
    Prf.eqCongr tmpl (σ := L) (σ' := R) (fun i => by
      fin_cases i
      · exact .eqRefl p
      · exact l
      · exact .eqRefl (fstT t)
      · exact .eqRefl (sndT t)
      · exact (congrFst r).eqTrans (fst_pair c d)
      · exact (congrSnd r).eqTrans (snd_pair c d))
  exact (evaluator_at false p t x).eqTrans ((GaussianOddSymmetricQuadrature.positive_at (rowClock p t x) t x).eqTrans
    (by simpa [tmpl,L,R,degree,rowClock,GaussianOddSymmetricQuadrature.positiveTerm] using e))

theorem wrapped_observations (p q t N c d E T : PTm n)
    (h : Γ ⊢[PRAAx] GaussianOddMomentIntegrand.source (fstT t) (sndT t) E T c d) : Γ ⊢[PRAAx]
    distanceBounded
      (ap2 (evaluatorName GaussianEulerQuadraticKernelCompactName.evaluatorF) p
        (nameData t (GaussianEulerPositiveScalingIntegrand.fixedData (argument N) one c d)))
      (ap2 (evaluatorName (evaluatorF false)) q (nameData t (fixedData N c d))) (unit p+unit q) (unit p*unit q) := by
  have left := (GaussianCompactRiemannName.evaluator_at (Γ := Γ) GaussianEulerQuadraticKernelCompactName.evaluatorF p t _).eqTrans
    (GaussianEulerQuadraticKernelCompactName.evaluator_at p t (argument N) one c d)
  have right := (GaussianCompactRiemannName.evaluator_at (Γ := Γ) (evaluatorF false) q t _).eqTrans
    ((literal_positive_at q t N c d).eqTrans (GaussianOddMomentIntegrand.sample_at q N (fstT t) (sndT t) c d).eqSymm)
  exact distance_congr left.eqSymm right.eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianOddMomentIntegrand.original_observations p q N (fstT t) (sndT t) E T c d h)

theorem local_agreement (N a C E T c d : PTm n) (h : Γ ⊢[PRAAx] source a C E T c d) : Γ ⊢[PRAAx]
    GaussianCompactClientIndependence.localAgreement GaussianEulerQuadraticKernelCompactName.evaluatorF
      (evaluatorF false) a C E (GaussianEulerPositiveScalingIntegrand.fixedData (argument N) one c d) (fixedData N c d) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift a) (Syn.shift C) (Syn.shift E) (Syn.shift T) (Syn.shift c) (Syn.shift d) :=
    by simpa only [Fm.shift,GaussianEvenMomentSymmetricGrid.subst_source,Syn.shift] using h.shift
  refine .allI (.impI (.allI (.allI ?_)))
  let Δ := (inside (Syn.shift a) (Syn.shift C) (Syn.shift E) (var 0) :: Γ.map Fm.shift).map Fm.shift
  have dom : (inside (Syn.shift a) (Syn.shift C) (Syn.shift E) (var 0) :: Γ.map Fm.shift) ⊢[PRAAx]
      GaussianOddMomentIntegrand.source (fstT (var 0)) (sndT (var 0)) (Syn.shift E) (Syn.shift T) (Syn.shift c) (Syn.shift d) :=
    .andI (.andI hs.andE₁.andE₁.wk (GaussianEulerCompactAdditivity.domain_of_inside (var 0) (Syn.shift a)
      (Syn.shift C) (Syn.shift E) (Syn.shift T) hs.andE₁.andE₂.andE₁.wk hs.andE₁.andE₁.wk
      hs.andE₁.andE₂.andE₂.wk Prf.hyp0)) hs.andE₂.wk
  have moved : Δ.map Fm.shift ⊢[PRAAx] GaussianOddMomentIntegrand.source (fstT (var 2)) (sndT (var 2))
      (Syn.shift (Syn.shift (Syn.shift E))) (Syn.shift (Syn.shift (Syn.shift T)))
      (Syn.shift (Syn.shift (Syn.shift c))) (Syn.shift (Syn.shift (Syn.shift d))) := by
    simpa [Δ,Fm.shift,Syn.shift] using dom.shift.shift
  simpa [Δ,GaussianCompactClientIndependence.localAgreement,GaussianCompactClientIndependence.agreementBody,
    crossEquivalent,Syn.shift,two,List.map_map] using
    wrapped_observations (Γ := Δ.map Fm.shift) (var 1) (var 0) (var 2) (Syn.shift (Syn.shift (Syn.shift N)))
      (Syn.shift (Syn.shift (Syn.shift c))) (Syn.shift (Syn.shift (Syn.shift d)))
      (Syn.shift (Syn.shift (Syn.shift E))) (Syn.shift (Syn.shift (Syn.shift T))) moved

theorem original_grid_distance (p q M a C E T N c d : PTm n) (h : Γ ⊢[PRAAx] source a C E T c d)
    (hM : Γ ⊢[PRAAx] le one M) : Γ ⊢[PRAAx]
    distanceBounded
      (quadrature GaussianEulerQuadraticKernelCompactName.evaluatorF p M a C E (GaussianEulerPositiveScalingIntegrand.fixedData (argument N) one c d))
      (quadrature (evaluatorF false) q M a C E (fixedData N c d)) (C*(unit p+unit q)) (E*(unit p*unit q)) :=
  GaussianCompactClientIndependence.quadrature_distance _ _ p q M a C E _ _
    (local_agreement N a C E T c d h) h.andE₁.andE₂.andE₁ h.andE₁.andE₁ hM

theorem actual_signed_odd_Gaussian_grid_zero_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (symmetricGrid (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ≐ qzero) :=
  closeUniv 6 (symmetric_grid_zero _ _ _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianOddMomentSignedGrid
