import IPRADerivations.Analysis.RationalArithmetic.Norms.GaussianNormFiberDivisibility
import IPRADerivations.Analysis.RationalArithmetic.Norms.GaussianNormGroupFactorProduct
import IPRADerivations.Analysis.RationalArithmetic.FiniteProducts.GaussianRationalBlockFactorTransfer
import IPRADerivations.Analysis.RationalArithmetic.GaussianRationalFixedWidthStrip
import IPRADerivations.Analysis.RationalArithmetic.FiniteProducts.GaussianRationalPaddedProductDegree
import IPRADerivations.Foundations.BoundedSyntaxInduction
import IPRADerivations.Core.CongruenceTactic

/-!
# Accumulating multiplicities of the actual monic norm

The quotient recursor starts at the original returned norm. Each step
applies actual fixed-width division for the next original fiber count.
The width is preserved for every numerical iteration, independently of
the degree and of the eventual total multiplicity.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNormFiniteZeroBound

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianNormFiberDivisibility
  (sourceOriginal sourceQuotient source_quotient_length source_evaluation_factor)
open LeanProofs.IPRA.Analysis.GaussianNormGroupFactorProduct
  (C T C_length C_evaluation_zero C_evaluation_succ C_degree T_total next_group_nonzero)
open LeanProofs.IPRA.Analysis.GaussianPolynomialMonicNorm (degreeBound)
open LeanProofs.IPRA.Analysis.GaussianPolynomialRowQuotient (H H_length H_evaluation)
open LeanProofs.IPRA.Analysis.GaussianRationalBlockFactorTransfer (baseLeft baseRight width terminal_evaluation)
open LeanProofs.IPRA.Analysis.GaussianRationalCurveFibers (selectedX)
open LeanProofs.IPRA.Analysis.GaussianRationalFiberGrouping (fiberCount groupCount)
open LeanProofs.IPRA.Analysis.GaussianRationalFixedWidthStrip (block block_length)
open LeanProofs.IPRA.Analysis.GaussianRationalGridCoefficientEquality (gridEqual coefficientsEqual)
open LeanProofs.IPRA.Analysis.GaussianRationalFiniteGridIdentity (gridPoint)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (evaluate qmul qzero horner_canonical)
open LeanProofs.IPRA.Analysis.GaussianRationalMonicReduction (evaluate_congr)
open LeanProofs.IPRA.Analysis.GaussianRationalPolynomialDegree (flag degree nonzero_of_flag_one degree_le)
open LeanProofs.IPRA.Analysis.GaussianRationalPolynomialBuffers (leftPad pad_length pad_evaluation)
open LeanProofs.IPRA.Analysis.GaussianRationalPolynomialProduct
  (product product_length product_canonical product_evaluation)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision (qmul_congr canonicalCoefficients)
open LeanProofs.IPRA.Analysis.GaussianReciprocalHorner (qmul_associative)
open LeanProofs.IPRA.Foundations.BoundedSyntax (BFm formula)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length)
open ConciseIPRA.PTm (zero succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def quotientData (P D L p : PTm n) : PTm n := pairT P (pairT D (pairT L p))

def quotientUpdate (Q D L p g : PTm n) : PTm n := block Q D (selectedX L p g) (fiberCount L p g)

def quotientInitial : PTm 1 := fstT (var 0)

def quotientStep : PTm 3 :=
  quotientUpdate (var 1) (fstT (sndT (var 2))) (fstT (sndT (sndT (var 2))))
    (sndT (sndT (sndT (var 2)))) (var 0)

def quotientF : PR 2 := rec2 quotientInitial quotientStep

def groupQuotient (P D L p g : PTm n) : PTm n := ap2 quotientF g (quotientData P D L p)

@[simp] theorem subst_quotientData {l : ℕ} (σ : Fin n → PTm l) (P D L p : PTm n) :
    Syn.subst σ (quotientData P D L p) = quotientData (Syn.subst σ P) (Syn.subst σ D)
      (Syn.subst σ L) (Syn.subst σ p) := by simp [quotientData]

@[simp] theorem subst_quotientUpdate {l : ℕ} (σ : Fin n → PTm l) (Q D L p g : PTm n) :
    Syn.subst σ (quotientUpdate Q D L p g) = quotientUpdate (Syn.subst σ Q) (Syn.subst σ D)
      (Syn.subst σ L) (Syn.subst σ p) (Syn.subst σ g) := by simp [quotientUpdate]

@[simp] theorem subst_groupQuotient {l : ℕ} (σ : Fin n → PTm l) (P D L p g : PTm n) :
    Syn.subst σ (groupQuotient P D L p g) = groupQuotient (Syn.subst σ P) (Syn.subst σ D)
      (Syn.subst σ L) (Syn.subst σ p) (Syn.subst σ g) := by simp [groupQuotient]

private theorem update_congr {Q Q' D D' L L' p p' g g' : PTm n}
    (hQ : Γ ⊢[PRAAx] Q ≐ Q') (hD : Γ ⊢[PRAAx] D ≐ D') (hL : Γ ⊢[PRAAx] L ≐ L')
    (hp : Γ ⊢[PRAAx] p ≐ p') (hg : Γ ⊢[PRAAx] g ≐ g') :
    Γ ⊢[PRAAx] quotientUpdate Q D L p g ≐ quotientUpdate Q' D' L' p' g' := by
  ipra_congr (quotientUpdate (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) with [hQ, hD, hL, hp, hg]

theorem quotient_zero (P D L p : PTm n) : Γ ⊢[PRAAx] groupQuotient P D L p zero ≐ P := by
  have initial := rec2_zero (Γ := Γ) quotientInitial quotientStep (quotientData P D L p)
  simp only [quotientInitial,subst_fstT,Syn.subst_var,Matrix.cons_val_zero] at initial
  exact initial.eqTrans (fst_pair P (pairT D (pairT L p)))

theorem quotient_succ (P D L p g : PTm n) : Γ ⊢[PRAAx]
    groupQuotient P D L p (succ g) ≐ quotientUpdate (groupQuotient P D L p g) D L p g := by
  have step := rec2_succ (Γ := Γ) quotientInitial quotientStep g (quotientData P D L p)
  simp only [quotientStep,subst_quotientUpdate,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] at step
  have tail := snd_pair (Γ := Γ) P (pairT D (pairT L p))
  have last := (congrSnd tail).eqTrans (snd_pair D (pairT L p))
  exact step.eqTrans (update_congr (.eqRefl _) ((congrFst tail).eqTrans (fst_pair D (pairT L p)))
    ((congrFst last).eqTrans (fst_pair L p)) ((congrSnd last).eqTrans (snd_pair L p)) (.eqRefl _))

theorem quotient_length (P D L p g : PTm n) (hP : Γ ⊢[PRAAx] length P ≐ succ D) :
    Γ ⊢[PRAAx] length (groupQuotient P D L p g) ≐ succ D := by
  have all : Γ ⊢[PRAAx] .all
      (length (groupQuotient (Syn.shift P) (Syn.shift D) (Syn.shift L) (Syn.shift p) (var 0)) ≐ succ (Syn.shift D)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [Fm.subst_eq,subst_length,subst_groupQuotient,ConciseIPRA.PTm.subst_succ,
        Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact (congrFst (quotient_zero P D L p)).eqTrans hP
    · simp only [Fm.subst_eq,subst_length,subst_groupQuotient,ConciseIPRA.PTm.subst_succ,
        Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact (congrFst (quotient_succ _ _ _ _ _)).eqTrans (block_length _ _ _ _ Prf.hyp0)
  simpa only [Fm.subst_eq,subst_length,subst_groupQuotient,ConciseIPRA.PTm.subst_succ,
    Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE g

def paddedNorm (P L p g : PTm n) : PTm n := leftPad P (T L p g)

def accumulatedProduct (P D L p g : PTm n) : PTm n :=
  product (C L p g) (groupQuotient P D L p g) (T L p g) D

def reconstruction (P D L p g : PTm n) : Fm PTm n :=
  coefficientsEqual (paddedNorm P L p g) (accumulatedProduct P D L p g) (T L p g+D)

@[simp] theorem subst_paddedNorm {l : ℕ} (σ : Fin n → PTm l) (P L p g : PTm n) :
    Syn.subst σ (paddedNorm P L p g) = paddedNorm (Syn.subst σ P) (Syn.subst σ L)
      (Syn.subst σ p) (Syn.subst σ g) := by simp [paddedNorm]

@[simp] theorem subst_accumulatedProduct {l : ℕ} (σ : Fin n → PTm l) (P D L p g : PTm n) :
    Syn.subst σ (accumulatedProduct P D L p g) = accumulatedProduct (Syn.subst σ P) (Syn.subst σ D)
      (Syn.subst σ L) (Syn.subst σ p) (Syn.subst σ g) := by simp [accumulatedProduct]

@[simp] theorem subst_reconstruction {l : ℕ} (σ : Fin n → PTm l) (P D L p g : PTm n) :
    (reconstruction P D L p g).subst σ = reconstruction (Syn.subst σ P) (Syn.subst σ D)
      (Syn.subst σ L) (Syn.subst σ p) (Syn.subst σ g) := by simp [reconstruction]

private theorem padded_length (P D L p g : PTm n) (hP : Γ ⊢[PRAAx] length P ≐ succ D) :
    Γ ⊢[PRAAx] length (paddedNorm P L p g) ≐ succ (T L p g+D) :=
  (pad_length P (T L p g)).eqTrans ((congrAdd (.eqRefl _) hP).eqTrans (by ipra_ring))

theorem product_evaluation_at (P D L p g z : PTm n) (hP : Γ ⊢[PRAAx] length P ≐ succ D) : Γ ⊢[PRAAx]
    evaluate (accumulatedProduct P D L p g) z ≐
      qmul (evaluate (C L p g) z) (evaluate (groupQuotient P D L p g) z) :=
  product_evaluation _ _ _ _ _ (C_length _ _ _) (quotient_length _ _ _ _ _ hP)

theorem reconstruction_evaluation (P D L p g z : PTm n) (hP : Γ ⊢[PRAAx] length P ≐ succ D)
    (h : Γ ⊢[PRAAx] reconstruction P D L p g) : Γ ⊢[PRAAx]
    evaluate P z ≐ evaluate (accumulatedProduct P D L p g) z :=
  (pad_evaluation P (T L p g) z).eqSymm.eqTrans
    (GaussianRationalLinearCancellation.coefficient_evaluation _ _ _ _ (padded_length _ _ _ _ _ hP)
      (product_length _ _ _ _) h)

private theorem zero_product_evaluation (P D L p z : PTm n) (hP : Γ ⊢[PRAAx] length P ≐ succ D) :
    Γ ⊢[PRAAx] evaluate (accumulatedProduct P D L p zero) z ≐ evaluate P z :=
  (product_evaluation_at _ _ _ _ _ _ hP).eqTrans
    ((qmul_congr (C_evaluation_zero _ _ _) (evaluate_congr (quotient_zero _ _ _ _) (.eqRefl _))).eqTrans
      ((GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans
        (GaussianReciprocalHorner.qmul_one_right _ (horner_canonical _ _ _))))

theorem zero_reconstruction (P D L p : PTm n) (hP : Γ ⊢[PRAAx] length P ≐ succ D)
    (hCan : Γ ⊢[PRAAx] canonicalCoefficients P) : Γ ⊢[PRAAx] reconstruction P D L p zero := by
  have shiftedLength : Γ.map Fm.shift ⊢[PRAAx] length (Syn.shift P) ≐ succ (Syn.shift D) := by
    simpa only [Fm.shift,Fm.subst_eq,subst_length,ConciseIPRA.PTm.subst_succ,Syn.shift] using hP.shift
  have grid : Γ ⊢[PRAAx] gridEqual (paddedNorm P L p zero) (accumulatedProduct P D L p zero) (T L p zero+D) := by
    refine .allI (.impI ?_)
    simpa only [Syn.shift,subst_accumulatedProduct,ConciseIPRA.PTm.subst_zero,paddedNorm,
      GaussianRationalPolynomialBuffers.subst_leftPad,GaussianNormGroupFactorProduct.subst_T] using
      (pad_evaluation (Syn.shift P) (T (Syn.shift L) (Syn.shift p) zero) (gridPoint (var 0))).eqTrans
        (zero_product_evaluation (Syn.shift P) (Syn.shift D) (Syn.shift L) (Syn.shift p)
          (gridPoint (var 0)) shiftedLength.wk).eqSymm
  exact GaussianRationalGridCoefficientEquality.coefficients_equal _ _ _ (padded_length _ _ _ _ _ hP)
    (product_length _ _ _ _) (GaussianPolynomialMonicCompanion.pad_canonical _ _ hCan)
    (product_canonical _ _ _ _) grid

def boundedReconstruction (P D L p g : PTm n) : BFm n :=
  .all (succ (T L p g+D)) (.eq
    (entry (Syn.shift (paddedNorm P L p g)) (var 0))
    (entry (Syn.shift (accumulatedProduct P D L p g)) (var 0)))

theorem bounded_of_reconstruction (P D L p g : PTm n) (h : Γ ⊢[PRAAx] reconstruction P D L p g) :
    Γ ⊢[PRAAx] formula (boundedReconstruction P D L p g) := by
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift (succ (T L p g+D))) :: Γ.map Fm.shift
  have range : Δ ⊢[PRAAx] lt (var 0) (succ (Syn.shift (T L p g+D))) := by
    simpa only [Δ,Syn.shift,ConciseIPRA.PTm.subst_succ] using
      (Prf.hyp0 : Δ ⊢[PRAAx] lt (var 0) (Syn.shift (succ (T L p g+D))))
  exact .impE h.allOpen.wk ((succ_monus_succ _ _).eqSymm.eqTrans range)

theorem reconstruction_of_bounded (P D L p g : PTm n) (h : Γ ⊢[PRAAx] formula (boundedReconstruction P D L p g)) :
    Γ ⊢[PRAAx] reconstruction P D L p g := by
  refine .allI (.impI ?_)
  exact .impE h.allOpen.wk ((succ_monus_succ _ _).eqTrans Prf.hyp0)

@[simp] theorem subst_formula_boundedReconstruction {l : ℕ} (σ : Fin n → PTm l) (P D L p g : PTm n) :
    (formula (boundedReconstruction P D L p g)).subst σ = formula (boundedReconstruction
      (Syn.subst σ P) (Syn.subst σ D) (Syn.subst σ L) (Syn.subst σ p) (Syn.subst σ g)) := by
  simp only [boundedReconstruction,formula,Fm.subst_all,Fm.subst_imp,Fm.subst_eq,subst_lt,
    Foundations.MasterCertificate.subst_entry,Syn.subst_var,Syn.up_zero,Foundations.BoundedFormulas.subst_up_shift',
    ConciseIPRA.PTm.subst_succ,PTm.subst_add,GaussianNormGroupFactorProduct.subst_T,
    subst_paddedNorm,subst_accumulatedProduct]

def sourceReconstruction (F G m a c L p g : PTm n) : Fm PTm n :=
  reconstruction (sourceOriginal F G m a c) (degreeBound m a c) L p g

def sourceTransferInput (F G m a c L p g : PTm n) : Fm PTm n :=
  GaussianRationalBlockFactorTransfer.input (C L p g)
    (groupQuotient (sourceOriginal F G m a c) (degreeBound m a c) L p g) (sourceQuotient F G m a c L p g)
    (T L p g) (degreeBound m a c) (degreeBound m a c) (fiberCount L p g) (selectedX L p g)

private theorem base_evaluation (F G m a c L p g z : PTm n)
    (hNorm : Γ ⊢[PRAAx] GaussianPolynomialMonicNorm.input F G m a c)
    (hPoints : Γ ⊢[PRAAx] GaussianRationalCurveFibers.sourceInput F G m L)
    (hReconstruction : Γ ⊢[PRAAx] sourceReconstruction F G m a c L p g) : Γ ⊢[PRAAx]
    evaluate (baseLeft (C L p g) (groupQuotient (sourceOriginal F G m a c) (degreeBound m a c) L p g)
      (T L p g) (degreeBound m a c) (degreeBound m a c) (fiberCount L p g)) z ≐
    evaluate (baseRight (sourceQuotient F G m a c L p g) (T L p g) (degreeBound m a c) (degreeBound m a c)
      (fiberCount L p g) (selectedX L p g)) z := by
  have original := reconstruction_evaluation (sourceOriginal F G m a c) (degreeBound m a c) L p g z
    (GaussianPolynomialMonicNorm.returned_length _ _ _ _ _) hReconstruction
  have localFactor := source_evaluation_factor F G m a c L p g z hNorm hPoints
  have padded : Γ ⊢[PRAAx]
      evaluate (baseRight (sourceQuotient F G m a c L p g) (T L p g) (degreeBound m a c) (degreeBound m a c)
        (fiberCount L p g) (selectedX L p g)) z ≐
      evaluate (product (H (selectedX L p g) (fiberCount L p g)) (sourceQuotient F G m a c L p g)
        (fiberCount L p g) (degreeBound m a c)) z := pad_evaluation _ _ _
  have right := padded.eqTrans
    ((product_evaluation (H (selectedX L p g) (fiberCount L p g)) (sourceQuotient F G m a c L p g)
      (fiberCount L p g) (degreeBound m a c) z (H_length _ _) (source_quotient_length _ _ _ _ _ _ _ _)).eqTrans
      (qmul_congr (H_evaluation _ _ z) (.eqRefl _)))
  exact (pad_evaluation _ _ z).eqTrans (original.eqSymm.eqTrans (localFactor.eqTrans right.eqSymm))

theorem source_transfer_input (F G m a c L p g : PTm n)
    (hNorm : Γ ⊢[PRAAx] GaussianPolynomialMonicNorm.input F G m a c)
    (hPoints : Γ ⊢[PRAAx] GaussianRationalCurveFibers.sourceInput F G m L)
    (hGroup : Γ ⊢[PRAAx] lt g (groupCount L p))
    (hReconstruction : Γ ⊢[PRAAx] sourceReconstruction F G m a c L p g) :
    Γ ⊢[PRAAx] sourceTransferInput F G m a c L p g := by
  have normShift : Γ.map Fm.shift ⊢[PRAAx] GaussianPolynomialMonicNorm.input
      (Syn.shift F) (Syn.shift G) (Syn.shift m) (Syn.shift a) (Syn.shift c) := by
    simpa only [Fm.shift,GaussianPolynomialMonicNorm.subst_input,Syn.shift] using hNorm.shift
  have pointsShift : Γ.map Fm.shift ⊢[PRAAx] GaussianRationalCurveFibers.sourceInput
      (Syn.shift F) (Syn.shift G) (Syn.shift m) (Syn.shift L) := by
    simpa only [Fm.shift,GaussianRationalCurveFibers.subst_sourceInput,Syn.shift] using hPoints.shift
  have reconstructionShift : Γ.map Fm.shift ⊢[PRAAx] sourceReconstruction
      (Syn.shift F) (Syn.shift G) (Syn.shift m) (Syn.shift a) (Syn.shift c) (Syn.shift L) (Syn.shift p) (Syn.shift g) := by
    simpa [Fm.shift,sourceReconstruction,Syn.shift] using hReconstruction.shift
  refine .andI (C_length _ _ _) (.andI (quotient_length _ _ _ _ _ (GaussianPolynomialMonicNorm.returned_length _ _ _ _ _))
    (.andI (source_quotient_length _ _ _ _ _ _ _ _) (.andI (next_group_nonzero _ _ _ hGroup) ?_)))
  refine .allI (.impI ?_)
  simpa [Syn.shift] using base_evaluation (Syn.shift F) (Syn.shift G) (Syn.shift m) (Syn.shift a) (Syn.shift c)
    (Syn.shift L) (Syn.shift p) (Syn.shift g) (gridPoint (var 0)) normShift.wk pointsShift.wk reconstructionShift.wk

private theorem next_evaluation (F G m a c L p g z : PTm n)
    (hNorm : Γ ⊢[PRAAx] GaussianPolynomialMonicNorm.input F G m a c)
    (hPoints : Γ ⊢[PRAAx] GaussianRationalCurveFibers.sourceInput F G m L)
    (hGroup : Γ ⊢[PRAAx] lt g (groupCount L p))
    (hReconstruction : Γ ⊢[PRAAx] sourceReconstruction F G m a c L p g) : Γ ⊢[PRAAx]
    evaluate (paddedNorm (sourceOriginal F G m a c) L p (succ g)) z ≐
    evaluate (accumulatedProduct (sourceOriginal F G m a c) (degreeBound m a c) L p (succ g)) z := by
  have transfer := source_transfer_input F G m a c L p g hNorm hPoints hGroup hReconstruction
  have terminal := terminal_evaluation (C L p g)
    (groupQuotient (sourceOriginal F G m a c) (degreeBound m a c) L p g) (sourceQuotient F G m a c L p g)
    (T L p g) (degreeBound m a c) (degreeBound m a c) (fiberCount L p g) (selectedX L p g) z transfer
  have actualQuotient := evaluate_congr (Γ := Γ)
    (quotient_succ (sourceOriginal F G m a c) (degreeBound m a c) L p g) (.eqRefl z)
  have localFactor := source_evaluation_factor F G m a c L p g z hNorm hPoints
  have nextValue := (product_evaluation_at (sourceOriginal F G m a c) (degreeBound m a c) L p (succ g) z
    (GaussianPolynomialMonicNorm.returned_length _ _ _ _ _)).eqTrans
    (qmul_congr (C_evaluation_succ L p g z) actualQuotient)
  refine (pad_evaluation _ _ z).eqTrans (localFactor.eqTrans ?_)
  exact (qmul_congr (.eqRefl _) terminal.eqSymm).eqTrans
    ((qmul_associative _ _ _).eqSymm.eqTrans
      ((qmul_congr (GaussianRationalPowerAlgebra.qmul_commutative _ _) (.eqRefl _)).eqTrans nextValue.eqSymm))

theorem next_reconstruction (F G m a c L p g : PTm n)
    (hNorm : Γ ⊢[PRAAx] GaussianPolynomialMonicNorm.input F G m a c)
    (hPoints : Γ ⊢[PRAAx] GaussianRationalCurveFibers.sourceInput F G m L)
    (hGroup : Γ ⊢[PRAAx] lt g (groupCount L p))
    (hReconstruction : Γ ⊢[PRAAx] sourceReconstruction F G m a c L p g) :
    Γ ⊢[PRAAx] sourceReconstruction F G m a c L p (succ g) := by
  have normShift : Γ.map Fm.shift ⊢[PRAAx] GaussianPolynomialMonicNorm.input
      (Syn.shift F) (Syn.shift G) (Syn.shift m) (Syn.shift a) (Syn.shift c) := by
    simpa only [Fm.shift,GaussianPolynomialMonicNorm.subst_input,Syn.shift] using hNorm.shift
  have pointsShift : Γ.map Fm.shift ⊢[PRAAx] GaussianRationalCurveFibers.sourceInput
      (Syn.shift F) (Syn.shift G) (Syn.shift m) (Syn.shift L) := by
    simpa only [Fm.shift,GaussianRationalCurveFibers.subst_sourceInput,Syn.shift] using hPoints.shift
  have groupShift : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift g) (groupCount (Syn.shift L) (Syn.shift p)) := by
    simpa [Fm.shift,Syn.shift] using hGroup.shift
  have reconstructionShift : Γ.map Fm.shift ⊢[PRAAx] sourceReconstruction
      (Syn.shift F) (Syn.shift G) (Syn.shift m) (Syn.shift a) (Syn.shift c) (Syn.shift L) (Syn.shift p) (Syn.shift g) := by
    simpa [Fm.shift,sourceReconstruction,Syn.shift] using hReconstruction.shift
  refine GaussianRationalGridCoefficientEquality.coefficients_equal _ _ _
    (padded_length _ _ _ _ _ (GaussianPolynomialMonicNorm.returned_length _ _ _ _ _))
    (product_length _ _ _ _) (GaussianPolynomialMonicCompanion.pad_canonical _ _
      (GaussianPolynomialMonicNorm.returned_canonical _ _ _ _ _)) (product_canonical _ _ _ _) ?_
  refine .allI (.impI ?_)
  simpa [Syn.shift] using next_evaluation (Syn.shift F) (Syn.shift G) (Syn.shift m) (Syn.shift a) (Syn.shift c)
    (Syn.shift L) (Syn.shift p) (Syn.shift g) (gridPoint (var 0)) normShift.wk pointsShift.wk groupShift.wk reconstructionShift.wk

private def guardedReconstruction (P D L p g : PTm n) : BFm n :=
  .imp (BFm.le g (groupCount L p)) (boundedReconstruction P D L p g)

private theorem guarded_formula (P D L p g : PTm n) : formula (guardedReconstruction P D L p g) =
    (le g (groupCount L p) ⟶ formula (boundedReconstruction P D L p g)) := rfl

private theorem subst_guarded_formula {l : ℕ} (σ : Fin n → PTm l) (P D L p g : PTm n) :
    (formula (guardedReconstruction P D L p g)).subst σ = formula (guardedReconstruction
      (Syn.subst σ P) (Syn.subst σ D) (Syn.subst σ L) (Syn.subst σ p) (Syn.subst σ g)) := by
  simp only [guarded_formula,Fm.subst_imp,subst_le,Foundations.FiniteFiberGrouping.subst_groupCount,
    subst_formula_boundedReconstruction]

theorem source_reconstruction (F G m a c L p g : PTm n)
    (hNorm : Γ ⊢[PRAAx] GaussianPolynomialMonicNorm.input F G m a c)
    (hPoints : Γ ⊢[PRAAx] GaussianRationalCurveFibers.sourceInput F G m L)
    (hGroup : Γ ⊢[PRAAx] le g (groupCount L p)) : Γ ⊢[PRAAx] sourceReconstruction F G m a c L p g := by
  let P := sourceOriginal F G m a c
  let D := degreeBound m a c
  let law := guardedReconstruction (Syn.shift P) (Syn.shift D) (Syn.shift L) (Syn.shift p) (var 0)
  have normShift : Γ.map Fm.shift ⊢[PRAAx] GaussianPolynomialMonicNorm.input
      (Syn.shift F) (Syn.shift G) (Syn.shift m) (Syn.shift a) (Syn.shift c) := by
    simpa only [Fm.shift,GaussianPolynomialMonicNorm.subst_input,Syn.shift] using hNorm.shift
  have pointsShift : Γ.map Fm.shift ⊢[PRAAx] GaussianRationalCurveFibers.sourceInput
      (Syn.shift F) (Syn.shift G) (Syn.shift m) (Syn.shift L) := by
    simpa only [Fm.shift,GaussianRationalCurveFibers.subst_sourceInput,Syn.shift] using hPoints.shift
  have initial : Γ ⊢[PRAAx] (formula law).subst (Syn.inst zero) := by
    dsimp only [law]
    rw [subst_guarded_formula]
    simp only [Syn.inst_zero,Syn.subst_var,Syn.subst_inst_shift,guarded_formula]
    exact .impI ((bounded_of_reconstruction P D L p zero
      (zero_reconstruction P D L p (GaussianPolynomialMonicNorm.returned_length _ _ _ _ _)
        (GaussianPolynomialMonicNorm.returned_canonical _ _ _ _ _))).wk)
  have advance : formula law :: Γ.map Fm.shift ⊢[PRAAx] (formula law).subst (Syn.repl (succ (var 0))) := by
    dsimp only [law]
    rw [subst_guarded_formula]
    simp only [Syn.repl_zero,Syn.subst_var,subst_repl_shift,guarded_formula]
    refine .impI ?_
    let bound := groupCount (Syn.shift L) (Syn.shift p)
    let Δ := lt (var 0) bound :: formula law :: Γ.map Fm.shift
    have nextGroup : Δ ⊢[PRAAx] lt (var 0) bound := Prf.hyp0
    have previous : Δ ⊢[PRAAx] le (var 0) bound ⟶
        formula (boundedReconstruction (Syn.shift P) (Syn.shift D) (Syn.shift L) (Syn.shift p) (var 0)) := Prf.hyp1
    have old := reconstruction_of_bounded (Syn.shift P) (Syn.shift D) (Syn.shift L) (Syn.shift p) (var 0)
      (.impE previous (le_of_lt nextGroup))
    have next := next_reconstruction (Syn.shift F) (Syn.shift G) (Syn.shift m) (Syn.shift a) (Syn.shift c)
      (Syn.shift L) (Syn.shift p) (var 0) normShift.wk.wk pointsShift.wk.wk nextGroup
      (by simpa [P,D,sourceReconstruction,Syn.shift] using old)
    have step : Δ ⊢[PRAAx] reconstruction (Syn.shift P) (Syn.shift D) (Syn.shift L) (Syn.shift p) (succ (var 0)) := by
      simpa [P,D,sourceReconstruction,Syn.shift] using next
    exact bounded_of_reconstruction _ _ _ _ _ step
  have conclusion := Foundations.BoundedSyntaxInduction.induction_at law g initial advance
  have reached : Γ ⊢[PRAAx] le g (groupCount L p) ⟶ formula (boundedReconstruction P D L p g) := by
    dsimp only [law] at conclusion
    rw [subst_guarded_formula] at conclusion
    simpa only [Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift,guarded_formula] using conclusion
  exact reconstruction_of_bounded P D L p g (.impE reached hGroup)

def input (F G m a c L : PTm n) : Fm PTm n := GaussianPolynomialMonicNorm.input F G m a c ⋏
  (GaussianRationalCurveFibers.sourceInput F G m L ⋏ flag (sourceOriginal F G m a c) (degreeBound m a c) ≐ one)

theorem finite_norm_zero_bound (F G m a c L p : PTm n) (h : Γ ⊢[PRAAx] input F G m a c L) :
    Γ ⊢[PRAAx] le (length L) (degree (sourceOriginal F G m a c) (degreeBound m a c)) := by
  let P := sourceOriginal F G m a c
  let D := degreeBound m a c
  let g := groupCount L p
  have factored := source_reconstruction F G m a c L p g (.andE₁ h) (.andE₁ (.andE₂ h)) (le_refl g)
  have original := nonzero_of_flag_one P D (.andE₂ (.andE₂ h))
  have bound := GaussianRationalPaddedProductDegree.full_width_factor_le P (C L p g) (groupQuotient P D L p g)
    (T L p g) D (.andI (GaussianPolynomialMonicNorm.returned_length _ _ _ _ _) (.andI original factored))
    (C_degree L p g)
  exact le_congr (T_total L p) (.eqRefl _) bound

theorem finite_norm_width_bound (F G m a c L p : PTm n) (h : Γ ⊢[PRAAx] input F G m a c L) :
    Γ ⊢[PRAAx] le (length L) (degreeBound m a c) :=
  le_trans (finite_norm_zero_bound F G m a c L p h) (degree_le _ _)

theorem original_group_norm_zero (F G m a c L p g : PTm n)
    (hNorm : Γ ⊢[PRAAx] GaussianPolynomialMonicNorm.input F G m a c)
    (hPoints : Γ ⊢[PRAAx] GaussianRationalCurveFibers.sourceInput F G m L)
    (hGroup : Γ ⊢[PRAAx] lt g (groupCount L p)) :
    Γ ⊢[PRAAx] evaluate (sourceOriginal F G m a c) (selectedX L p g) ≐ qzero := by
  let x := selectedX L p g
  let t := fiberCount L p g
  have positive := GaussianRationalFiberGrouping.fiber_nonempty L p g hGroup
  have same := GaussianRationalValueEquality.value_equal_refl (Γ := Γ) x
  have difference := GaussianRationalValueEquality.difference_zero_of_equal_values _ _ same
  have powerZero : Γ ⊢[PRAAx] GaussianRationalReciprocal.power qzero t ≐ qzero := by
    refine .orE (zero_or_succ t) ?_ ?_
    · exact not_succ_le_self zero _ (le_congr (.eqRefl _) Prf.hyp0 positive.wk)
    · exact (congrAp2 GaussianRationalReciprocal.powerF Prf.hyp0 (.eqRefl _)).eqTrans
        (GaussianRationalPowerNonzero.zero_positive_power _)
  have rootPower := (congrAp2 GaussianRationalReciprocal.powerF (.eqRefl t) difference).eqTrans powerZero
  exact (source_evaluation_factor F G m a c L p g x hNorm hPoints).eqTrans
    ((qmul_congr rootPower (.eqRefl _)).eqTrans (GaussianRationalSyntheticDivision.qmul_zero_left _))

theorem original_point_norm_zero (F G m a c L p i : PTm n)
    (hNorm : Γ ⊢[PRAAx] GaussianPolynomialMonicNorm.input F G m a c)
    (hPoints : Γ ⊢[PRAAx] GaussianRationalCurveFibers.sourceInput F G m L)
    (hi : Γ ⊢[PRAAx] lt i (length L)) : Γ ⊢[PRAAx]
    evaluate (sourceOriginal F G m a c) (GaussianRationalFiberGrouping.abscissa L i) ≐ qzero := by
  let g := GaussianRationalFiberGrouping.groupOf L p i
  let slot := GaussianRationalFiberGrouping.slotOf L p i
  have covered := GaussianRationalFiberGrouping.coverage L p i hi
  have groupBound := Prf.andE₁ covered
  have slotBound := Prf.andE₁ (Prf.andE₂ covered)
  have sourceIndex := Prf.andE₂ (Prf.andE₂ covered)
  have member := GaussianRationalFiberGrouping.member_abscissa L p g slot slotBound
  have abscissa := congrFst (Foundations.SequenceComposition.entry_congr (.eqRefl L) sourceIndex)
  have value := GaussianRationalValueEquality.value_equal_trans _ _ _
    (GaussianRationalValueEquality.value_equal_of_code abscissa.eqSymm) member
  exact (GaussianRationalValueEquality.evaluation_value_proper _ _ _ value).eqTrans
    (original_group_norm_zero F G m a c L p g hNorm hPoints groupBound)

theorem actual_norm_accumulation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (GaussianPolynomialMonicNorm.input (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      GaussianRationalCurveFibers.sourceInput (var 0) (var 1) (var 2) (var 5) ⟶
      le (var 7) (groupCount (var 5) (var 6)) ⟶ sourceReconstruction (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)) :=
  closeUniv 8 (.impI (.impI (.impI (source_reconstruction _ _ _ _ _ _ _ _ (Prf.hyp1.wk) Prf.hyp1 Prf.hyp0))))

theorem actual_finite_norm_zero_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
      le (length (var 5)) (degree (sourceOriginal (var 0) (var 1) (var 2) (var 3) (var 4)) (degreeBound (var 2) (var 3) (var 4)))) :=
  closeUniv 6 (.impI (finite_norm_zero_bound _ _ _ _ _ _ zero Prf.hyp0))

theorem actual_original_point_norm_zero_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (GaussianPolynomialMonicNorm.input (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      GaussianRationalCurveFibers.sourceInput (var 0) (var 1) (var 2) (var 5) ⟶
      lt (var 6) (length (var 5)) ⟶ evaluate (sourceOriginal (var 0) (var 1) (var 2) (var 3) (var 4))
        (GaussianRationalFiberGrouping.abscissa (var 5) (var 6)) ≐ qzero) :=
  closeUniv 7 (.impI (.impI (.impI (original_point_norm_zero _ _ _ _ _ _ zero _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianNormFiniteZeroBound
