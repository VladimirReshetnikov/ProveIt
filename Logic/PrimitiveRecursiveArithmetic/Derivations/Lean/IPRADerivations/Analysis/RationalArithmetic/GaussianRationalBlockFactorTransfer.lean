import IPRADerivations.Analysis.RationalArithmetic.GaussianRationalFixedWidthStrip
import IPRADerivations.Analysis.RationalArithmetic.GaussianRationalLinearCancellation
import IPRADerivations.Analysis.RationalArithmetic.Powers.GaussianRationalPowerNonzero
import IPRADerivations.Analysis.Polynomials.GaussianPolynomialRowQuotient
import IPRADerivations.Analysis.RationalArithmetic.GaussianRationalTranslationStages
import IPRADerivations.Foundations.BoundedSyntaxInduction
import IPRADerivations.Core.CongruenceTactic

/-!
# Actual inner fixed-width factor transfer

One finite comparison of the ORIGINAL products C*Q and (X-x)^t*J starts
a bounded coefficient induction on the actual fixed-width strip recursor.
The previously accumulated C is required to have nonzero actual value at x.
Every current root is derived from the coefficient invariant; cancellation
uses actual monic linear buffers on a finite grid, including the point x.
All degrees, counts, data and coefficient/query indices are numerical.
No successful-strip or all-stage factor law is an input.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalBlockFactorTransfer

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (qzero qmul canonical evaluate)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (qsub)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision (qone qmul_congr canonicalCoefficients)
open LeanProofs.IPRA.Analysis.GaussianRationalPolynomialProduct (product product_length product_canonical product_evaluation)
open LeanProofs.IPRA.Analysis.GaussianRationalPolynomialBuffers (leftPad pad_length pad_evaluation)
open LeanProofs.IPRA.Analysis.GaussianPolynomialRowQuotient (H H_length H_canonical H_evaluation)
open LeanProofs.IPRA.Analysis.GaussianRationalFixedWidthStrip (block block_length block_zero block_factor)
open LeanProofs.IPRA.Analysis.GaussianRationalReciprocal (power powerF power_zero power_succ)
open LeanProofs.IPRA.Analysis.GaussianRationalGridCoefficientEquality (gridEqual coefficientsEqual)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length entry_congr)
open LeanProofs.IPRA.Foundations.BoundedSyntax (BFm formula)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ app)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def width (T D E t : PTm n) : PTm n := T+D+t+E
def remaining (t r : PTm n) : PTm n := monus t r
def baseLeft (C Q T D E t : PTm n) : PTm n := leftPad (product C Q T D) (t+E)
def baseRight (J T D E t x : PTm n) : PTm n :=
  leftPad (product (H x t) J t E) (monus (width T D E t) (t+E))
def leftBuffer (C Q T D E t x r : PTm n) : PTm n :=
  leftPad (product C (block Q D x r) T D) (t+E)
def rightBuffer (J T D E t x r : PTm n) : PTm n :=
  leftPad (product (H x (remaining t r)) J (remaining t r) E)
    (monus (width T D E t) (remaining t r+E))
def relation (C Q J T D E t x r : PTm n) : Fm PTm n := .all
  (lt (var 0) (succ (width (Syn.shift T) (Syn.shift D) (Syn.shift E) (Syn.shift t))) ⟶
    entry (leftBuffer (Syn.shift C) (Syn.shift Q) (Syn.shift T) (Syn.shift D) (Syn.shift E)
      (Syn.shift t) (Syn.shift x) (Syn.shift r)) (var 0) ≐
    entry (rightBuffer (Syn.shift J) (Syn.shift T) (Syn.shift D) (Syn.shift E)
      (Syn.shift t) (Syn.shift x) (Syn.shift r)) (var 0))
def input (C Q J T D E t x : PTm n) : Fm PTm n := (length C ≐ succ T) ⋏
  ((length Q ≐ succ D) ⋏ ((length J ≐ succ E) ⋏
    (neg (evaluate C x ≐ qzero) ⋏ gridEqual (baseLeft C Q T D E t) (baseRight J T D E t x) (width T D E t))))

@[simp] theorem subst_width {l : ℕ} (σ : Fin n → PTm l) (T D E t : PTm n) :
    Syn.subst σ (width T D E t) = width (Syn.subst σ T) (Syn.subst σ D) (Syn.subst σ E) (Syn.subst σ t) := by simp [width]
@[simp] theorem subst_remaining {l : ℕ} (σ : Fin n → PTm l) (t r : PTm n) :
    Syn.subst σ (remaining t r) = remaining (Syn.subst σ t) (Syn.subst σ r) := by simp [remaining]
@[simp] theorem subst_baseLeft {l : ℕ} (σ : Fin n → PTm l) (C Q T D E t : PTm n) :
    Syn.subst σ (baseLeft C Q T D E t) = baseLeft (Syn.subst σ C) (Syn.subst σ Q)
      (Syn.subst σ T) (Syn.subst σ D) (Syn.subst σ E) (Syn.subst σ t) := by simp [baseLeft]
@[simp] theorem subst_baseRight {l : ℕ} (σ : Fin n → PTm l) (J T D E t x : PTm n) :
    Syn.subst σ (baseRight J T D E t x) = baseRight (Syn.subst σ J) (Syn.subst σ T)
      (Syn.subst σ D) (Syn.subst σ E) (Syn.subst σ t) (Syn.subst σ x) := by simp [baseRight]
@[simp] theorem subst_leftBuffer {l : ℕ} (σ : Fin n → PTm l) (C Q T D E t x r : PTm n) :
    Syn.subst σ (leftBuffer C Q T D E t x r) = leftBuffer (Syn.subst σ C) (Syn.subst σ Q)
      (Syn.subst σ T) (Syn.subst σ D) (Syn.subst σ E) (Syn.subst σ t) (Syn.subst σ x) (Syn.subst σ r) := by simp [leftBuffer]
@[simp] theorem subst_rightBuffer {l : ℕ} (σ : Fin n → PTm l) (J T D E t x r : PTm n) :
    Syn.subst σ (rightBuffer J T D E t x r) = rightBuffer (Syn.subst σ J) (Syn.subst σ T)
      (Syn.subst σ D) (Syn.subst σ E) (Syn.subst σ t) (Syn.subst σ x) (Syn.subst σ r) := by simp [rightBuffer]
@[simp] theorem subst_relation {l : ℕ} (σ : Fin n → PTm l) (C Q J T D E t x r : PTm n) :
    (relation C Q J T D E t x r).subst σ = relation (Syn.subst σ C) (Syn.subst σ Q) (Syn.subst σ J)
      (Syn.subst σ T) (Syn.subst σ D) (Syn.subst σ E) (Syn.subst σ t) (Syn.subst σ x) (Syn.subst σ r) := by
  simp [relation,Syn.subst_shift,Syn.shift_subst]
@[simp] theorem subst_input {l : ℕ} (σ : Fin n → PTm l) (C Q J T D E t x : PTm n) :
    (input C Q J T D E t x).subst σ = input (Syn.subst σ C) (Syn.subst σ Q) (Syn.subst σ J)
      (Syn.subst σ T) (Syn.subst σ D) (Syn.subst σ E) (Syn.subst σ t) (Syn.subst σ x) := by simp [input]

theorem product_congr {A A' B B' N N' M M' : PTm n} (hA : Γ ⊢[PRAAx] A ≐ A')
    (hB : Γ ⊢[PRAAx] B ≐ B') (hN : Γ ⊢[PRAAx] N ≐ N') (hM : Γ ⊢[PRAAx] M ≐ M') : Γ ⊢[PRAAx]
    product A B N M ≐ product A' B' N' M' := by
  ipra_congr (product (var 0) (var 1) (var 2) (var 3) : PTm 4) with [hA, hB, hN, hM]
theorem pad_congr {A B s t : PTm n} (hA : Γ ⊢[PRAAx] A ≐ B) (hs : Γ ⊢[PRAAx] s ≐ t) : Γ ⊢[PRAAx]
    leftPad A s ≐ leftPad B t := by
  ipra_congr (leftPad (var 0) (var 1) : PTm 2) with [hA, hs]
theorem H_congr {x y s t : PTm n} (hx : Γ ⊢[PRAAx] x ≐ y) (hs : Γ ⊢[PRAAx] s ≐ t) : Γ ⊢[PRAAx]
    H x s ≐ H y t := by
  ipra_congr (H (var 0) (var 1) : PTm 2) with [hx, hs]
theorem coefficients_congr {A A' B B' N : PTm n} (hA : Γ ⊢[PRAAx] A ≐ A')
    (hB : Γ ⊢[PRAAx] B ≐ B') (h : Γ ⊢[PRAAx] coefficientsEqual A B N) : Γ ⊢[PRAAx] coefficientsEqual A' B' N := by
  have transport := Prf.eqSubst (Ax := PRAAx) (Γ := Γ) (coefficientsEqual (var 0) (var 1) (var 2) : Fm PTm 3)
    ![A,B,N] ![A',B',N] (fun i => by fin_cases i; exact hA; exact hB; exact .eqRefl _)
  have rule : (Γ ⊢[PRAAx] coefficientsEqual A B N) → (Γ ⊢[PRAAx] coefficientsEqual A' B' N) := by
    simpa only [GaussianRationalGridCoefficientEquality.subst_coefficientsEqual,Syn.subst_var,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using transport
  exact rule h

theorem right_bound (T D E t r : PTm n) : Γ ⊢[PRAAx] le (remaining t r+E) (width T D E t) :=
  le_trans (add_le_add₂ (GaussianRationalMonicReconstruction.monus_le_left t r) (le_refl E))
    (le_of_eq_add (a := t+E) (d := T+D) (by unfold width; ipra_ring))
theorem left_length (C Q T D E t x r : PTm n) : Γ ⊢[PRAAx]
    length (leftBuffer C Q T D E t x r) ≐ succ (width T D E t) :=
  (pad_length _ _).eqTrans ((congrAdd (.eqRefl _) (product_length _ _ _ _)).eqTrans (by unfold width; ipra_ring))
theorem right_length (J T D E t x r : PTm n) : Γ ⊢[PRAAx]
    length (rightBuffer J T D E t x r) ≐ succ (width T D E t) :=
  (pad_length _ _).eqTrans ((congrAdd (.eqRefl _) (product_length _ _ _ _)).eqTrans
    ((by ipra_ring : Γ ⊢[PRAAx] monus (width T D E t) (remaining t r+E)+succ (remaining t r+E) ≐
      succ (remaining t r+E+monus (width T D E t) (remaining t r+E))).eqTrans
        (congrSucc (eq_add_of_le (right_bound T D E t r)).eqSymm)))
theorem left_canonical (C Q T D E t x r : PTm n) : Γ ⊢[PRAAx] canonicalCoefficients (leftBuffer C Q T D E t x r) :=
  GaussianPolynomialMonicCompanion.pad_canonical _ _ (product_canonical _ _ _ _)
theorem right_canonical (J T D E t x r : PTm n) : Γ ⊢[PRAAx] canonicalCoefficients (rightBuffer J T D E t x r) :=
  GaussianPolynomialMonicCompanion.pad_canonical _ _ (product_canonical _ _ _ _)
theorem left_zero (C Q T D E t x : PTm n) : Γ ⊢[PRAAx]
    leftBuffer C Q T D E t x zero ≐ baseLeft C Q T D E t :=
  pad_congr (product_congr (.eqRefl _) (block_zero _ _ _) (.eqRefl _) (.eqRefl _)) (.eqRefl _)
theorem right_zero (J T D E t x : PTm n) : Γ ⊢[PRAAx]
    rightBuffer J T D E t x zero ≐ baseRight J T D E t x :=
  pad_congr (product_congr (H_congr (.eqRefl _) (monus_zero t)) (.eqRefl _) (monus_zero t) (.eqRefl _))
    (congrMonus (.eqRefl _) (congrAdd (monus_zero t) (.eqRefl _)))
theorem base_left_length (C Q T D E t : PTm n) : Γ ⊢[PRAAx] length (baseLeft C Q T D E t) ≐ succ (width T D E t) :=
  (congrFst (left_zero C Q T D E t zero)).eqSymm.eqTrans (left_length _ _ _ _ _ _ _ _)
theorem base_right_length (J T D E t x : PTm n) : Γ ⊢[PRAAx] length (baseRight J T D E t x) ≐ succ (width T D E t) :=
  (congrFst (right_zero _ _ _ _ _ _)).eqSymm.eqTrans (right_length _ _ _ _ _ _ _)
theorem base_left_canonical (C Q T D E t : PTm n) : Γ ⊢[PRAAx] canonicalCoefficients (baseLeft C Q T D E t) :=
  GaussianRationalMonicReduction.canonical_coefficients_congr (left_zero C Q T D E t zero).eqSymm (left_canonical _ _ _ _ _ _ _ _)
theorem base_right_canonical (J T D E t x : PTm n) : Γ ⊢[PRAAx] canonicalCoefficients (baseRight J T D E t x) :=
  GaussianRationalMonicReduction.canonical_coefficients_congr (right_zero _ _ _ _ _ _).eqSymm (right_canonical _ _ _ _ _ _ _)

theorem relation_at (C Q J T D E t x r i : PTm n) (h : Γ ⊢[PRAAx] relation C Q J T D E t x r)
    (hi : Γ ⊢[PRAAx] le i (width T D E t)) : Γ ⊢[PRAAx]
    entry (leftBuffer C Q T D E t x r) i ≐ entry (rightBuffer J T D E t x r) i := by
  have rule : Γ ⊢[PRAAx] lt i (succ (width T D E t)) ⟶
      entry (leftBuffer C Q T D E t x r) i ≐ entry (rightBuffer J T D E t x r) i := by simpa [relation] using h.allE i
  exact .impE rule ((succ_monus_succ _ _).eqTrans hi)
theorem relation_coefficients (C Q J T D E t x r : PTm n) (h : Γ ⊢[PRAAx] relation C Q J T D E t x r) : Γ ⊢[PRAAx]
    coefficientsEqual (leftBuffer C Q T D E t x r) (rightBuffer J T D E t x r) (width T D E t) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] relation (Syn.shift C) (Syn.shift Q) (Syn.shift J) (Syn.shift T)
      (Syn.shift D) (Syn.shift E) (Syn.shift t) (Syn.shift x) (Syn.shift r) := by
    simpa only [Fm.shift,subst_relation,Syn.shift] using h.shift
  refine .allI (.impI ?_)
  simpa only [Syn.shift,subst_leftBuffer,subst_rightBuffer,subst_width] using
    relation_at (Syn.shift C) (Syn.shift Q) (Syn.shift J) (Syn.shift T) (Syn.shift D) (Syn.shift E)
      (Syn.shift t) (Syn.shift x) (Syn.shift r) (var 0) hs.wk Prf.hyp0
theorem coefficients_relation (C Q J T D E t x r : PTm n)
    (h : Γ ⊢[PRAAx] coefficientsEqual (leftBuffer C Q T D E t x r) (rightBuffer J T D E t x r) (width T D E t)) : Γ ⊢[PRAAx]
    relation C Q J T D E t x r := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] coefficientsEqual
      (leftBuffer (Syn.shift C) (Syn.shift Q) (Syn.shift T) (Syn.shift D) (Syn.shift E) (Syn.shift t) (Syn.shift x) (Syn.shift r))
      (rightBuffer (Syn.shift J) (Syn.shift T) (Syn.shift D) (Syn.shift E) (Syn.shift t) (Syn.shift x) (Syn.shift r))
      (width (Syn.shift T) (Syn.shift D) (Syn.shift E) (Syn.shift t)) := by
    simpa only [Fm.shift,GaussianRationalGridCoefficientEquality.subst_coefficientsEqual,
      subst_leftBuffer,subst_rightBuffer,subst_width,Syn.shift] using h.shift
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (succ (width (Syn.shift T) (Syn.shift D) (Syn.shift E) (Syn.shift t))) :: Γ.map Fm.shift
  have hi : Δ ⊢[PRAAx] le (var 0) (width (Syn.shift T) (Syn.shift D) (Syn.shift E) (Syn.shift t)) :=
    (succ_monus_succ _ _).eqSymm.eqTrans (Prf.hyp0 : Δ ⊢[PRAAx]
      lt (var 0) (succ (width (Syn.shift T) (Syn.shift D) (Syn.shift E) (Syn.shift t))))
  exact GaussianRationalLinearCancellation.coefficients_at _ _ _ (var 0) hs.wk hi

theorem left_evaluation (C Q T D E t x r z : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ T)
    (hQ : Γ ⊢[PRAAx] length Q ≐ succ D) : Γ ⊢[PRAAx]
    evaluate (leftBuffer C Q T D E t x r) z ≐ qmul (evaluate C z) (evaluate (block Q D x r) z) :=
  (pad_evaluation _ _ _).eqTrans (product_evaluation _ _ _ _ _ hC (block_length _ _ _ _ hQ))
theorem right_evaluation (J T D E t x r z : PTm n) (hJ : Γ ⊢[PRAAx] length J ≐ succ E) : Γ ⊢[PRAAx]
    evaluate (rightBuffer J T D E t x r) z ≐ qmul (power (qsub z x) (remaining t r)) (evaluate J z) :=
  (pad_evaluation _ _ _).eqTrans ((product_evaluation _ _ _ _ _ (H_length _ _) hJ).eqTrans
    (qmul_congr (H_evaluation _ _ _) (.eqRefl _)))
theorem relation_evaluation (C Q J T D E t x r z : PTm n)
    (h : Γ ⊢[PRAAx] relation C Q J T D E t x r) : Γ ⊢[PRAAx]
    evaluate (leftBuffer C Q T D E t x r) z ≐ evaluate (rightBuffer J T D E t x r) z :=
  GaussianRationalLinearCancellation.coefficient_evaluation _ _ _ _ (left_length _ _ _ _ _ _ _ _)
    (right_length _ _ _ _ _ _ _) (relation_coefficients _ _ _ _ _ _ _ _ _ h)

theorem input_c (C Q J T D E t x : PTm n) (h : Γ ⊢[PRAAx] input C Q J T D E t x) : Γ ⊢[PRAAx] length C ≐ succ T := .andE₁ h
theorem input_q (C Q J T D E t x : PTm n) (h : Γ ⊢[PRAAx] input C Q J T D E t x) : Γ ⊢[PRAAx] length Q ≐ succ D := .andE₁ (.andE₂ h)
theorem input_j (C Q J T D E t x : PTm n) (h : Γ ⊢[PRAAx] input C Q J T D E t x) : Γ ⊢[PRAAx] length J ≐ succ E := .andE₁ (.andE₂ (.andE₂ h))
theorem input_nonzero (C Q J T D E t x : PTm n) (h : Γ ⊢[PRAAx] input C Q J T D E t x) : Γ ⊢[PRAAx]
    neg (evaluate C x ≐ qzero) := .andE₁ (.andE₂ (.andE₂ (.andE₂ h)))
theorem input_grid (C Q J T D E t x : PTm n) (h : Γ ⊢[PRAAx] input C Q J T D E t x) : Γ ⊢[PRAAx]
    gridEqual (baseLeft C Q T D E t) (baseRight J T D E t x) (width T D E t) := .andE₂ (.andE₂ (.andE₂ (.andE₂ h)))

theorem base_relation (C Q J T D E t x : PTm n) (h : Γ ⊢[PRAAx] input C Q J T D E t x) : Γ ⊢[PRAAx]
    relation C Q J T D E t x zero := by
  have base : Γ ⊢[PRAAx] coefficientsEqual (baseLeft C Q T D E t) (baseRight J T D E t x) (width T D E t) :=
    GaussianRationalGridCoefficientEquality.coefficients_equal _ _ _ (base_left_length _ _ _ _ _ _)
      (base_right_length _ _ _ _ _ _) (base_left_canonical _ _ _ _ _ _)
      (base_right_canonical _ _ _ _ _ _) (input_grid _ _ _ _ _ _ _ _ h)
  exact coefficients_relation _ _ _ _ _ _ _ _ _
    (coefficients_congr (left_zero _ _ _ _ _ _ _).eqSymm (right_zero _ _ _ _ _ _).eqSymm base)

theorem remaining_step (t r : PTm n) (hr : Γ ⊢[PRAAx] lt r t) : Γ ⊢[PRAAx]
    remaining t r ≐ succ (remaining t (succ r)) := GaussianRationalTranslationStages.remaining_step _ _ hr
theorem right_at_root (J T D E t x r : PTm n) (hJ : Γ ⊢[PRAAx] length J ≐ succ E)
    (hr : Γ ⊢[PRAAx] lt r t) : Γ ⊢[PRAAx] evaluate (rightBuffer J T D E t x r) x ≐ qzero :=
  (right_evaluation _ _ _ _ _ _ _ _ hJ).eqTrans
    ((qmul_congr ((congrAp2 powerF (remaining_step _ _ hr) (GaussianCoefficientNormOrder.qsub_self x)).eqTrans
      (GaussianRationalPowerNonzero.zero_positive_power _)) (.eqRefl _)).eqTrans
        (GaussianRationalSyntheticDivision.qmul_zero_left _))

/-- The root of the actual current block is derived from the finite
coefficient witness and actual C(x) nonzero. -/
theorem root_from_relation (C Q J T D E t x r : PTm n) (h : Γ ⊢[PRAAx] input C Q J T D E t x)
    (hr : Γ ⊢[PRAAx] lt r t) (hRel : Γ ⊢[PRAAx] relation C Q J T D E t x r) : Γ ⊢[PRAAx]
    evaluate (block Q D x r) x ≐ qzero := by
  have productZero := (left_evaluation C Q T D E t x r x (input_c _ _ _ _ _ _ _ _ h) (input_q _ _ _ _ _ _ _ _ h)).eqSymm.eqTrans
    ((relation_evaluation _ _ _ _ _ _ _ _ _ _ hRel).eqTrans
      (right_at_root _ _ _ _ _ _ _ (input_j _ _ _ _ _ _ _ _ h) hr))
  exact GaussianRationalFiniteRoots.product_zero_reflect _ _
    (GaussianRationalHorner.horner_canonical _ _ _) (GaussianRationalHorner.horner_canonical _ _ _)
    (input_nonzero _ _ _ _ _ _ _ _ h) productZero

theorem commute_left (a b c : PTm n) : Γ ⊢[PRAAx] qmul a (qmul b c) ≐ qmul b (qmul a c) :=
  (GaussianReciprocalHorner.qmul_associative _ _ _).eqSymm.eqTrans
    ((qmul_congr (GaussianRationalPowerAlgebra.qmul_commutative _ _) (.eqRefl _)).eqTrans
      (GaussianReciprocalHorner.qmul_associative _ _ _))
theorem power_remaining (t r x z : PTm n) (hr : Γ ⊢[PRAAx] lt r t) : Γ ⊢[PRAAx]
    power (qsub z x) (remaining t r) ≐ qmul (qsub z x) (power (qsub z x) (remaining t (succ r))) :=
  (congrAp2 powerF (remaining_step _ _ hr) (.eqRefl _)).eqTrans
    ((power_succ _ _).eqTrans (GaussianRationalPowerAlgebra.qmul_commutative _ _))
theorem right_factorized (J T D E t x r z : PTm n) (hJ : Γ ⊢[PRAAx] length J ≐ succ E)
    (hr : Γ ⊢[PRAAx] lt r t) : Γ ⊢[PRAAx]
    evaluate (rightBuffer J T D E t x r) z ≐ qmul (qsub z x) (evaluate (rightBuffer J T D E t x (succ r)) z) :=
  (right_evaluation _ _ _ _ _ _ _ _ hJ).eqTrans
    ((qmul_congr (power_remaining _ _ _ _ hr) (.eqRefl _)).eqTrans
      ((GaussianReciprocalHorner.qmul_associative _ _ _).eqTrans
        (qmul_congr (.eqRefl _) (right_evaluation _ _ _ _ _ _ _ _ hJ).eqSymm)))
theorem left_factorized (C Q T D E t x r z : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ T)
    (hQ : Γ ⊢[PRAAx] length Q ≐ succ D) (hRoot : Γ ⊢[PRAAx] evaluate (block Q D x r) x ≐ qzero) : Γ ⊢[PRAAx]
    evaluate (leftBuffer C Q T D E t x r) z ≐ qmul (qsub z x) (evaluate (leftBuffer C Q T D E t x (succ r)) z) :=
  (left_evaluation _ _ _ _ _ _ _ _ _ hC hQ).eqTrans
    ((qmul_congr (.eqRefl _) (block_factor _ _ _ _ _ hQ hRoot)).eqTrans
      ((commute_left _ _ _).eqTrans
        (qmul_congr (.eqRefl _) (left_evaluation _ _ _ _ _ _ _ _ _ hC hQ).eqSymm)))

theorem linear_evaluation_equal (C Q J T D E t x r z : PTm n) (h : Γ ⊢[PRAAx] input C Q J T D E t x)
    (hr : Γ ⊢[PRAAx] lt r t) (hRel : Γ ⊢[PRAAx] relation C Q J T D E t x r) : Γ ⊢[PRAAx]
    evaluate (GaussianRationalLinearProduct.linear (leftBuffer C Q T D E t x (succ r)) x (succ (width T D E t))) z ≐
      evaluate (GaussianRationalLinearProduct.linear (rightBuffer J T D E t x (succ r)) x (succ (width T D E t))) z :=
  (GaussianRationalLinearProduct.linear_evaluation _ _ _ _ (left_length _ _ _ _ _ _ _ _) (left_canonical _ _ _ _ _ _ _ _)).eqTrans
    ((left_factorized _ _ _ _ _ _ _ _ _ (input_c _ _ _ _ _ _ _ _ h) (input_q _ _ _ _ _ _ _ _ h)
      (root_from_relation _ _ _ _ _ _ _ _ _ h hr hRel)).eqSymm.eqTrans
      ((relation_evaluation _ _ _ _ _ _ _ _ _ _ hRel).eqTrans
        ((right_factorized _ _ _ _ _ _ _ _ (input_j _ _ _ _ _ _ _ _ h) hr).eqTrans
          (GaussianRationalLinearProduct.linear_evaluation _ _ _ _ (right_length _ _ _ _ _ _ _)
            (right_canonical _ _ _ _ _ _ _)).eqSymm)))

theorem step_grid (C Q J T D E t x r : PTm n) (h : Γ ⊢[PRAAx] input C Q J T D E t x)
    (hr : Γ ⊢[PRAAx] lt r t) (hRel : Γ ⊢[PRAAx] relation C Q J T D E t x r) : Γ ⊢[PRAAx]
    gridEqual (GaussianRationalLinearProduct.linear (leftBuffer C Q T D E t x (succ r)) x (succ (width T D E t)))
      (GaussianRationalLinearProduct.linear (rightBuffer J T D E t x (succ r)) x (succ (width T D E t)))
      (succ (width T D E t)) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] input (Syn.shift C) (Syn.shift Q) (Syn.shift J) (Syn.shift T)
      (Syn.shift D) (Syn.shift E) (Syn.shift t) (Syn.shift x) := by
    simpa only [Fm.shift,subst_input,Syn.shift] using h.shift
  have hrs : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift r) (Syn.shift t) := by simpa only [Fm.shift,subst_lt,Syn.shift] using hr.shift
  have rs : Γ.map Fm.shift ⊢[PRAAx] relation (Syn.shift C) (Syn.shift Q) (Syn.shift J) (Syn.shift T)
      (Syn.shift D) (Syn.shift E) (Syn.shift t) (Syn.shift x) (Syn.shift r) := by
    simpa only [Fm.shift,subst_relation,Syn.shift] using hRel.shift
  refine .allI (.impI ?_)
  let Δ := le (var 0) (succ (width (Syn.shift T) (Syn.shift D) (Syn.shift E) (Syn.shift t))) :: Γ.map Fm.shift
  have eq := linear_evaluation_equal (Γ := Δ) (Syn.shift C) (Syn.shift Q) (Syn.shift J) (Syn.shift T)
    (Syn.shift D) (Syn.shift E) (Syn.shift t) (Syn.shift x) (Syn.shift r)
    (GaussianRationalFiniteGridIdentity.gridPoint (var 0)) hs.wk hrs.wk rs.wk
  simpa only [Δ,Syn.shift,GaussianRationalLinearProduct.subst_linear,subst_leftBuffer,subst_rightBuffer,
    subst_width,ConciseIPRA.PTm.subst_succ] using eq

theorem relation_step (C Q J T D E t x r : PTm n) (h : Γ ⊢[PRAAx] input C Q J T D E t x)
    (hr : Γ ⊢[PRAAx] lt r t) (hRel : Γ ⊢[PRAAx] relation C Q J T D E t x r) : Γ ⊢[PRAAx]
    relation C Q J T D E t x (succ r) := coefficients_relation _ _ _ _ _ _ _ _ _
      (GaussianRationalLinearCancellation.linear_grid_cancel _ _ _ _ (left_length _ _ _ _ _ _ _ _)
        (right_length _ _ _ _ _ _ _) (left_canonical _ _ _ _ _ _ _ _) (right_canonical _ _ _ _ _ _ _)
        (step_grid _ _ _ _ _ _ _ _ _ h hr hRel))

def stateLaw (C Q J T D E t x r : PTm n) : Fm PTm n := le r t ⟶ relation C Q J T D E t x r
def stateSyntax (C Q J T D E t x r : PTm n) : BFm n := .imp (.le r t)
  (.all (succ (width T D E t)) (.eq
    (entry (leftBuffer (Syn.shift C) (Syn.shift Q) (Syn.shift T) (Syn.shift D) (Syn.shift E)
      (Syn.shift t) (Syn.shift x) (Syn.shift r)) (var 0))
    (entry (rightBuffer (Syn.shift J) (Syn.shift T) (Syn.shift D) (Syn.shift E)
      (Syn.shift t) (Syn.shift x) (Syn.shift r)) (var 0))))
@[simp] theorem subst_stateLaw {l : ℕ} (σ : Fin n → PTm l) (C Q J T D E t x r : PTm n) :
    (stateLaw C Q J T D E t x r).subst σ = stateLaw (Syn.subst σ C) (Syn.subst σ Q) (Syn.subst σ J)
      (Syn.subst σ T) (Syn.subst σ D) (Syn.subst σ E) (Syn.subst σ t) (Syn.subst σ x) (Syn.subst σ r) := by simp [stateLaw]
theorem state_formula (C Q J T D E t x r : PTm n) : formula (stateSyntax C Q J T D E t x r) = stateLaw C Q J T D E t x r := by
  simp [stateSyntax,formula,stateLaw,relation,BFm.le,le,Syn.shift]

/-- The actual Boolean compiler makes the bounded coefficient relation a
genuine QF induction. No all-stage root or factor certificate is supplied. -/
theorem transfer_relation (C Q J T D E t x r : PTm n) (h : Γ ⊢[PRAAx] input C Q J T D E t x)
    (hr : Γ ⊢[PRAAx] le r t) : Γ ⊢[PRAAx] relation C Q J T D E t x r := by
  let A := stateSyntax (Syn.shift C) (Syn.shift Q) (Syn.shift J) (Syn.shift T) (Syn.shift D)
    (Syn.shift E) (Syn.shift t) (Syn.shift x) (var 0)
  have h0 : Γ ⊢[PRAAx] (formula A).subst (Syn.inst zero) := by
    simp only [A,state_formula,subst_stateLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
    exact .impI (base_relation _ _ _ _ _ _ _ _ h).wk
  have hs : formula A :: Γ.map Fm.shift ⊢[PRAAx] (formula A).subst (repl (succ (var 0))) := by
    simp only [A,state_formula,subst_stateLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
    refine .impI ?_
    let Δ := le (succ (var 0)) (Syn.shift t) :: stateLaw (Syn.shift C) (Syn.shift Q) (Syn.shift J)
      (Syn.shift T) (Syn.shift D) (Syn.shift E) (Syn.shift t) (Syn.shift x) (var 0) :: Γ.map Fm.shift
    have source : Γ.map Fm.shift ⊢[PRAAx] input (Syn.shift C) (Syn.shift Q) (Syn.shift J)
        (Syn.shift T) (Syn.shift D) (Syn.shift E) (Syn.shift t) (Syn.shift x) := by
      simpa only [Fm.shift,subst_input,Syn.shift] using h.shift
    have bound : Δ ⊢[PRAAx] lt (var 0) (Syn.shift t) := Prf.hyp0
    have past : Δ ⊢[PRAAx] stateLaw (Syn.shift C) (Syn.shift Q) (Syn.shift J)
        (Syn.shift T) (Syn.shift D) (Syn.shift E) (Syn.shift t) (Syn.shift x) (var 0) := Prf.hyp1
    exact relation_step _ _ _ _ _ _ _ _ _ source.wk.wk bound (.impE past (le_of_lt bound))
  have lawAt : Γ ⊢[PRAAx] stateLaw C Q J T D E t x r := by
    simpa only [A,state_formula,subst_stateLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      Foundations.BoundedSyntaxInduction.induction_at A r h0 hs
  exact .impE lawAt hr

theorem block_transfer (C Q J T D E t x r : PTm n) (h : Γ ⊢[PRAAx] input C Q J T D E t x)
    (hr : Γ ⊢[PRAAx] le r t) : Γ ⊢[PRAAx]
    coefficientsEqual (leftBuffer C Q T D E t x r) (rightBuffer J T D E t x r) (width T D E t) :=
  relation_coefficients _ _ _ _ _ _ _ _ _ (transfer_relation _ _ _ _ _ _ _ _ _ h hr)
theorem block_root (C Q J T D E t x r : PTm n) (h : Γ ⊢[PRAAx] input C Q J T D E t x)
    (hr : Γ ⊢[PRAAx] lt r t) : Γ ⊢[PRAAx] evaluate (block Q D x r) x ≐ qzero :=
  root_from_relation _ _ _ _ _ _ _ _ _ h hr (transfer_relation _ _ _ _ _ _ _ _ _ h (le_of_lt hr))
theorem terminal_evaluation (C Q J T D E t x z : PTm n) (h : Γ ⊢[PRAAx] input C Q J T D E t x) : Γ ⊢[PRAAx]
    qmul (evaluate C z) (evaluate (block Q D x t) z) ≐ evaluate J z :=
  (left_evaluation _ _ _ _ _ _ _ _ _ (input_c _ _ _ _ _ _ _ _ h) (input_q _ _ _ _ _ _ _ _ h)).eqSymm.eqTrans
    ((relation_evaluation _ _ _ _ _ _ _ _ _ _ (transfer_relation _ _ _ _ _ _ _ _ _ h (le_refl t))).eqTrans
      ((right_evaluation _ _ _ _ _ _ _ _ (input_j _ _ _ _ _ _ _ _ h)).eqTrans
        ((qmul_congr ((congrAp2 powerF (monus_self t) (.eqRefl _)).eqTrans (power_zero _)) (.eqRefl _)).eqTrans
          ((GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans
            (GaussianReciprocalHorner.qmul_one_right _ (GaussianRationalHorner.horner_canonical _ _ _))))))
theorem terminal_product_evaluation (C Q J T D E t x z : PTm n) (h : Γ ⊢[PRAAx] input C Q J T D E t x) : Γ ⊢[PRAAx]
    evaluate (product C (block Q D x t) T D) z ≐ evaluate J z :=
  (product_evaluation _ _ _ _ _ (input_c _ _ _ _ _ _ _ _ h)
    (block_length _ _ _ _ (input_q _ _ _ _ _ _ _ _ h))).eqTrans (terminal_evaluation _ _ _ _ _ _ _ _ _ h)

/-- The original numerical data return the SAME block, both actual padded
buffers, and the independently computed width and remaining depth. -/
def output (C Q J T D E t x r : PTm n) : PTm n := pairT (block Q D x r)
  (pairT (leftBuffer C Q T D E t x r) (pairT (rightBuffer J T D E t x r)
    (pairT (width T D E t) (remaining t r))))
def outputF : PR 9 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8))
def run (C Q J T D E t x r : PTm n) : PTm n := app outputF ![C,Q,J,T,D,E,t,x,r]
def fields (p : PTm n) (i : Fin 5) : PTm n := ![fstT p,fstT (sndT p),fstT (sndT (sndT p)),
  fstT (sndT (sndT (sndT p))),sndT (sndT (sndT (sndT p)))] i
@[simp] theorem subst_output {l : ℕ} (σ : Fin n → PTm l) (C Q J T D E t x r : PTm n) :
    Syn.subst σ (output C Q J T D E t x r) = output (Syn.subst σ C) (Syn.subst σ Q) (Syn.subst σ J)
      (Syn.subst σ T) (Syn.subst σ D) (Syn.subst σ E) (Syn.subst σ t) (Syn.subst σ x) (Syn.subst σ r) := by simp [output]
@[simp] theorem subst_run {l : ℕ} (σ : Fin n → PTm l) (C Q J T D E t x r : PTm n) :
    Syn.subst σ (run C Q J T D E t x r) = run (Syn.subst σ C) (Syn.subst σ Q) (Syn.subst σ J)
      (Syn.subst σ T) (Syn.subst σ D) (Syn.subst σ E) (Syn.subst σ t) (Syn.subst σ x) (Syn.subst σ r) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl
@[simp] theorem subst_fields {l : ℕ} (σ : Fin n → PTm l) (p : PTm n) (i : Fin 5) :
    Syn.subst σ (fields p i) = fields (Syn.subst σ p) i := by fin_cases i <;> simp [fields]
theorem program_at (C Q J T D E t x r : PTm n) : Γ ⊢[PRAAx] run C Q J T D E t x r ≐ output C Q J T D E t x r := by
  simpa [run,outputF] using toPR_eq (Γ := Γ)
    (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) : PTm 9) ![C,Q,J,T,D,E,t,x,r]
theorem returned_fields (C Q J T D E t x r : PTm n) (i : Fin 5) : Γ ⊢[PRAAx]
    fields (run C Q J T D E t x r) i ≐ ![block Q D x r,leftBuffer C Q T D E t x r,
      rightBuffer J T D E t x r,width T D E t,remaining t r] i := by
  have e0 := program_at (Γ := Γ) C Q J T D E t x r
  have e1 := (congrSnd e0).eqTrans (snd_pair _ _)
  have e2 := (congrSnd e1).eqTrans (snd_pair _ _)
  have e3 := (congrSnd e2).eqTrans (snd_pair _ _)
  fin_cases i
  · exact (congrFst e0).eqTrans (fst_pair _ _)
  · exact (congrFst e1).eqTrans (fst_pair _ _)
  · exact (congrFst e2).eqTrans (fst_pair _ _)
  · exact (congrFst e3).eqTrans (fst_pair _ _)
  · exact (congrSnd e3).eqTrans (snd_pair _ _)
theorem returned_transfer (C Q J T D E t x r : PTm n) (h : Γ ⊢[PRAAx] input C Q J T D E t x)
    (hr : Γ ⊢[PRAAx] le r t) : Γ ⊢[PRAAx]
    coefficientsEqual (fields (run C Q J T D E t x r) 1) (fields (run C Q J T D E t x r) 2) (width T D E t) :=
  coefficients_congr (returned_fields _ _ _ _ _ _ _ _ _ 1).eqSymm
    (returned_fields _ _ _ _ _ _ _ _ _ 2).eqSymm (block_transfer _ _ _ _ _ _ _ _ _ h hr)
theorem returned_root (C Q J T D E t x r : PTm n) (h : Γ ⊢[PRAAx] input C Q J T D E t x)
    (hr : Γ ⊢[PRAAx] lt r t) : Γ ⊢[PRAAx] evaluate (fields (run C Q J T D E t x r) 0) x ≐ qzero :=
  (GaussianRationalMonicReduction.evaluate_congr (returned_fields _ _ _ _ _ _ _ _ _ 0) (.eqRefl _)).eqTrans
    (block_root _ _ _ _ _ _ _ _ _ h hr)
theorem returned_left_length (C Q J T D E t x r : PTm n) : Γ ⊢[PRAAx]
    length (fields (run C Q J T D E t x r) 1) ≐ succ (width T D E t) :=
  (congrFst (returned_fields _ _ _ _ _ _ _ _ _ 1)).eqTrans (left_length _ _ _ _ _ _ _ _)
theorem returned_right_length (C Q J T D E t x r : PTm n) : Γ ⊢[PRAAx]
    length (fields (run C Q J T D E t x r) 2) ≐ succ (width T D E t) :=
  (congrFst (returned_fields _ _ _ _ _ _ _ _ _ 2)).eqTrans (right_length _ _ _ _ _ _ _)
theorem returned_terminal_evaluation (C Q J T D E t x z : PTm n) (h : Γ ⊢[PRAAx] input C Q J T D E t x) : Γ ⊢[PRAAx]
    qmul (evaluate C z) (evaluate (fields (run C Q J T D E t x t) 0) z) ≐ evaluate J z :=
  (qmul_congr (.eqRefl _) (GaussianRationalMonicReduction.evaluate_congr
    (returned_fields _ _ _ _ _ _ _ _ _ 0) (.eqRefl _))).eqTrans (terminal_evaluation _ _ _ _ _ _ _ _ _ h)

theorem original_base_buffers_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    ((length (baseLeft (var 0) (var 1) (var 3) (var 4) (var 5) (var 6)) ≐ succ (width (var 3) (var 4) (var 5) (var 6))) ⋏
      (length (baseRight (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)) ≐ succ (width (var 3) (var 4) (var 5) (var 6)))) :=
  closeUniv 8 (.andI (base_left_length _ _ _ _ _ _) (base_right_length _ _ _ _ _ _))
theorem actual_one_step_transfer_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ⟶ lt (var 8) (var 6) ⟶
      relation (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⟶
        relation (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (succ (var 8))) :=
  closeUniv 9 (.impI (.impI (.impI (relation_step _ _ _ _ _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))
theorem actual_block_transfer_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ⟶ le (var 8) (var 6) ⟶
      coefficientsEqual (leftBuffer (var 0) (var 1) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8))
        (rightBuffer (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8)) (width (var 3) (var 4) (var 5) (var 6))) :=
  closeUniv 9 (.impI (.impI (block_transfer _ _ _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_block_root_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ⟶ lt (var 8) (var 6) ⟶
      evaluate (block (var 1) (var 4) (var 7) (var 8)) (var 7) ≐ qzero) :=
  closeUniv 9 (.impI (.impI (block_root _ _ _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_terminal_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ⟶
      qmul (evaluate (var 0) (var 8)) (evaluate (block (var 1) (var 4) (var 7) (var 6)) (var 8)) ≐ evaluate (var 2) (var 8)) :=
  closeUniv 9 (.impI (terminal_evaluation _ _ _ _ _ _ _ _ _ Prf.hyp0))
theorem actual_terminal_product_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ⟶
      evaluate (product (var 0) (block (var 1) (var 4) (var 7) (var 6)) (var 3) (var 4)) (var 8) ≐ evaluate (var 2) (var 8)) :=
  closeUniv 9 (.impI (terminal_product_evaluation _ _ _ _ _ _ _ _ _ Prf.hyp0))
theorem actual_transfer_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ≐
      output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8)) := closeUniv 9 (program_at _ _ _ _ _ _ _ _ _)
theorem actual_returned_transfer_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ⟶ le (var 8) (var 6) ⟶
      coefficientsEqual (fields (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8)) 1)
        (fields (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8)) 2) (width (var 3) (var 4) (var 5) (var 6))) :=
  closeUniv 9 (.impI (.impI (returned_transfer _ _ _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_returned_root_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ⟶ lt (var 8) (var 6) ⟶
      evaluate (fields (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8)) 0) (var 7) ≐ qzero) :=
  closeUniv 9 (.impI (.impI (returned_root _ _ _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_returned_terminal_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ⟶
      qmul (evaluate (var 0) (var 8))
        (evaluate (fields (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 6)) 0) (var 8)) ≐ evaluate (var 2) (var 8)) :=
  closeUniv 9 (.impI (returned_terminal_evaluation _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianRationalBlockFactorTransfer
