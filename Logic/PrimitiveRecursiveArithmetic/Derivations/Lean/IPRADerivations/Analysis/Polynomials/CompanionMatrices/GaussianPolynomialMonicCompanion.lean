import IPRADerivations.Analysis.Polynomials.Products.GaussianRationalPolynomialProduct
import IPRADerivations.Analysis.Polynomials.RootFinding.Reconstruction.GaussianRationalMonicReduction
import IPRADerivations.Analysis.Polynomials.RootFinding.Reconstruction.GaussianRationalMonicReconstruction
import IPRADerivations.Core.CongruenceTactic

/-!
# A polynomial-valued monic companion step

Rows are descending coefficients in Y; each row is an actual descending
Gaussian-rational coefficient list in X. The numerical m,a,c are runtime
row count and X degree bounds. The program normalizes the used rows, shifts
the remainder by Y, and subtracts its top row times the lower monic rows.
Coefficient reconstruction is proved on the stored X coefficients, before
specialization at any X value. This is a Q(i)[X] dependency, not a determinant
or norm constructor.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianPolynomialMonicCompanion

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianRationalHorner
  (qzero qadd qmul canonical evaluate horner hornerF)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision
  (qone qadd_congr qmul_congr qsub_congr qzero_canonical qone_canonical
    canonicalCoefficients canonical_coefficient_at)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (qsub)
open LeanProofs.IPRA.Analysis.GaussianRationalCoefficientScaling
  (scaled scaled_length scaled_lookup scaled_entry_canonical evaluation_linearity)
open LeanProofs.IPRA.Analysis.GaussianRationalPolynomialBuffers
  (zeros zeros_length zeros_lookup zeros_evaluation leftPad pad_length pad_lookup
    pad_coefficient_before pad_coefficient_after pad_evaluation)
open LeanProofs.IPRA.Analysis.GaussianRationalPolynomialProduct
  (product product_length product_canonical product_evaluation)
open LeanProofs.IPRA.Analysis.GaussianCoefficientL1 (subCoefficients sub_lookup)
open LeanProofs.IPRA.Foundations.MasterCertificate
  (entry sequence sequence_length sequence_decode subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length entry_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ app)
open LeanProofs.IPRA.PTm (monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def normalizedRow (C : PTm n) : PTm n := scaled C qone
def rowShape (F m c : PTm n) : Fm PTm n :=
  .all (lt (var 0) (Syn.shift m) ⟶ length (entry (Syn.shift F) (var 0)) ≐ succ (Syn.shift c))
def nextRow (G m a r : PTm n) : PTm n :=
  RationalArithmetic.select (Signum.sg (monus m (succ r))) (zeros (succ a))
    (normalizedRow (entry G (succ r)))
def topRow (G : PTm n) : PTm n := normalizedRow (entry G zero)
def productRow (F G a c r : PTm n) : PTm n :=
  product (topRow G) (normalizedRow (entry F r)) a c
def shiftedRow (G m a c r : PTm n) : PTm n := leftPad (nextRow G m a r) c
def outputRow (F G m a c r : PTm n) : PTm n :=
  subCoefficients (shiftedRow G m a c r) (productRow F G a c r) (succ (a+c))
def rowF : PR 6 := PTm.toPR (outputRow (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
def data (F G m a c : PTm n) : PTm n := pairT F (pairT G (pairT m (pairT a c)))
def rowBody : PTm 2 := app rowF ![fstT (var 1),fstT (sndT (var 1)),
  fstT (sndT (sndT (var 1))),fstT (sndT (sndT (sndT (var 1)))),
  sndT (sndT (sndT (sndT (var 1)))),var 0]
def companion (F G m a c : PTm n) : PTm n := sequence rowBody m (data F G m a c)

@[simp] theorem subst_normalizedRow {l : ℕ} (σ : Fin n → PTm l) (C : PTm n) :
    Syn.subst σ (normalizedRow C) = normalizedRow (Syn.subst σ C) := by simp [normalizedRow]
@[simp] theorem subst_rowShape {l : ℕ} (σ : Fin n → PTm l) (F m c : PTm n) :
      (rowShape F m c).subst σ = rowShape (Syn.subst σ F) (Syn.subst σ m) (Syn.subst σ c) := by
  simp [rowShape,Syn.subst_shift,Syn.shift_subst]
@[simp] theorem subst_nextRow {l : ℕ} (σ : Fin n → PTm l) (G m a r : PTm n) :
    Syn.subst σ (nextRow G m a r) = nextRow (Syn.subst σ G) (Syn.subst σ m)
      (Syn.subst σ a) (Syn.subst σ r) := by simp [nextRow,Signum.sg]
@[simp] theorem subst_topRow {l : ℕ} (σ : Fin n → PTm l) (G : PTm n) :
    Syn.subst σ (topRow G) = topRow (Syn.subst σ G) := by simp [topRow]
@[simp] theorem subst_productRow {l : ℕ} (σ : Fin n → PTm l) (F G a c r : PTm n) :
    Syn.subst σ (productRow F G a c r) = productRow (Syn.subst σ F) (Syn.subst σ G)
      (Syn.subst σ a) (Syn.subst σ c) (Syn.subst σ r) := by simp [productRow]
@[simp] theorem subst_shiftedRow {l : ℕ} (σ : Fin n → PTm l) (G m a c r : PTm n) :
    Syn.subst σ (shiftedRow G m a c r) = shiftedRow (Syn.subst σ G) (Syn.subst σ m)
      (Syn.subst σ a) (Syn.subst σ c) (Syn.subst σ r) := by simp [shiftedRow]
@[simp] theorem subst_outputRow {l : ℕ} (σ : Fin n → PTm l) (F G m a c r : PTm n) :
    Syn.subst σ (outputRow F G m a c r) = outputRow (Syn.subst σ F) (Syn.subst σ G)
      (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ c) (Syn.subst σ r) := by simp [outputRow]
@[simp] theorem subst_data {l : ℕ} (σ : Fin n → PTm l) (F G m a c : PTm n) :
    Syn.subst σ (data F G m a c) = data (Syn.subst σ F) (Syn.subst σ G)
      (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ c) := by simp [data]
@[simp] theorem subst_companion {l : ℕ} (σ : Fin n → PTm l) (F G m a c : PTm n) :
    Syn.subst σ (companion F G m a c) = companion (Syn.subst σ F) (Syn.subst σ G)
      (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ c) := by simp [companion]

theorem row_shape_at (F m c r : PTm n) (hF : Γ ⊢[PRAAx] rowShape F m c)
    (hr : Γ ⊢[PRAAx] lt r m) : Γ ⊢[PRAAx] length (entry F r) ≐ succ c := by
  have h : Γ ⊢[PRAAx] lt r m ⟶ length (entry F r) ≐ succ c := by
    simpa [rowShape] using hF.allE r
  exact .impE h hr

theorem normalized_length (C : PTm n) : Γ ⊢[PRAAx] length (normalizedRow C) ≐ length C := scaled_length _ _
theorem normalized_canonical (C : PTm n) : Γ ⊢[PRAAx] canonicalCoefficients (normalizedRow C) := by
  refine .allI (.impI ?_)
  have h : lt (var 0) (length (Syn.shift (normalizedRow C))) :: Γ.map Fm.shift ⊢[PRAAx]
      lt (var 0) (length (Syn.shift C)) :=
    lt_congr (.eqRefl _) (normalized_length _) (by simpa only [Syn.shift,subst_normalizedRow] using Prf.hyp0)
  simpa only [Syn.shift,subst_normalizedRow,normalizedRow,GaussianRationalCoefficientScaling.subst_scaled,
    GaussianRationalSyntheticDivision.subst_qone] using scaled_entry_canonical (Syn.shift C) qone (var 0) h
theorem normalized_evaluation (C x : PTm n) : Γ ⊢[PRAAx]
    evaluate (normalizedRow C) x ≐ evaluate C x :=
  (evaluation_linearity _ _ _).eqTrans
    ((GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans
      (GaussianReciprocalHorner.qmul_one_right _ (GaussianRationalHorner.horner_canonical _ _ _)))

theorem next_inside (G m a r : PTm n) (hr : Γ ⊢[PRAAx] lt (succ r) m) : Γ ⊢[PRAAx]
    nextRow G m a r ≐ normalizedRow (entry G (succ r)) :=
  RationalArithmetic.select_one _ _ _ (AnalyticNumberTheory.Totatives.sg_lt hr)
theorem next_outside (G m a r : PTm n) (hr : Γ ⊢[PRAAx] le m (succ r)) : Γ ⊢[PRAAx]
    nextRow G m a r ≐ zeros (succ a) :=
  RationalArithmetic.select_zero _ _ _ (AnalyticNumberTheory.Totatives.sg_le hr)

theorem next_length (G m a r : PTm n) (hG : Γ ⊢[PRAAx] rowShape G m a) : Γ ⊢[PRAAx]
    length (nextRow G m a r) ≐ succ a := by
  refine .orE (lt_or_le (succ r) m) ?_ ?_
  · exact (congrFst (next_inside G m a r Prf.hyp0)).eqTrans
      ((normalized_length _).eqTrans (row_shape_at _ _ _ _ hG.wk Prf.hyp0))
  · exact (congrFst (next_outside G m a r Prf.hyp0)).eqTrans (zeros_length _)

theorem next_canonical (G m a r : PTm n) : Γ ⊢[PRAAx]
    canonicalCoefficients (nextRow G m a r) := by
  refine .orE (lt_or_le (succ r) m) ?_ ?_
  · exact GaussianRationalMonicReduction.canonical_coefficients_congr
      (next_inside G m a r Prf.hyp0) (normalized_canonical _)
  · exact GaussianRationalMonicReduction.canonical_coefficients_congr
      (next_outside G m a r Prf.hyp0) (GaussianRationalMonicReduction.zeros_canonical _)

theorem shifted_length (G m a c r : PTm n) (hG : Γ ⊢[PRAAx] rowShape G m a) : Γ ⊢[PRAAx]
    length (shiftedRow G m a c r) ≐ succ (a+c) :=
  (pad_length _ _).eqTrans ((congrAdd (.eqRefl _) (next_length G m a r hG)).eqTrans (by ipra_ring))

theorem pad_canonical (C t : PTm n) (hC : Γ ⊢[PRAAx] canonicalCoefficients C) : Γ ⊢[PRAAx]
    canonicalCoefficients (leftPad C t) := by
  refine .allI (.impI ?_)
  simp only [Syn.shift,GaussianRationalPolynomialBuffers.subst_leftPad]
  let Δ := lt (var 0) (length (leftPad (Syn.shift C) (Syn.shift t))) :: Γ.map Fm.shift
  have hi : Δ ⊢[PRAAx] lt (var 0) (Syn.shift t+length (Syn.shift C)) :=
    lt_congr (.eqRefl _) (pad_length _ _) Prf.hyp0
  have eq := pad_lookup (Γ := Δ) (Syn.shift C) (Syn.shift t) (var 0) hi
  refine .orE (lt_or_le (var 0) (Syn.shift t)) ?_ ?_
  · exact GaussianRationalHorner.canonical_congr (eq.wk.eqTrans (pad_coefficient_before _ _ _ Prf.hyp0)) qzero_canonical
  · have bound : (le (Syn.shift t) (var 0) :: Δ) ⊢[PRAAx]
        lt (monus (var 0) (Syn.shift t)) (length (Syn.shift C)) := by
      exact GaussianRationalMonicReconstruction.subtract_bound _ _ _ Prf.hyp0 hi.wk
    exact GaussianRationalHorner.canonical_congr
      (eq.wk.eqTrans (pad_coefficient_after _ _ _ Prf.hyp0))
      (canonical_coefficient_at _ _ (by
        have hc : Γ.map Fm.shift ⊢[PRAAx] canonicalCoefficients (Syn.shift C) := by
          simpa only [Fm.shift,GaussianRationalSyntheticDivision.subst_canonicalCoefficients,Syn.shift] using hC.shift
        exact hc.wk.wk) bound)

theorem shifted_canonical (G m a c r : PTm n) : Γ ⊢[PRAAx]
    canonicalCoefficients (shiftedRow G m a c r) := pad_canonical _ _ (next_canonical _ _ _ _)
theorem output_length (F G m a c r : PTm n) : Γ ⊢[PRAAx]
    length (outputRow F G m a c r) ≐ succ (a+c) := GaussianRationalMonicCompanion.sub_length _ _ _

theorem row_program (F G m a c r : PTm n) : Γ ⊢[PRAAx]
    app rowF ![F,G,m,a,c,r] ≐ outputRow F G m a c r := by
  simpa [rowF] using toPR_eq (Γ := Γ)
    (outputRow (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6) ![F,G,m,a,c,r]

theorem row_body_at (F G m a c r : PTm n) : Γ ⊢[PRAAx]
    inst2 rowBody r (data F G m a c) ≐ outputRow F G m a c r := by
  have e := snd_pair (Γ := Γ) F (pairT G (pairT m (pairT a c)))
  have f := (congrSnd e).eqTrans (snd_pair G (pairT m (pairT a c)))
  have g := (congrSnd f).eqTrans (snd_pair m (pairT a c))
  have h : Γ ⊢[PRAAx] inst2 rowBody r (data F G m a c) ≐ app rowF ![F,G,m,a,c,r] := by
    have body : inst2 rowBody r (data F G m a c) = app rowF
        ![fstT (data F G m a c),fstT (sndT (data F G m a c)),
          fstT (sndT (sndT (data F G m a c))),fstT (sndT (sndT (sndT (data F G m a c)))),
          sndT (sndT (sndT (sndT (data F G m a c)))),r] := by
      simp only [rowBody,inst2,ConciseIPRA.PTm.subst_app]
      congr 1
      funext j
      fin_cases j <;> simp only [Matrix.cons_val_succ',Matrix.cons_val_zero',Matrix.cons_val_succ,Matrix.cons_val_zero,Matrix.cons_val_one,
        subst_fstT,subst_sndT,Syn.subst_var]
    rw [body]
    apply congrApp rowF
    intro j
    fin_cases j
    all_goals simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
      Matrix.head_cons,Matrix.tail_cons,data]
    · exact fst_pair _ _
    · exact (congrFst e).eqTrans (fst_pair _ _)
    · exact (congrFst f).eqTrans (fst_pair _ _)
    · exact (congrFst g).eqTrans (fst_pair _ _)
    · exact (congrSnd g).eqTrans (snd_pair _ _)
    · exact .eqRefl _
  exact h.eqTrans (row_program _ _ _ _ _ _)

theorem companion_length (F G m a c : PTm n) : Γ ⊢[PRAAx]
    length (companion F G m a c) ≐ m := sequence_length _ _ _
theorem companion_lookup (F G m a c r : PTm n) (hr : Γ ⊢[PRAAx] lt r m) : Γ ⊢[PRAAx]
    entry (companion F G m a c) r ≐ outputRow F G m a c r :=
  (sequence_decode rowBody hr).eqTrans (row_body_at _ _ _ _ _ _)

theorem coefficient_reconstruction (F G m a c r s : PTm n)
    (hG : Γ ⊢[PRAAx] rowShape G m a) (hs : Γ ⊢[PRAAx] le s (a+c)) : Γ ⊢[PRAAx]
    qadd (entry (productRow F G a c r) s) (entry (outputRow F G m a c r) s) ≐
      entry (shiftedRow G m a c r) s := by
  have hr : Γ ⊢[PRAAx] lt s (length (shiftedRow G m a c r)) :=
    lt_congr (.eqRefl _) (shifted_length G m a c r hG).eqSymm
      ((succ_monus_succ _ _).eqTrans hs)
  exact (qadd_congr (.eqRefl _) (sub_lookup _ _ _ _ ((succ_monus_succ _ _).eqTrans hs))).eqTrans
    (GaussianRationalLinearProduct.add_sub_right _ _ (canonical_coefficient_at _ _ (shifted_canonical _ _ _ _ _) hr))

theorem difference_canonical (C E L : PTm n) : Γ ⊢[PRAAx]
    canonicalCoefficients (subCoefficients C E L) := by
  refine .allI (.impI ?_)
  have hi : lt (var 0) (length (Syn.shift (subCoefficients C E L))) :: Γ.map Fm.shift ⊢[PRAAx]
      lt (var 0) (Syn.shift L) :=
    lt_congr (.eqRefl _) (GaussianRationalMonicCompanion.sub_length _ _ _)
      (by simpa only [Syn.shift,GaussianCoefficientL1.subst_subCoefficients] using Prf.hyp0)
  simpa only [Syn.shift,GaussianCoefficientL1.subst_subCoefficients] using GaussianRationalHorner.canonical_congr
    (sub_lookup _ _ _ _ hi) (GaussianRationalMetric.qsub_canonical _ _)
theorem output_canonical (F G m a c r : PTm n) : Γ ⊢[PRAAx]
    canonicalCoefficients (outputRow F G m a c r) := difference_canonical _ _ _

theorem actual_row_length (F G m a c r : PTm n) (hr : Γ ⊢[PRAAx] lt r m) : Γ ⊢[PRAAx]
    length (entry (companion F G m a c) r) ≐ succ (a+c) :=
  (congrFst (companion_lookup _ _ _ _ _ _ hr)).eqTrans (output_length _ _ _ _ _ _)
theorem actual_row_canonical (F G m a c r : PTm n) (hr : Γ ⊢[PRAAx] lt r m) : Γ ⊢[PRAAx]
    canonicalCoefficients (entry (companion F G m a c) r) :=
  GaussianRationalMonicReduction.canonical_coefficients_congr
    (companion_lookup _ _ _ _ _ _ hr) (output_canonical _ _ _ _ _ _)
theorem actual_coefficient_reconstruction (F G m a c r s : PTm n)
    (hG : Γ ⊢[PRAAx] rowShape G m a) (hr : Γ ⊢[PRAAx] lt r m)
    (hs : Γ ⊢[PRAAx] le s (a+c)) : Γ ⊢[PRAAx]
    qadd (entry (productRow F G a c r) s) (entry (entry (companion F G m a c) r) s) ≐
      entry (shiftedRow G m a c r) s :=
  (qadd_congr (.eqRefl _) (entry_congr (companion_lookup _ _ _ _ _ _ hr) (.eqRefl _))).eqTrans
    (coefficient_reconstruction _ _ _ _ _ _ _ hG hs)

/-- The implicit monic Y coefficient acts on every actual top-row X
coefficient by one, with canonicality derived from normalization. -/
theorem leading_coefficient_reconstruction (G m a s : PTm n)
    (hm : Γ ⊢[PRAAx] le one m) (hG : Γ ⊢[PRAAx] rowShape G m a)
    (hs : Γ ⊢[PRAAx] le s a) : Γ ⊢[PRAAx]
    qmul qone (entry (topRow G) s) ≐ entry (topRow G) s := by
  have shape : Γ ⊢[PRAAx] length (topRow G) ≐ succ a :=
    (normalized_length _).eqTrans (row_shape_at _ _ _ _ hG hm)
  have hi : Γ ⊢[PRAAx] lt s (length (topRow G)) :=
    lt_congr (.eqRefl _) shape.eqSymm ((succ_monus_succ _ _).eqTrans hs)
  exact (GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans
    (GaussianReciprocalHorner.qmul_one_right _ (canonical_coefficient_at _ _ (normalized_canonical _) hi))

/-- The leading monic row is an actual X-polynomial buffer, and its
convolution product equals the padded top row coefficient by coefficient.
This is obtained from the finite-convolution constant kernel, not from
agreement of evaluator values. -/
def monicRow (c : PTm n) : PTm n := GaussianRationalMonicReduction.constant qone (succ c)
@[simp] theorem subst_monicRow {l : ℕ} (σ : Fin n → PTm l) (c : PTm n) :
    Syn.subst σ (monicRow c) = monicRow (Syn.subst σ c) := by simp [monicRow]
theorem monic_row_length (c : PTm n) : Γ ⊢[PRAAx] length (monicRow c) ≐ succ c :=
  GaussianRationalMonicReduction.constant_length _ _ (succ_monus_succ _ _ |>.eqTrans (zero_le _))

theorem monic_row_product (C a c s : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ a)
    (hCan : Γ ⊢[PRAAx] canonicalCoefficients C) (hs : Γ ⊢[PRAAx] le s (a+c)) : Γ ⊢[PRAAx]
    entry (product C (monicRow c) a c) s ≐ entry (leftPad C c) s := by
  have range : Γ ⊢[PRAAx] lt s (c+succ a) :=
    lt_congr (.eqRefl _) (by ipra_ring : Γ ⊢[PRAAx] succ (a+c) ≐ c+succ a)
      ((succ_monus_succ _ _).eqTrans hs)
  have actualRange : Γ ⊢[PRAAx] lt s (length (leftPad C c)) :=
    lt_congr (.eqRefl _) ((pad_length C c).eqTrans (congrAdd (.eqRefl _) hC)).eqSymm range
  exact (GaussianRationalPolynomialProduct.product_lookup C (monicRow c) a c s hs).eqTrans
    ((GaussianRationalMonicReconstruction.coefficient_constant C qone c (succ a) s).eqTrans
      ((GaussianRationalMonicReconstruction.offset_as_multiply C qone (succ a) c s).eqTrans
        ((qmul_congr (.eqRefl _) (GaussianRationalMonicReconstruction.shifted_pad_entry C (succ a) c s hC range)).eqTrans
          ((GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans
            (GaussianReciprocalHorner.qmul_one_right _
              (canonical_coefficient_at _ _ (pad_canonical C c hCan) actualRange))))))

theorem leading_polynomial_reconstruction (G m a c s : PTm n)
    (hm : Γ ⊢[PRAAx] le one m) (hG : Γ ⊢[PRAAx] rowShape G m a)
    (hs : Γ ⊢[PRAAx] le s (a+c)) : Γ ⊢[PRAAx]
    entry (product (topRow G) (monicRow c) a c) s ≐ entry (leftPad (topRow G) c) s :=
  monic_row_product _ _ _ _ ((normalized_length _).eqTrans (row_shape_at _ _ _ _ hG hm))
    (normalized_canonical _) hs

theorem evaluation_congr {C D x y : PTm n} (hC : Γ ⊢[PRAAx] C ≐ D)
    (hx : Γ ⊢[PRAAx] x ≐ y) : Γ ⊢[PRAAx] evaluate C x ≐ evaluate D y :=
  congrAp3 hornerF (congrFst hC) hC hx

theorem output_evaluation (F G m a c r x : PTm n)
    (hm : Γ ⊢[PRAAx] le one m) (hF : Γ ⊢[PRAAx] rowShape F m c)
    (hG : Γ ⊢[PRAAx] rowShape G m a) (hr : Γ ⊢[PRAAx] lt r m) : Γ ⊢[PRAAx]
    evaluate (outputRow F G m a c r) x ≐
      qsub (evaluate (nextRow G m a r) x)
        (qmul (evaluate (entry G zero) x) (evaluate (entry F r) x)) := by
  have htop : Γ ⊢[PRAAx] length (topRow G) ≐ succ a :=
    (normalized_length _).eqTrans (row_shape_at _ _ _ _ hG hm)
  have hrow : Γ ⊢[PRAAx] length (normalizedRow (entry F r)) ≐ succ c :=
    (normalized_length _).eqTrans (row_shape_at _ _ _ _ hF hr)
  exact (GaussianRationalMonicCompanion.difference_evaluation _ _ _ _
      (shifted_length _ _ _ _ _ hG) (product_length _ _ _ _)).eqTrans
    (qsub_congr (pad_evaluation _ _ _)
      ((product_evaluation _ _ _ _ _ htop hrow).eqTrans
        (qmul_congr (normalized_evaluation _ _) (normalized_evaluation _ _))))

/-! Specialization constructs actual scalar coefficient lists. No equation
between arbitrary outer list codes is inferred from entrywise equality. -/
def valuesBody : PTm 2 := evaluate (entry (fstT (var 1)) (var 0)) (sndT (var 1))
def values (F m x : PTm n) : PTm n := sequence valuesBody m (pairT F x)
def monicCoefficient (F x i : PTm n) : PTm n :=
  RationalArithmetic.select (Signum.sg i) qone (evaluate (entry F (pred i)) x)
def monicBody : PTm 2 := monicCoefficient (fstT (var 1)) (sndT (var 1)) (var 0)
def monicValues (F m x : PTm n) : PTm n := sequence monicBody (succ m) (pairT F x)

@[simp] theorem subst_values {l : ℕ} (σ : Fin n → PTm l) (F m x : PTm n) :
    Syn.subst σ (values F m x) = values (Syn.subst σ F) (Syn.subst σ m) (Syn.subst σ x) := by simp [values]
@[simp] theorem subst_monicCoefficient {l : ℕ} (σ : Fin n → PTm l) (F x i : PTm n) :
    Syn.subst σ (monicCoefficient F x i) = monicCoefficient (Syn.subst σ F) (Syn.subst σ x)
      (Syn.subst σ i) := by simp [monicCoefficient,Signum.sg]
@[simp] theorem subst_monicValues {l : ℕ} (σ : Fin n → PTm l) (F m x : PTm n) :
    Syn.subst σ (monicValues F m x) = monicValues (Syn.subst σ F) (Syn.subst σ m) (Syn.subst σ x) := by simp [monicValues]

theorem values_body_at (F x r : PTm n) : Γ ⊢[PRAAx]
    inst2 valuesBody r (pairT F x) ≐ evaluate (entry F r) x := by
  simp only [valuesBody,inst2,GaussianRationalHorner.subst_evaluate,subst_entry,subst_fstT,subst_sndT,
    Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact evaluation_congr (entry_congr (fst_pair _ _) (.eqRefl _)) (snd_pair _ _)
theorem values_length (F m x : PTm n) : Γ ⊢[PRAAx] length (values F m x) ≐ m := sequence_length _ _ _
theorem values_lookup (F m x r : PTm n) (hr : Γ ⊢[PRAAx] lt r m) : Γ ⊢[PRAAx]
    entry (values F m x) r ≐ evaluate (entry F r) x :=
  (sequence_decode valuesBody hr).eqTrans (values_body_at _ _ _)

theorem monic_body_at (F x i : PTm n) : Γ ⊢[PRAAx]
    inst2 monicBody i (pairT F x) ≐ monicCoefficient F x i := by
  simp only [monicBody,inst2,subst_monicCoefficient,subst_fstT,subst_sndT,
    Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact GaussianRationalMonicReconstruction.select_congr (.eqRefl _) (.eqRefl _)
    (evaluation_congr (entry_congr (fst_pair F x) (.eqRefl (pred i))) (snd_pair F x))
theorem monic_length (F m x : PTm n) : Γ ⊢[PRAAx] length (monicValues F m x) ≐ succ m := sequence_length _ _ _
theorem monic_head (F m x : PTm n) : Γ ⊢[PRAAx] entry (monicValues F m x) zero ≐ qone :=
  (sequence_decode monicBody (zero_lt_succ m)).eqTrans
    ((monic_body_at _ _ _).eqTrans (RationalArithmetic.select_zero _ _ _ Signum.sg_zero))
theorem monic_tail (F m x r : PTm n) (hr : Γ ⊢[PRAAx] lt r m) : Γ ⊢[PRAAx]
    entry (monicValues F m x) (succ r) ≐ evaluate (entry F r) x :=
  (sequence_decode monicBody ((succ_monus_succ _ _).eqTrans hr)).eqTrans
    ((monic_body_at _ _ _).eqTrans ((RationalArithmetic.select_one _ _ _ (Signum.sg_succ r)).eqTrans
      (evaluation_congr (entry_congr (.eqRefl _) (pred_succ r)) (.eqRefl _))))

theorem next_specialization (G m a r x : PTm n) : Γ ⊢[PRAAx]
    evaluate (nextRow G m a r) x ≐ GaussianRationalLinearProduct.padded (values G m x) m (succ r) := by
  refine .orE (lt_or_le (succ r) m) ?_ ?_
  · exact (evaluation_congr (next_inside _ _ _ _ Prf.hyp0) (.eqRefl _)).eqTrans
      ((normalized_evaluation _ _).eqTrans
        ((values_lookup _ _ _ _ Prf.hyp0).eqSymm.eqTrans
          (GaussianRationalLinearProduct.padded_inside _ _ _ Prf.hyp0).eqSymm))
  · exact (evaluation_congr (next_outside _ _ _ _ Prf.hyp0) (.eqRefl _)).eqTrans
      ((zeros_evaluation _ _).eqTrans (GaussianRationalLinearProduct.padded_outside _ _ _ Prf.hyp0).eqSymm)

theorem specialized_entry (F G m a c r x : PTm n)
    (hm : Γ ⊢[PRAAx] le one m) (hF : Γ ⊢[PRAAx] rowShape F m c)
    (hG : Γ ⊢[PRAAx] rowShape G m a) (hr : Γ ⊢[PRAAx] lt r m) : Γ ⊢[PRAAx]
    entry (values (companion F G m a c) m x) r ≐
      entry (GaussianRationalMonicCompanion.companionY (monicValues F m x) (values G m x) m) r := by
  exact (values_lookup _ _ _ _ hr).eqTrans
    ((evaluation_congr (companion_lookup _ _ _ _ _ _ hr) (.eqRefl _)).eqTrans
      ((output_evaluation _ _ _ _ _ _ _ hm hF hG hr).eqTrans
        ((qsub_congr (next_specialization _ _ _ _ _)
          (qmul_congr (values_lookup _ _ _ _ hm).eqSymm (monic_tail _ _ _ _ hr).eqSymm)).eqTrans
            (GaussianRationalMonicCompanion.companion_lookup _ _ _ _
              (monic_length _ _ _) (values_length _ _ _) hr).eqSymm)))

theorem specialization (F G m a c x y : PTm n)
    (hm : Γ ⊢[PRAAx] le one m) (hF : Γ ⊢[PRAAx] rowShape F m c)
    (hG : Γ ⊢[PRAAx] rowShape G m a) : Γ ⊢[PRAAx]
    evaluate (values (companion F G m a c) m x) y ≐
      evaluate (GaussianRationalMonicCompanion.companionY (monicValues F m x) (values G m x) m) y := by
  have entries : Γ ⊢[PRAAx] .all (lt (var 0) (Syn.shift m) ⟶
      entry (Syn.shift (values (companion F G m a c) m x)) (var 0) ≐
        entry (Syn.shift (GaussianRationalMonicCompanion.companionY (monicValues F m x) (values G m x) m)) (var 0)) := by
    refine .allI (.impI ?_)
    have f : Γ.map Fm.shift ⊢[PRAAx] rowShape (Syn.shift F) (Syn.shift m) (Syn.shift c) := by
      simpa only [Fm.shift,subst_rowShape,Syn.shift] using hF.shift
    have g : Γ.map Fm.shift ⊢[PRAAx] rowShape (Syn.shift G) (Syn.shift m) (Syn.shift a) := by
      simpa only [Fm.shift,subst_rowShape,Syn.shift] using hG.shift
    have bound : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift m) := by
      simpa only [Fm.shift,subst_le,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift] using hm.shift
    simpa only [Syn.shift,subst_values,subst_companion,GaussianRationalMonicCompanion.subst_companionY,subst_monicValues] using
      specialized_entry (Syn.shift F) (Syn.shift G) (Syn.shift m) (Syn.shift a) (Syn.shift c) (var 0) (Syn.shift x)
        bound.wk f.wk g.wk Prf.hyp0
  exact (congrAp3 hornerF (values_length _ _ _) (.eqRefl _) (.eqRefl _)).eqTrans
    ((GaussianRationalLinearProduct.horner_ext _ _ _ _ _ entries (le_refl _)).eqTrans
      (congrAp3 hornerF (GaussianRationalMonicCompanion.companion_length _ _ _).eqSymm (.eqRefl _) (.eqRefl _)))

theorem companion_evaluation (F G m a c x y : PTm n)
    (hm : Γ ⊢[PRAAx] le one m) (hF : Γ ⊢[PRAAx] rowShape F m c)
    (hG : Γ ⊢[PRAAx] rowShape G m a) : Γ ⊢[PRAAx]
    qmul y (evaluate (values G m x) y) ≐
      qadd (qmul (evaluate (monicValues F m x) y) (evaluate (entry G zero) x))
        (evaluate (values (companion F G m a c) m x) y) :=
  (GaussianRationalMonicCompanion.companion_evaluation _ _ _ _ hm
    (monic_length _ _ _) (monic_head _ _ _) (values_length _ _ _)).eqTrans
      (qadd_congr (qmul_congr (.eqRefl _) (values_lookup _ _ _ _ hm))
        (specialization _ _ _ _ _ _ _ hm hF hG).eqSymm)

theorem curve_step (F G m a c x y : PTm n)
    (hm : Γ ⊢[PRAAx] le one m) (hF : Γ ⊢[PRAAx] rowShape F m c)
    (hG : Γ ⊢[PRAAx] rowShape G m a)
    (hCurve : Γ ⊢[PRAAx] evaluate (monicValues F m x) y ≐ qzero) : Γ ⊢[PRAAx]
    qmul y (evaluate (values G m x) y) ≐ evaluate (values (companion F G m a c) m x) y :=
  (companion_evaluation _ _ _ _ _ _ _ hm hF hG).eqTrans
    ((qadd_congr ((qmul_congr hCurve (.eqRefl _)).eqTrans
      (GaussianRationalSyntheticDivision.qmul_zero_left _)) (.eqRefl _)).eqTrans
        (GaussianRationalSyntheticDivision.qzero_add _ (GaussianRationalHorner.horner_canonical _ _ _)))

/-! The actual PR5 returns the polynomial-valued rows. All observations
below use that same program; the Y degree and both X bounds remain numeric. -/
def companionF : PR 5 := PTm.toPR (companion (var 0) (var 1) (var 2) (var 3) (var 4))
def run (F G m a c : PTm n) : PTm n := app companionF ![F,G,m,a,c]
@[simp] theorem subst_run {l : ℕ} (σ : Fin n → PTm l) (F G m a c : PTm n) :
    Syn.subst σ (run F G m a c) = run (Syn.subst σ F) (Syn.subst σ G)
      (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ c) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext j
  fin_cases j <;> rfl
theorem program_at (F G m a c : PTm n) : Γ ⊢[PRAAx] run F G m a c ≐ companion F G m a c := by
  simpa only [run,companionF,subst_companion,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons] using
      toPR_eq (Γ := Γ) (companion (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![F,G,m,a,c]
theorem returned_length (F G m a c : PTm n) : Γ ⊢[PRAAx] length (run F G m a c) ≐ m :=
  (congrFst (program_at _ _ _ _ _)).eqTrans (companion_length _ _ _ _ _)
theorem returned_row (F G m a c r : PTm n) (hr : Γ ⊢[PRAAx] lt r m) : Γ ⊢[PRAAx]
    entry (run F G m a c) r ≐ outputRow F G m a c r :=
  (entry_congr (program_at _ _ _ _ _) (.eqRefl _)).eqTrans (companion_lookup _ _ _ _ _ _ hr)
theorem returned_row_length (F G m a c r : PTm n) (hr : Γ ⊢[PRAAx] lt r m) : Γ ⊢[PRAAx]
    length (entry (run F G m a c) r) ≐ succ (a+c) :=
  (congrFst (returned_row _ _ _ _ _ _ hr)).eqTrans (output_length _ _ _ _ _ _)
theorem returned_row_canonical (F G m a c r : PTm n) (hr : Γ ⊢[PRAAx] lt r m) : Γ ⊢[PRAAx]
    canonicalCoefficients (entry (run F G m a c) r) :=
  GaussianRationalMonicReduction.canonical_coefficients_congr
    (returned_row _ _ _ _ _ _ hr) (output_canonical _ _ _ _ _ _)
theorem returned_coefficient_reconstruction (F G m a c r s : PTm n)
    (hG : Γ ⊢[PRAAx] rowShape G m a) (hr : Γ ⊢[PRAAx] lt r m)
    (hs : Γ ⊢[PRAAx] le s (a+c)) : Γ ⊢[PRAAx]
    qadd (entry (productRow F G a c r) s) (entry (entry (run F G m a c) r) s) ≐
      entry (shiftedRow G m a c r) s :=
  (qadd_congr (.eqRefl _) (entry_congr (returned_row _ _ _ _ _ _ hr) (.eqRefl _))).eqTrans
    (coefficient_reconstruction _ _ _ _ _ _ _ hG hs)

theorem values_congr {F G m l x y : PTm n} (hF : Γ ⊢[PRAAx] F ≐ G)
    (hm : Γ ⊢[PRAAx] m ≐ l) (hx : Γ ⊢[PRAAx] x ≐ y) : Γ ⊢[PRAAx]
    values F m x ≐ values G l y := by
  ipra_congr (values (var 0) (var 1) (var 2) : PTm 3) with [hF, hm, hx]
theorem returned_evaluation (F G m a c x y : PTm n)
    (hm : Γ ⊢[PRAAx] le one m) (hF : Γ ⊢[PRAAx] rowShape F m c)
    (hG : Γ ⊢[PRAAx] rowShape G m a) : Γ ⊢[PRAAx]
    qmul y (evaluate (values G m x) y) ≐
      qadd (qmul (evaluate (monicValues F m x) y) (evaluate (entry G zero) x))
        (evaluate (values (run F G m a c) m x) y) :=
  (companion_evaluation _ _ _ _ _ _ _ hm hF hG).eqTrans
    (qadd_congr (.eqRefl _) (evaluation_congr (values_congr (program_at _ _ _ _ _).eqSymm (.eqRefl _) (.eqRefl _)) (.eqRefl _)))

theorem actual_polynomial_companion_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((run (var 0) (var 1) (var 2) (var 3) (var 4) ≐ companion (var 0) (var 1) (var 2) (var 3) (var 4)) ⋏
      length (run (var 0) (var 1) (var 2) (var 3) (var 4)) ≐ var 2) :=
  closeUniv 5 (.andI (program_at _ _ _ _ _) (returned_length _ _ _ _ _))
theorem actual_polynomial_companion_row_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (lt (var 5) (var 2) ⟶
      ((length (entry (run (var 0) (var 1) (var 2) (var 3) (var 4)) (var 5)) ≐ succ (var 3+var 4)) ⋏
        canonicalCoefficients (entry (run (var 0) (var 1) (var 2) (var 3) (var 4)) (var 5)))) :=
  closeUniv 6 (.impI (.andI (returned_row_length _ _ _ _ _ _ Prf.hyp0) (returned_row_canonical _ _ _ _ _ _ Prf.hyp0)))
theorem actual_polynomial_companion_coefficient_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (rowShape (var 1) (var 2) (var 3) ⟶ lt (var 5) (var 2) ⟶ le (var 6) (var 3+var 4) ⟶
      qadd (entry (productRow (var 0) (var 1) (var 3) (var 4) (var 5)) (var 6))
        (entry (entry (run (var 0) (var 1) (var 2) (var 3) (var 4)) (var 5)) (var 6)) ≐
          entry (shiftedRow (var 1) (var 2) (var 3) (var 4) (var 5)) (var 6)) :=
  closeUniv 7 (.impI (.impI (.impI (returned_coefficient_reconstruction _ _ _ _ _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))
theorem actual_monic_polynomial_row_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 1) ⟶ rowShape (var 0) (var 1) (var 2) ⟶ le (var 4) (var 2+var 3) ⟶
      entry (product (topRow (var 0)) (monicRow (var 3)) (var 2) (var 3)) (var 4) ≐
        entry (leftPad (topRow (var 0)) (var 3)) (var 4)) :=
  closeUniv 5 (.impI (.impI (.impI (leading_polynomial_reconstruction _ _ _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))
theorem actual_polynomial_companion_specialization_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (le one (var 2) ⟶ rowShape (var 0) (var 2) (var 4) ⟶ rowShape (var 1) (var 2) (var 3) ⟶
      evaluate (values (companion (var 0) (var 1) (var 2) (var 3) (var 4)) (var 2) (var 5)) (var 6) ≐
        evaluate (GaussianRationalMonicCompanion.companionY (monicValues (var 0) (var 2) (var 5))
          (values (var 1) (var 2) (var 5)) (var 2)) (var 6)) :=
  closeUniv 7 (.impI (.impI (.impI (specialization _ _ _ _ _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))
theorem actual_polynomial_companion_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (le one (var 2) ⟶ rowShape (var 0) (var 2) (var 4) ⟶ rowShape (var 1) (var 2) (var 3) ⟶
      qmul (var 6) (evaluate (values (var 1) (var 2) (var 5)) (var 6)) ≐
        qadd (qmul (evaluate (monicValues (var 0) (var 2) (var 5)) (var 6)) (evaluate (entry (var 1) zero) (var 5)))
          (evaluate (values (run (var 0) (var 1) (var 2) (var 3) (var 4)) (var 2) (var 5)) (var 6))) :=
  closeUniv 7 (.impI (.impI (.impI (returned_evaluation _ _ _ _ _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))
theorem actual_polynomial_companion_curve_step_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (le one (var 2) ⟶ rowShape (var 0) (var 2) (var 4) ⟶ rowShape (var 1) (var 2) (var 3) ⟶
      evaluate (monicValues (var 0) (var 2) (var 5)) (var 6) ≐ qzero ⟶
        qmul (var 6) (evaluate (values (var 1) (var 2) (var 5)) (var 6)) ≐
          evaluate (values (companion (var 0) (var 1) (var 2) (var 3) (var 4)) (var 2) (var 5)) (var 6)) :=
  closeUniv 7 (.impI (.impI (.impI (.impI (curve_step _ _ _ _ _ _ _ hyp2.wk hyp2 Prf.hyp1 Prf.hyp0)))))

end LeanProofs.IPRA.Analysis.GaussianPolynomialMonicCompanion
