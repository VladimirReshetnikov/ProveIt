import IPRADerivations.Analysis.GaussianSuperellipticMatrixEntries
import IPRADerivations.Analysis.GaussianRationalGridCoefficientEquality

/-!
# Actual polynomial buffers for the superelliptic matrix entries

The original inverse index selects the original descending A row. The
tightly stored buffer is its actual normalization, or its actual product
with f, according to the real wrap case. Original numerical index bounds
derive that its width fits the original matrix store. Padding then gives
two canonical buffers of the SAME width. Their proved evaluations on the
actual finite grid derive literal bounded coefficient equality.

No original coefficient canonicality, nonzero head, exact degree,
coprimality, supplied evaluator or desired coefficient identity is assumed.
The local store bound is a or a+c, not a claim about the actual degree.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianSuperellipticMatrixCoefficients

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.PTm (monus pred)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (evaluate qmul)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision (canonicalCoefficients qmul_congr)
open LeanProofs.IPRA.Analysis.GaussianPolynomialMonicCompanion
  (rowShape normalizedRow normalized_length normalized_canonical normalized_evaluation row_shape_at pad_canonical)
open LeanProofs.IPRA.Analysis.GaussianPolynomialMultiplicationMatrix (slot width)
open LeanProofs.IPRA.Analysis.GaussianSuperellipticMatrixEntries (A input entryPolynomial)
open LeanProofs.IPRA.Analysis.GaussianRationalPolynomialBuffers (leftPad pad_length pad_evaluation)
open LeanProofs.IPRA.Analysis.GaussianRationalPolynomialProduct (product product_length product_canonical product_evaluation)
open LeanProofs.IPRA.Analysis.GaussianRationalMonicReduction (evaluate_congr canonical_coefficients_congr)
open LeanProofs.IPRA.Foundations.RuntimeCyclicPermutation (inverseIndex wrap)
open LeanProofs.IPRA.Foundations.GuardedTotalization (sel sel_one sel_zero)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ app)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def APolynomial (G m r j : PTm n) : PTm n := normalizedRow (entry G (slot m (inverseIndex m j r)))
def wrapped (f G m a c r j : PTm n) : PTm n := product (APolynomial G m r j) (normalizedRow f) a c
def localBound (a c r j : PTm n) : PTm n := sel (Signum.sg (monus j r)) (a+c) a
def localPolynomial (f G m a c r j : PTm n) : PTm n :=
  sel (Signum.sg (monus j r)) (wrapped f G m a c r j) (APolynomial G m r j)
def witness (f G m a c r j : PTm n) : PTm n :=
  leftPad (localPolynomial f G m a c r j) (monus (width m a c) (localBound a c r j))

@[simp] theorem subst_APolynomial {l : ℕ} (σ : Fin n → PTm l) (G m r j : PTm n) :
    Syn.subst σ (APolynomial G m r j) = APolynomial (Syn.subst σ G) (Syn.subst σ m) (Syn.subst σ r) (Syn.subst σ j) := by simp [APolynomial]
@[simp] theorem subst_wrapped {l : ℕ} (σ : Fin n → PTm l) (f G m a c r j : PTm n) :
    Syn.subst σ (wrapped f G m a c r j) = wrapped (Syn.subst σ f) (Syn.subst σ G) (Syn.subst σ m)
      (Syn.subst σ a) (Syn.subst σ c) (Syn.subst σ r) (Syn.subst σ j) := by simp [wrapped]
@[simp] theorem subst_localBound {l : ℕ} (σ : Fin n → PTm l) (a c r j : PTm n) :
    Syn.subst σ (localBound a c r j) = localBound (Syn.subst σ a) (Syn.subst σ c) (Syn.subst σ r) (Syn.subst σ j) := by simp [localBound,sel]
@[simp] theorem subst_localPolynomial {l : ℕ} (σ : Fin n → PTm l) (f G m a c r j : PTm n) :
    Syn.subst σ (localPolynomial f G m a c r j) = localPolynomial (Syn.subst σ f) (Syn.subst σ G) (Syn.subst σ m)
      (Syn.subst σ a) (Syn.subst σ c) (Syn.subst σ r) (Syn.subst σ j) := by simp [localPolynomial,sel]
@[simp] theorem subst_witness {l : ℕ} (σ : Fin n → PTm l) (f G m a c r j : PTm n) :
    Syn.subst σ (witness f G m a c r j) = witness (Syn.subst σ f) (Syn.subst σ G) (Syn.subst σ m)
      (Syn.subst σ a) (Syn.subst σ c) (Syn.subst σ r) (Syn.subst σ j) := by simp [witness]

theorem unwrapped_bound_value (a c r j : PTm n) (h : Γ ⊢[PRAAx] le j r) : Γ ⊢[PRAAx]
    localBound a c r j ≐ a := sel_zero (Foundations.BoundedFormulas.sg_of_zero h)
theorem wrapped_bound_value (a c r j : PTm n) (h : Γ ⊢[PRAAx] lt r j) : Γ ⊢[PRAAx]
    localBound a c r j ≐ a+c := sel_one (AnalyticNumberTheory.Totatives.sg_lt h)
theorem unwrapped_value (f G m a c r j : PTm n) (h : Γ ⊢[PRAAx] le j r) : Γ ⊢[PRAAx]
    localPolynomial f G m a c r j ≐ APolynomial G m r j := sel_zero (Foundations.BoundedFormulas.sg_of_zero h)
theorem wrapped_value (f G m a c r j : PTm n) (h : Γ ⊢[PRAAx] lt r j) : Γ ⊢[PRAAx]
    localPolynomial f G m a c r j ≐ wrapped f G m a c r j := sel_one (AnalyticNumberTheory.Totatives.sg_lt h)

theorem A_length (G m a r j : PTm n) (hG : Γ ⊢[PRAAx] rowShape G m a)
    (hr : Γ ⊢[PRAAx] lt r m) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    length (APolynomial G m r j) ≐ succ a :=
  (normalized_length _).eqTrans (row_shape_at _ _ _ _ hG
    (GaussianPolynomialMultiplicationMatrix.slot_range _ _
      (.andE₁ (Foundations.RuntimeCyclicPermutation.inverse_correct _ _ _ hj hr))))
theorem A_canonical (G m r j : PTm n) : Γ ⊢[PRAAx] canonicalCoefficients (APolynomial G m r j) := normalized_canonical _
theorem A_evaluation (G m r j x : PTm n) : Γ ⊢[PRAAx]
    evaluate (APolynomial G m r j) x ≐ A G m (inverseIndex m j r) x := normalized_evaluation _ _
theorem wrapped_length (f G m a c r j : PTm n) : Γ ⊢[PRAAx]
    length (wrapped f G m a c r j) ≐ succ (a+c) := product_length _ _ _ _
theorem wrapped_canonical (f G m a c r j : PTm n) : Γ ⊢[PRAAx]
    canonicalCoefficients (wrapped f G m a c r j) := product_canonical _ _ _ _
theorem wrapped_evaluation (f G m a c r j x : PTm n)
    (hf : Γ ⊢[PRAAx] length f ≐ succ c) (hG : Γ ⊢[PRAAx] rowShape G m a)
    (hr : Γ ⊢[PRAAx] lt r m) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    evaluate (wrapped f G m a c r j) x ≐ qmul (A G m (inverseIndex m j r) x) (evaluate f x) :=
  (product_evaluation _ _ _ _ _ (A_length _ _ _ _ _ hG hr hj) ((normalized_length _).eqTrans hf)).eqTrans
    (qmul_congr (A_evaluation _ _ _ _ _) (normalized_evaluation _ _))

theorem local_length (f G m a c r j : PTm n) (hG : Γ ⊢[PRAAx] rowShape G m a)
    (hr : Γ ⊢[PRAAx] lt r m) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    length (localPolynomial f G m a c r j) ≐ succ (localBound a c r j) := by
  refine .orE (lt_or_le r j) ?_ ?_
  · exact (congrFst (wrapped_value _ _ _ _ _ _ _ Prf.hyp0)).eqTrans
      ((wrapped_length _ _ _ _ _ _ _).eqTrans (congrSucc (wrapped_bound_value _ _ _ _ Prf.hyp0)).eqSymm)
  · exact (congrFst (unwrapped_value _ _ _ _ _ _ _ Prf.hyp0)).eqTrans
      ((A_length _ _ _ _ _ hG.wk hr.wk hj.wk).eqTrans (congrSucc (unwrapped_bound_value _ _ _ _ Prf.hyp0)).eqSymm)
theorem local_canonical (f G m a c r j : PTm n) : Γ ⊢[PRAAx]
    canonicalCoefficients (localPolynomial f G m a c r j) := by
  refine .orE (lt_or_le r j) ?_ ?_
  · exact canonical_coefficients_congr (wrapped_value _ _ _ _ _ _ _ Prf.hyp0) (wrapped_canonical _ _ _ _ _ _ _)
  · exact canonical_coefficients_congr (unwrapped_value _ _ _ _ _ _ _ Prf.hyp0) (A_canonical _ _ _ _)

theorem unwrapped_store_bound (m a c : PTm n) : Γ ⊢[PRAAx] le a (width m a c) := le_add_right _ _
/-- A wrap itself gives 1<=j<=pred m, so the a+c store really fits.
No extra m>=2 or positive c premise is added. -/
theorem wrapped_store_bound (m a c r j : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hrj : Γ ⊢[PRAAx] lt r j) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx] le (a+c) (width m a c) := by
  have hp : Γ ⊢[PRAAx] le one (pred m) := le_trans
    (lt_of_le_of_lt (zero_le r) hrj) (GaussianPolynomialMultiplicationMatrix.index_le_pred _ _ hm hj)
  have mul := AnalyticNumberTheory.PhiLower.le_mul_mono hp (le_refl c)
  exact le_congr ((congrAdd (one_mul c) (.eqRefl a)).eqTrans (add_comm _ _)) (add_comm _ _)
    (add_le_add_right a mul)
theorem local_store_bound (f G m a c r j : PTm n) (h : Γ ⊢[PRAAx] input f G m a c r j) : Γ ⊢[PRAAx]
    le (localBound a c r j) (width m a c) := by
  refine .orE (lt_or_le r j) ?_ ?_
  · exact le_congr (wrapped_bound_value _ _ _ _ Prf.hyp0).eqSymm (.eqRefl _)
      (wrapped_store_bound _ _ _ _ _ (.andE₁ (.andE₁ h.wk)) Prf.hyp0 (.andE₂ (.andE₂ h.wk)))
  · exact le_congr (unwrapped_bound_value _ _ _ _ Prf.hyp0).eqSymm (.eqRefl _) (unwrapped_store_bound _ _ _)
theorem local_bound_wrap (m a c r j : PTm n) (hr : Γ ⊢[PRAAx] lt r m) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    localBound a c r j ≐ a+wrap m (inverseIndex m j r) j*c := by
  refine .orE (lt_or_le r j) ?_ ?_
  · exact (wrapped_bound_value _ _ _ _ Prf.hyp0).eqTrans
      ((congrAdd (.eqRefl _) (congrMul (GaussianSuperellipticMatrixEntries.inverse_wrap_one _ _ _ hj.wk Prf.hyp0) (.eqRefl _))).eqTrans (by ipra_ring)).eqSymm
  · exact (unwrapped_bound_value _ _ _ _ Prf.hyp0).eqTrans
      ((congrAdd (.eqRefl _) (congrMul (GaussianSuperellipticMatrixEntries.inverse_wrap_zero _ _ _ hr.wk Prf.hyp0) (.eqRefl _))).eqTrans (by ipra_ring)).eqSymm

theorem pad_to_bound (C d B : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ d)
    (hB : Γ ⊢[PRAAx] le d B) : Γ ⊢[PRAAx] length (leftPad C (monus B d)) ≐ succ B :=
  (pad_length _ _).eqTrans ((congrAdd (.eqRefl _) hC).eqTrans
    ((by ipra_ring : Γ ⊢[PRAAx] monus B d+succ d ≐ succ (monus B d+d)).eqTrans
      (congrSucc ((add_comm _ _).eqTrans (eq_add_of_le hB).eqSymm))))
theorem witness_length (f G m a c r j : PTm n) (h : Γ ⊢[PRAAx] input f G m a c r j) : Γ ⊢[PRAAx]
    length (witness f G m a c r j) ≐ succ (width m a c) :=
  pad_to_bound _ _ _ (local_length _ _ _ _ _ _ _ (.andE₂ (.andE₂ (.andE₁ h)))
    (.andE₁ (.andE₂ h)) (.andE₂ (.andE₂ h))) (local_store_bound _ _ _ _ _ _ _ h)
theorem witness_canonical (f G m a c r j : PTm n) : Γ ⊢[PRAAx]
    canonicalCoefficients (witness f G m a c r j) := pad_canonical _ _ (local_canonical _ _ _ _ _ _ _)

theorem evaluation_equal (f G m a c r j x : PTm n) (h : Γ ⊢[PRAAx] input f G m a c r j) : Γ ⊢[PRAAx]
    evaluate (entryPolynomial f G m a c r j) x ≐ evaluate (witness f G m a c r j) x := by
  have hm := Prf.andE₁ (Prf.andE₁ h)
  have hf := Prf.andE₁ (Prf.andE₂ (Prf.andE₁ h))
  have hG := Prf.andE₂ (Prf.andE₂ (Prf.andE₁ h))
  have hr := Prf.andE₁ (Prf.andE₂ h)
  have hj := Prf.andE₂ (Prf.andE₂ h)
  refine .orE (lt_or_le r j) ?_ ?_
  · have left := GaussianSuperellipticMatrixEntries.matrix_entry_wrapped (Γ := (lt r j) :: Γ)
      f G m a c r j x hm.wk hf.wk hG.wk hr.wk hj.wk Prf.hyp0
    have right := (pad_evaluation (Γ := (lt r j) :: Γ) (localPolynomial f G m a c r j)
      (monus (width m a c) (localBound a c r j)) x).eqTrans
      ((evaluate_congr (wrapped_value _ _ _ _ _ _ _ Prf.hyp0) (.eqRefl _)).eqTrans
        (wrapped_evaluation _ _ _ _ _ _ _ _ hf.wk hG.wk hr.wk hj.wk))
    exact left.eqTrans right.eqSymm
  · have left := GaussianSuperellipticMatrixEntries.matrix_entry_unwrapped (Γ := (le j r) :: Γ)
      f G m a c r j x hm.wk hf.wk hG.wk hr.wk hj.wk Prf.hyp0
    have right := (pad_evaluation (Γ := (le j r) :: Γ) (localPolynomial f G m a c r j)
      (monus (width m a c) (localBound a c r j)) x).eqTrans
      ((evaluate_congr (unwrapped_value _ _ _ _ _ _ _ Prf.hyp0) (.eqRefl _)).eqTrans (A_evaluation _ _ _ _ _))
    exact left.eqTrans right.eqSymm

theorem original_length (f G m a c r j : PTm n) (h : Γ ⊢[PRAAx] input f G m a c r j) : Γ ⊢[PRAAx]
    length (entryPolynomial f G m a c r j) ≐ succ (width m a c) :=
  GaussianPolynomialMultiplicationMatrix.matrix_polynomial_length _ _ _ _ _ _ _
    (.andE₁ (.andE₁ h)) (.andE₂ (.andE₂ (.andE₁ h))) (.andE₁ (.andE₂ h)) (.andE₂ (.andE₂ h))
theorem original_canonical (f G m a c r j : PTm n) (h : Γ ⊢[PRAAx] input f G m a c r j) : Γ ⊢[PRAAx]
    canonicalCoefficients (entryPolynomial f G m a c r j) :=
  GaussianPolynomialMultiplicationMatrix.matrix_polynomial_canonical _ _ _ _ _ _ _
    (.andE₂ (.andE₂ (.andE₁ h))) (.andE₁ (.andE₂ h)) (.andE₂ (.andE₂ h))

theorem grid_equal (f G m a c r j : PTm n) (h : Γ ⊢[PRAAx] input f G m a c r j) : Γ ⊢[PRAAx]
    GaussianRationalGridCoefficientEquality.gridEqual (entryPolynomial f G m a c r j) (witness f G m a c r j) (width m a c) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] input (Syn.shift f) (Syn.shift G) (Syn.shift m)
      (Syn.shift a) (Syn.shift c) (Syn.shift r) (Syn.shift j) := by
    simpa only [Fm.shift,GaussianSuperellipticMatrixEntries.subst_input,Syn.shift] using h.shift
  refine .allI (.impI ?_)
  simpa only [Syn.shift,GaussianSuperellipticMatrixEntries.subst_entryPolynomial,subst_witness,
    GaussianPolynomialMultiplicationMatrix.subst_width] using
      evaluation_equal (Syn.shift f) (Syn.shift G) (Syn.shift m) (Syn.shift a) (Syn.shift c) (Syn.shift r) (Syn.shift j)
        (GaussianRationalFiniteGridIdentity.gridPoint (var 0)) hs.wk
theorem coefficients_equal (f G m a c r j : PTm n) (h : Γ ⊢[PRAAx] input f G m a c r j) : Γ ⊢[PRAAx]
    GaussianRationalGridCoefficientEquality.coefficientsEqual (entryPolynomial f G m a c r j) (witness f G m a c r j) (width m a c) :=
  GaussianRationalGridCoefficientEquality.coefficients_equal _ _ _ (original_length _ _ _ _ _ _ _ h)
    (witness_length _ _ _ _ _ _ _ h) (original_canonical _ _ _ _ _ _ _ h)
    (witness_canonical _ _ _ _ _ _ _) (grid_equal _ _ _ _ _ _ _ h)
theorem coefficient_equal (f G m a c r j s : PTm n) (h : Γ ⊢[PRAAx] input f G m a c r j)
    (hs : Γ ⊢[PRAAx] le s (width m a c)) : Γ ⊢[PRAAx]
    entry (entryPolynomial f G m a c r j) s ≐ entry (witness f G m a c r j) s :=
  GaussianRationalGridCoefficientEquality.coefficient_equal _ _ _ _ (original_length _ _ _ _ _ _ _ h)
    (witness_length _ _ _ _ _ _ _ h) (original_canonical _ _ _ _ _ _ _ h)
    (witness_canonical _ _ _ _ _ _ _) (grid_equal _ _ _ _ _ _ _ h) hs

/-- The original cell has the actual zero prefix dictated by the tight
store, even when its true degree is smaller or the whole cell is zero. -/
theorem leading_zero (f G m a c r j s : PTm n) (h : Γ ⊢[PRAAx] input f G m a c r j)
    (hs : Γ ⊢[PRAAx] lt s (monus (width m a c) (localBound a c r j))) : Γ ⊢[PRAAx]
    entry (entryPolynomial f G m a c r j) s ≐ GaussianRationalHorner.qzero := by
  have padding : Γ ⊢[PRAAx] le (monus (width m a c) (localBound a c r j)) (width m a c) :=
    le_congr (.eqRefl _) ((add_comm _ _).eqTrans (eq_add_of_le (local_store_bound _ _ _ _ _ _ _ h)).eqSymm)
      (le_add_right _ _)
  exact (coefficient_equal _ _ _ _ _ _ _ _ h (le_trans (le_of_lt hs) padding)).eqTrans
    (GaussianRationalPolynomialBuffers.pad_leading _ _ _ hs)
theorem local_coefficient (f G m a c r j s : PTm n) (h : Γ ⊢[PRAAx] input f G m a c r j)
    (hs : Γ ⊢[PRAAx] le s (localBound a c r j)) : Γ ⊢[PRAAx]
    entry (entryPolynomial f G m a c r j) (monus (width m a c) (localBound a c r j)+s) ≐
      entry (localPolynomial f G m a c r j) s := by
  have range : Γ ⊢[PRAAx] le (monus (width m a c) (localBound a c r j)+s) (width m a c) :=
    le_congr (.eqRefl _) ((add_comm _ _).eqTrans (eq_add_of_le (local_store_bound _ _ _ _ _ _ _ h)).eqSymm)
      (add_le_add₂ (le_refl _) hs)
  have localLen := local_length f G m a c r j (.andE₂ (.andE₂ (.andE₁ h)))
    (.andE₁ (.andE₂ h)) (.andE₂ (.andE₂ h))
  exact (coefficient_equal _ _ _ _ _ _ _ _ h range).eqTrans
    (GaussianRationalPolynomialBuffers.pad_tail _ _ _
      (lt_congr (.eqRefl _) localLen.eqSymm ((succ_monus_succ _ _).eqTrans hs)))

def certificate (f G m a c r j : PTm n) : Fm PTm n :=
  (length (localPolynomial f G m a c r j) ≐ succ (localBound a c r j)) ⋏
    ((localBound a c r j ≐ a+wrap m (inverseIndex m j r) j*c) ⋏
      (le (localBound a c r j) (width m a c) ⋏
        ((length (witness f G m a c r j) ≐ succ (width m a c)) ⋏
          GaussianRationalGridCoefficientEquality.coefficientsEqual
            (entryPolynomial f G m a c r j) (witness f G m a c r j) (width m a c))))
@[simp] theorem subst_certificate {l : ℕ} (σ : Fin n → PTm l) (f G m a c r j : PTm n) :
    (certificate f G m a c r j).subst σ = certificate (Syn.subst σ f) (Syn.subst σ G) (Syn.subst σ m)
      (Syn.subst σ a) (Syn.subst σ c) (Syn.subst σ r) (Syn.subst σ j) := by simp [certificate]
theorem matrix_coefficients (f G m a c r j : PTm n) (h : Γ ⊢[PRAAx] input f G m a c r j) : Γ ⊢[PRAAx]
    certificate f G m a c r j :=
  .andI (local_length _ _ _ _ _ _ _ (.andE₂ (.andE₂ (.andE₁ h))) (.andE₁ (.andE₂ h)) (.andE₂ (.andE₂ h)))
    (.andI (local_bound_wrap _ _ _ _ _ (.andE₁ (.andE₂ h)) (.andE₂ (.andE₂ h)))
      (.andI (local_store_bound _ _ _ _ _ _ _ h) (.andI (witness_length _ _ _ _ _ _ _ h) (coefficients_equal _ _ _ _ _ _ _ h))))

/-! Actual PR8 retains both SAME-width buffers, original Y coefficient
index, common width and the queried original/witness coefficient codes. -/
def output (f G m a c r j s : PTm n) : PTm n := pairT (entryPolynomial f G m a c r j)
  (pairT (witness f G m a c r j) (pairT (inverseIndex m j r) (pairT (width m a c)
    (pairT (entry (entryPolynomial f G m a c r j) s) (entry (witness f G m a c r j) s)))))
def outputF : PR 8 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7))
def run (f G m a c r j s : PTm n) : PTm n := app outputF ![f,G,m,a,c,r,j,s]
def fields (p : PTm n) (i : Fin 6) : PTm n :=
  ![fstT p,fstT (sndT p),fstT (sndT (sndT p)),fstT (sndT (sndT (sndT p))),
    fstT (sndT (sndT (sndT (sndT p)))),sndT (sndT (sndT (sndT (sndT p))))] i
@[simp] theorem subst_output {l : ℕ} (σ : Fin n → PTm l) (f G m a c r j s : PTm n) :
    Syn.subst σ (output f G m a c r j s) = output (Syn.subst σ f) (Syn.subst σ G) (Syn.subst σ m)
      (Syn.subst σ a) (Syn.subst σ c) (Syn.subst σ r) (Syn.subst σ j) (Syn.subst σ s) := by simp [output]
@[simp] theorem subst_run {l : ℕ} (σ : Fin n → PTm l) (f G m a c r j s : PTm n) :
    Syn.subst σ (run f G m a c r j s) = run (Syn.subst σ f) (Syn.subst σ G) (Syn.subst σ m)
      (Syn.subst σ a) (Syn.subst σ c) (Syn.subst σ r) (Syn.subst σ j) (Syn.subst σ s) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl
@[simp] theorem subst_fields {l : ℕ} (σ : Fin n → PTm l) (p : PTm n) (i : Fin 6) :
    Syn.subst σ (fields p i) = fields (Syn.subst σ p) i := by fin_cases i <;> simp [fields]
theorem program_at (f G m a c r j s : PTm n) : Γ ⊢[PRAAx] run f G m a c r j s ≐ output f G m a c r j s := by
  simpa [run,outputF] using toPR_eq (Γ := Γ)
    (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) : PTm 8) ![f,G,m,a,c,r,j,s]
theorem returned_fields (f G m a c r j s : PTm n) (i : Fin 6) : Γ ⊢[PRAAx]
    fields (run f G m a c r j s) i ≐
      ![entryPolynomial f G m a c r j,witness f G m a c r j,inverseIndex m j r,width m a c,
        entry (entryPolynomial f G m a c r j) s,entry (witness f G m a c r j) s] i := by
  have e0 := program_at (Γ := Γ) f G m a c r j s
  have e1 := (congrSnd e0).eqTrans (snd_pair _ _)
  have e2 := (congrSnd e1).eqTrans (snd_pair _ _)
  have e3 := (congrSnd e2).eqTrans (snd_pair _ _)
  have e4 := (congrSnd e3).eqTrans (snd_pair _ _)
  have e5 := (congrSnd e4).eqTrans (snd_pair _ _)
  fin_cases i
  · exact (congrFst e0).eqTrans (fst_pair _ _)
  · exact (congrFst e1).eqTrans (fst_pair _ _)
  · exact (congrFst e2).eqTrans (fst_pair _ _)
  · exact (congrFst e3).eqTrans (fst_pair _ _)
  · exact (congrFst e4).eqTrans (fst_pair _ _)
  · exact e5
theorem returned_equality (f G m a c r j s : PTm n) (h : Γ ⊢[PRAAx] input f G m a c r j)
    (hs : Γ ⊢[PRAAx] le s (width m a c)) : Γ ⊢[PRAAx]
    fields (run f G m a c r j s) 4 ≐ fields (run f G m a c r j s) 5 :=
  (returned_fields _ _ _ _ _ _ _ _ 4).eqTrans
    ((coefficient_equal _ _ _ _ _ _ _ _ h hs).eqTrans (returned_fields _ _ _ _ _ _ _ _ 5).eqSymm)

/-! All original buffers, stored bounds, matrix positions and coefficient
queries are numerical and bound internally in these ordinary sequents. -/
theorem actual_tight_store_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      ((length (localPolynomial (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)) ≐
        succ (localBound (var 3) (var 4) (var 5) (var 6))) ⋏
          canonicalCoefficients (localPolynomial (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)))) :=
  closeUniv 7 (.impI (.andI (local_length _ _ _ _ _ _ _ (.andE₂ (.andE₂ (.andE₁ Prf.hyp0)))
    (.andE₁ (.andE₂ Prf.hyp0)) (.andE₂ (.andE₂ Prf.hyp0))) (local_canonical _ _ _ _ _ _ _)))
theorem actual_wrapped_store_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 0) ⟶ lt (var 3) (var 4) ⟶ lt (var 4) (var 0) ⟶
      le ((var 1)+(var 2)) (width (var 0) (var 1) (var 2))) :=
  closeUniv 5 (.impI (.impI (.impI (wrapped_store_bound _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))
theorem actual_local_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      ((localBound (var 3) (var 4) (var 5) (var 6) ≐
        (var 3)+wrap (var 2) (inverseIndex (var 2) (var 6) (var 5)) (var 6)*(var 4)) ⋏
          le (localBound (var 3) (var 4) (var 5) (var 6)) (width (var 2) (var 3) (var 4)))) :=
  closeUniv 7 (.impI (.andI (local_bound_wrap _ _ _ _ _ (.andE₁ (.andE₂ Prf.hyp0)) (.andE₂ (.andE₂ Prf.hyp0)))
    (local_store_bound _ _ _ _ _ _ _ Prf.hyp0)))
theorem actual_same_width_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      ((length (entryPolynomial (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)) ≐ succ (width (var 2) (var 3) (var 4))) ⋏
        ((length (witness (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)) ≐ succ (width (var 2) (var 3) (var 4))) ⋏
          (canonicalCoefficients (entryPolynomial (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)) ⋏
            canonicalCoefficients (witness (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)))))) :=
  closeUniv 7 (.impI (.andI (original_length _ _ _ _ _ _ _ Prf.hyp0)
    (.andI (witness_length _ _ _ _ _ _ _ Prf.hyp0)
      (.andI (original_canonical _ _ _ _ _ _ _ Prf.hyp0) (witness_canonical _ _ _ _ _ _ _)))))
theorem actual_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      evaluate (entryPolynomial (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)) (var 7) ≐
        evaluate (witness (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)) (var 7)) :=
  closeUniv 8 (.impI (evaluation_equal _ _ _ _ _ _ _ _ Prf.hyp0))
theorem actual_coefficients_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      certificate (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)) :=
  closeUniv 7 (.impI (matrix_coefficients _ _ _ _ _ _ _ Prf.hyp0))
theorem actual_coefficient_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶ le (var 7) (width (var 2) (var 3) (var 4)) ⟶
      entry (entryPolynomial (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)) (var 7) ≐
        entry (witness (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)) (var 7)) :=
  closeUniv 8 (.impI (.impI (coefficient_equal _ _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_leading_zero_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      lt (var 7) (monus (width (var 2) (var 3) (var 4)) (localBound (var 3) (var 4) (var 5) (var 6))) ⟶
        entry (entryPolynomial (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)) (var 7) ≐ GaussianRationalHorner.qzero) :=
  closeUniv 8 (.impI (.impI (leading_zero _ _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_local_coefficient_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶ le (var 7) (localBound (var 3) (var 4) (var 5) (var 6)) ⟶
      entry (entryPolynomial (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))
        (monus (width (var 2) (var 3) (var 4)) (localBound (var 3) (var 4) (var 5) (var 6))+(var 7)) ≐
          entry (localPolynomial (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)) (var 7)) :=
  closeUniv 8 (.impI (.impI (local_coefficient _ _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ≐
      output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)) :=
  closeUniv 8 (program_at _ _ _ _ _ _ _ _)
theorem actual_returned_equality_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶ le (var 7) (width (var 2) (var 3) (var 4)) ⟶
      fields (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)) 4 ≐
        fields (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)) 5) :=
  closeUniv 8 (.impI (.impI (returned_equality _ _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianSuperellipticMatrixCoefficients
