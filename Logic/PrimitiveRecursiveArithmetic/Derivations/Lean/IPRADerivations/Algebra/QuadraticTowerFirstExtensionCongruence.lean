import IPRADerivations.Algebra.QuadraticTowerFirstExtensionOrder

/-!
# Actual first-extension quotient operations

Original raw bounded arrays retain their actual addition, negation and
multiplication programs. Genuine output heights derive sufficient sign
caps; the actual difference predicates are congruent under all three
operations. The actual strict order is translation invariant and is
preserved by multiplication by an actual positive element. These are
first-extension laws, including zero/redundant rational radicands; the
arbitrary-depth ordered-quotient provider remains separate.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Algebra.QuadraticTowerFirstExtensionCongruence

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis
open QuadraticTowerArrayCodec (arrayHeight)
open QuadraticTowerScalarBudget (amp growth)
open QuadraticTowerCoefficientArithmetic (added negated)
open QuadraticTowerMultiplicationTable (query)
open QuadraticTowerMultiplicationHeight (radicandsHeight)
open QuadraticTowerFirstExtensionSign (coefficients radicand)
open QuadraticTowerFirstExtensionIdeal (productBound query_sign_original product_coefficients native_sign_code_congr)
open QuadraticTowerFirstExtensionOrder (first_index second_index coefficients_entries native_difference_congr sign_difference)
open QuadraticTowerDifferenceIdentities (difference signDifference equivalent less)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem native_negative_pair (a b : PTm n) : Γ ⊢[PRAAx]
    QuadraticRationalPairArithmetic.negative (pairT a b) ≐
      pairT (RationalArithmetic.negative a) (RationalArithmetic.negative b) :=
  congrPairT (RationalAlgebra.negative_congr (fst_pair _ _)) (RationalAlgebra.negative_congr (snd_pair _ _))
theorem native_negative_congr {A C : PTm n} (e : Γ ⊢[PRAAx] A ≐ C) : Γ ⊢[PRAAx]
    QuadraticRationalPairArithmetic.negative A ≐ QuadraticRationalPairArithmetic.negative C := by
  simpa using Prf.eqCongr (QuadraticRationalPairArithmetic.negative (var 0) : PTm 1)
    (σ := ![A]) (σ' := ![C]) (fun i => by fin_cases i; exact e)
theorem negated_coefficients (A : PTm n) : Γ ⊢[PRAAx]
    coefficients (negated one A) ≐ QuadraticRationalPairArithmetic.negative (coefficients A) :=
  (coefficients_entries _).eqTrans
    ((congrPairT (QuadraticTowerCoefficientArithmetic.negated_lookup one A zero first_index)
      (QuadraticTowerCoefficientArithmetic.negated_lookup one A one second_index)).eqTrans
        ((native_negative_pair _ _).eqSymm.eqTrans (native_negative_congr (coefficients_entries A).eqSymm)))

/-- Original sign-zero equality descends through actual coefficientwise negation. -/
theorem negative_congruence (S D A C b : PTm n) (hS : Γ ⊢[PRAAx] le (amp b) S)
    (hD : Γ ⊢[PRAAx] radicandsHeight D one b) (ha : Γ ⊢[PRAAx] arrayHeight one A b)
    (hc : Γ ⊢[PRAAx] arrayHeight one C b)
    (hn : Γ ⊢[PRAAx] QuadraticRationalNonnegativeRadicand.nonnegative (radicand D))
    (hAC : Γ ⊢[PRAAx] equivalent one S D A C) : Γ ⊢[PRAAx]
    equivalent one S D (negated one A) (negated one C) :=
  (sign_difference S D _ _ b hS hD (QuadraticTowerSignRecipe.negated_height one A b ha)
    (QuadraticTowerSignRecipe.negated_height one C b hc) hn).eqTrans
      ((native_sign_code_congr _ (native_difference_congr (negated_coefficients A) (negated_coefficients C))).eqTrans
        (QuadraticRationalNonnegativeRadicand.equivalent_negative _ _ _ hn
          ((sign_difference S D A C b hS hD ha hc hn).eqSymm.eqTrans hAC)))

/-- The extra amplification is the proved height of the actual SUM difference. -/
theorem addition_congruence (S D A C E F b : PTm n) (hS : Γ ⊢[PRAAx] le (amp (amp b)) S)
    (hD : Γ ⊢[PRAAx] radicandsHeight D one b) (ha : Γ ⊢[PRAAx] arrayHeight one A b)
    (hc : Γ ⊢[PRAAx] arrayHeight one C b) (he : Γ ⊢[PRAAx] arrayHeight one E b)
    (hf : Γ ⊢[PRAAx] arrayHeight one F b)
    (hn : Γ ⊢[PRAAx] QuadraticRationalNonnegativeRadicand.nonnegative (radicand D))
    (hAC : Γ ⊢[PRAAx] equivalent one S D A C) (hEF : Γ ⊢[PRAAx] equivalent one S D E F) : Γ ⊢[PRAAx]
    equivalent one S D (added one A E) (added one C F) := by
  have small := le_trans (QuadraticTowerGrowth.amp_inflation (amp b)) hS
  have ds := QuadraticTowerMultiplicationHeight.radicands_mono _ _ _ _ hD (QuadraticTowerGrowth.amp_inflation b)
  exact (sign_difference S D _ _ (amp b) hS ds
    (QuadraticTowerMultiplicationHeight.added_height one A E b ha he)
    (QuadraticTowerMultiplicationHeight.added_height one C F b hc hf) hn).eqTrans
      ((native_sign_code_congr _ (native_difference_congr
        (QuadraticTowerFirstExtensionOrder.added_coefficients A E) (QuadraticTowerFirstExtensionOrder.added_coefficients C F))).eqTrans
          (QuadraticRationalNonnegativeRadicand.equivalent_add _ _ _ _ _ hn
            ((sign_difference S D A C b small hD ha hc hn).eqSymm.eqTrans hAC)
            ((sign_difference S D E F b small hD he hf hn).eqSymm.eqTrans hEF)))

/-- Both SAME computed products have their true growth(path 1,b) height. -/
theorem multiplication_congruence (M S D A C E F b : PTm n) (hM : Γ ⊢[PRAAx] le b M)
    (hS : Γ ⊢[PRAAx] le (amp (productBound b)) S)
    (hD : Γ ⊢[PRAAx] radicandsHeight D one b) (ha : Γ ⊢[PRAAx] arrayHeight one A b)
    (hc : Γ ⊢[PRAAx] arrayHeight one C b) (he : Γ ⊢[PRAAx] arrayHeight one E b)
    (hf : Γ ⊢[PRAAx] arrayHeight one F b)
    (hn : Γ ⊢[PRAAx] QuadraticRationalNonnegativeRadicand.nonnegative (radicand D))
    (hAC : Γ ⊢[PRAAx] equivalent one S D A C) (hEF : Γ ⊢[PRAAx] equivalent one S D E F) : Γ ⊢[PRAAx]
    equivalent one S D (query one M D A E) (query one M D C F) := by
  have grow := QuadraticTowerGrowth.growth_inflation (Γ := Γ) (QuadraticTowerGrowth.path one) b
  have small := le_trans (QuadraticTowerGrowth.amp_mono grow) hS
  have ds := QuadraticTowerMultiplicationHeight.radicands_mono _ _ _ _ hD grow
  exact (sign_difference S D _ _ (productBound b) hS ds
    (QuadraticTowerMultiplicationHeight.query_height one M D A E b hM hD ha he)
    (QuadraticTowerMultiplicationHeight.query_height one M D C F b hM hD hc hf) hn).eqTrans
      ((native_sign_code_congr _ (native_difference_congr
        (product_coefficients M D A E b hM hD ha he) (product_coefficients M D C F b hM hD hc hf))).eqTrans
          (QuadraticRationalNonnegativeRadicand.equivalent_multiply _ _ _ _ _ hn
            ((sign_difference S D A C b small hD ha hc hn).eqSymm.eqTrans hAC)
            ((sign_difference S D E F b small hD he hf hn).eqSymm.eqTrans hEF)))

/-- Translation retains the SAME exact constructed differences at every cap. -/
theorem equivalence_translation (S D A C E : PTm n) : Γ ⊢[PRAAx]
    Fm.iff (equivalent one S D (added one A E) (added one C E)) (equivalent one S D A C) :=
  QuadraticTowerDifferenceIdentities.equivalent_translation one S D A C E
theorem order_translation (S D A C E : PTm n) : Γ ⊢[PRAAx]
    Fm.iff (less one S D (added one A E) (added one C E)) (less one S D A C) :=
  QuadraticTowerDifferenceIdentities.less_translation one S D A C E

/-- An actual positive multiplier preserves the actual strict order. -/
theorem positive_multiplication_order (M S D A C E b : PTm n) (hM : Γ ⊢[PRAAx] le b M)
    (hS : Γ ⊢[PRAAx] le (amp (productBound b)) S)
    (hD : Γ ⊢[PRAAx] radicandsHeight D one b) (ha : Γ ⊢[PRAAx] arrayHeight one A b)
    (hc : Γ ⊢[PRAAx] arrayHeight one C b) (he : Γ ⊢[PRAAx] arrayHeight one E b)
    (hn : Γ ⊢[PRAAx] QuadraticRationalNonnegativeRadicand.nonnegative (radicand D))
    (hE : Γ ⊢[PRAAx] QuadraticTowerSignTable.query one S D E ≐ one)
    (hAC : Γ ⊢[PRAAx] less one S D A C) : Γ ⊢[PRAAx]
    less one S D (query one M D E A) (query one M D E C) := by
  have grow := QuadraticTowerGrowth.growth_inflation (Γ := Γ) (QuadraticTowerGrowth.path one) b
  have small := le_trans (QuadraticTowerGrowth.amp_mono grow) hS
  have bs := le_trans grow (le_trans (QuadraticTowerGrowth.amp_inflation (productBound b)) hS)
  have es := query_sign_original S D E (QuadraticTowerMultiplicationHeight.radicands_mono _ _ _ _ hD bs)
    (QuadraticTowerMultiplicationHeight.array_mono _ _ _ _ he bs) hn
  exact (sign_difference S D _ _ (productBound b) hS
    (QuadraticTowerMultiplicationHeight.radicands_mono _ _ _ _ hD grow)
    (QuadraticTowerMultiplicationHeight.query_height one M D E C b hM hD he hc)
    (QuadraticTowerMultiplicationHeight.query_height one M D E A b hM hD he ha) hn).eqTrans
      ((native_sign_code_congr _ (native_difference_congr
        (product_coefficients M D E C b hM hD he hc) (product_coefficients M D E A b hM hD he ha))).eqTrans
          (QuadraticRationalNonnegativeRadicand.less_multiply_positive _ _ _ _ hn (es.eqSymm.eqTrans hE)
            ((sign_difference S D C A b small hD hc ha hn).eqSymm.eqTrans hAC)))


/-! The actual frontend computes caps covering every operation comparison. -/
def signCap (b : PTm n) : PTm n := amp (productBound b)
def source (D A C E F b : PTm n) : Fm PTm n := QuadraticTowerFirstExtensionIdeal.source D A C b ⋏
  (arrayHeight one E b ⋏ arrayHeight one F b)
@[simp] theorem subst_signCap {k : ℕ} (σ : Fin n → PTm k) (b : PTm n) :
    Syn.subst σ (signCap b) = signCap (Syn.subst σ b) := by simp [signCap]
@[simp] theorem subst_source {k : ℕ} (σ : Fin n → PTm k) (D A C E F b : PTm n) :
    (source D A C E F b).subst σ = source (Syn.subst σ D) (Syn.subst σ A) (Syn.subst σ C)
      (Syn.subst σ E) (Syn.subst σ F) (Syn.subst σ b) := by simp [source]

theorem growth_one (b : PTm n) : Γ ⊢[PRAAx] growth one b ≐ amp b :=
  (QuadraticTowerScalarBudget.growth_succ zero b).eqTrans (QuadraticTowerGrowth.amp_congr (QuadraticTowerScalarBudget.growth_zero b))
theorem amp_le_product_bound (b : PTm n) : Γ ⊢[PRAAx] le (amp b) (productBound b) :=
  le_congr (growth_one b) (.eqRefl _) (QuadraticTowerGrowth.growth_counter_mono one (QuadraticTowerGrowth.path one) b
    (le_congr QuadraticTowerGrowth.path_zero (.eqRefl _) (QuadraticTowerGrowth.path_increasing zero)))
theorem input_cap (b : PTm n) : Γ ⊢[PRAAx] le (amp b) (signCap b) :=
  le_trans (amp_le_product_bound b) (QuadraticTowerGrowth.amp_inflation (productBound b))
theorem addition_cap (b : PTm n) : Γ ⊢[PRAAx] le (amp (amp b)) (signCap b) :=
  QuadraticTowerGrowth.amp_mono (amp_le_product_bound b)

def output (b D A C E F : PTm n) : PTm n :=
  pairT (signDifference one (signCap b) D (added one A E) (added one C F))
    (pairT (signDifference one (signCap b) D (negated one A) (negated one C))
      (pairT (signDifference one (signCap b) D (query one b D A E) (query one b D C F)) (signCap b)))
def outputF : PR 6 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
def run (b D A C E F : PTm n) : PTm n := PTm.app outputF ![b,D,A,C,E,F]
@[simp] theorem subst_output {k : ℕ} (σ : Fin n → PTm k) (b D A C E F : PTm n) :
    Syn.subst σ (output b D A C E F) = output (Syn.subst σ b) (Syn.subst σ D) (Syn.subst σ A)
      (Syn.subst σ C) (Syn.subst σ E) (Syn.subst σ F) := by simp [output]
@[simp] theorem subst_run {k : ℕ} (σ : Fin n → PTm k) (b D A C E F : PTm n) :
    Syn.subst σ (run b D A C E F) = run (Syn.subst σ b) (Syn.subst σ D) (Syn.subst σ A)
      (Syn.subst σ C) (Syn.subst σ E) (Syn.subst σ F) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem program_at (b D A C E F : PTm n) : Γ ⊢[PRAAx] run b D A C E F ≐ output b D A C E F := by
  simpa [run,outputF] using toPR_eq (Γ := Γ)
    (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6) ![b,D,A,C,E,F]
theorem returned_addition (b D A C E F : PTm n) : Γ ⊢[PRAAx] fstT (run b D A C E F) ≐
    signDifference one (signCap b) D (added one A E) (added one C F) :=
  (congrFst (program_at _ _ _ _ _ _)).eqTrans (fst_pair _ _)
theorem returned_tail (b D A C E F : PTm n) : Γ ⊢[PRAAx] sndT (run b D A C E F) ≐
    pairT (signDifference one (signCap b) D (negated one A) (negated one C))
      (pairT (signDifference one (signCap b) D (query one b D A E) (query one b D C F)) (signCap b)) :=
  (congrSnd (program_at _ _ _ _ _ _)).eqTrans (snd_pair _ _)
theorem returned_negative (b D A C E F : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run b D A C E F)) ≐
    signDifference one (signCap b) D (negated one A) (negated one C) :=
  (congrFst (returned_tail _ _ _ _ _ _)).eqTrans (fst_pair _ _)
theorem returned_product_pair (b D A C E F : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run b D A C E F)) ≐
    pairT (signDifference one (signCap b) D (query one b D A E) (query one b D C F)) (signCap b) :=
  (congrSnd (returned_tail _ _ _ _ _ _)).eqTrans (snd_pair _ _)
theorem returned_multiplication (b D A C E F : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run b D A C E F))) ≐
    signDifference one (signCap b) D (query one b D A E) (query one b D C F) :=
  (congrFst (returned_product_pair _ _ _ _ _ _)).eqTrans (fst_pair _ _)
theorem returned_cap (b D A C E F : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (run b D A C E F))) ≐ signCap b :=
  (congrSnd (returned_product_pair _ _ _ _ _ _)).eqTrans (snd_pair _ _)

/-- All three literal returned tags vanish from original quotient inputs. -/
theorem returned_congruences (b D A C E F : PTm n) (h : Γ ⊢[PRAAx] source D A C E F b)
    (hAC : Γ ⊢[PRAAx] equivalent one (signCap b) D A C)
    (hEF : Γ ⊢[PRAAx] equivalent one (signCap b) D E F) : Γ ⊢[PRAAx]
    (fstT (run b D A C E F) ≐ zero) ⋏
      ((fstT (sndT (run b D A C E F)) ≐ zero) ⋏ (fstT (sndT (sndT (run b D A C E F))) ≐ zero)) :=
  .andI ((returned_addition _ _ _ _ _ _).eqTrans
    (addition_congruence _ _ _ _ _ _ b (addition_cap b) h.andE₁.andE₁ h.andE₁.andE₂.andE₁
      h.andE₁.andE₂.andE₂.andE₁ h.andE₂.andE₁ h.andE₂.andE₂ h.andE₁.andE₂.andE₂.andE₂ hAC hEF))
    (.andI ((returned_negative _ _ _ _ _ _).eqTrans
      (negative_congruence _ _ _ _ b (input_cap b) h.andE₁.andE₁ h.andE₁.andE₂.andE₁
        h.andE₁.andE₂.andE₂.andE₁ h.andE₁.andE₂.andE₂.andE₂ hAC))
      ((returned_multiplication _ _ _ _ _ _).eqTrans
        (multiplication_congruence _ _ _ _ _ _ _ b (le_refl _) (le_refl _) h.andE₁.andE₁ h.andE₁.andE₂.andE₁
          h.andE₁.andE₂.andE₂.andE₁ h.andE₂.andE₁ h.andE₂.andE₂ h.andE₁.andE₂.andE₂.andE₂ hAC hEF)))

theorem positive_order_from_source (M S D A C E b : PTm n) (hM : Γ ⊢[PRAAx] le b M)
    (hS : Γ ⊢[PRAAx] le (amp (productBound b)) S) (h : Γ ⊢[PRAAx] source D A C E E b)
    (hE : Γ ⊢[PRAAx] QuadraticTowerSignTable.query one S D E ≐ one) (hAC : Γ ⊢[PRAAx] less one S D A C) : Γ ⊢[PRAAx]
    less one S D (query one M D E A) (query one M D E C) :=
  positive_multiplication_order _ _ _ _ _ _ b hM hS h.andE₁.andE₁ h.andE₁.andE₂.andE₁
    h.andE₁.andE₂.andE₂.andE₁ h.andE₂.andE₁ h.andE₁.andE₂.andE₂.andE₂ hE hAC

theorem actual_first_extension_negative_coefficients_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (coefficients (negated one (var 0)) ≐ QuadraticRationalPairArithmetic.negative (coefficients (var 0))) :=
  closeUniv 1 (negated_coefficients _)
theorem actual_first_extension_equivalence_translation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (Fm.iff (equivalent one (var 0) (var 1) (added one (var 2) (var 4)) (added one (var 3) (var 4)))
      (equivalent one (var 0) (var 1) (var 2) (var 3))) := closeUniv 5 (equivalence_translation _ _ _ _ _)
theorem actual_first_extension_order_translation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (Fm.iff (less one (var 0) (var 1) (added one (var 2) (var 4)) (added one (var 3) (var 4)))
      (less one (var 0) (var 1) (var 2) (var 3))) := closeUniv 5 (order_translation _ _ _ _ _)
theorem actual_first_extension_quotient_computed_cap_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (le (amp (var 0)) (signCap (var 0)) ⋏ le (amp (amp (var 0))) (signCap (var 0))) :=
  closeUniv 1 (.andI (input_cap _) (addition_cap _))
theorem actual_first_extension_quotient_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ≐ output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) :=
  closeUniv 6 (program_at _ _ _ _ _ _)
theorem actual_first_extension_quotient_returned_cap_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (sndT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)))) ≐ signCap (var 0)) :=
  closeUniv 6 (returned_cap _ _ _ _ _ _)
theorem original_computed_first_extension_quotient_congruences_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (source (var 1) (var 2) (var 3) (var 4) (var 5) (var 0) ⟶
      equivalent one (signCap (var 0)) (var 1) (var 2) (var 3) ⟶
      equivalent one (signCap (var 0)) (var 1) (var 4) (var 5) ⟶
        (fstT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) ≐ zero) ⋏
          ((fstT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))) ≐ zero) ⋏
            (fstT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)))) ≐ zero))) :=
  closeUniv 6 (.impI (.impI (.impI (returned_congruences _ _ _ _ _ _ (.hyp (by simp)) Prf.hyp1 Prf.hyp0))))
theorem original_first_extension_positive_multiplication_order_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (le (var 6) (var 0) ⟶ le (amp (productBound (var 6))) (var 1) ⟶
      source (var 2) (var 3) (var 4) (var 5) (var 5) (var 6) ⟶
      QuadraticTowerSignTable.query one (var 1) (var 2) (var 5) ≐ one ⟶ less one (var 1) (var 2) (var 3) (var 4) ⟶
        less one (var 1) (var 2) (query one (var 0) (var 2) (var 5) (var 3)) (query one (var 0) (var 2) (var 5) (var 4))) :=
  closeUniv 7 (.impI (.impI (.impI (.impI (.impI (positive_order_from_source _ _ _ _ _ _ (var 6)
    (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)) Prf.hyp1 Prf.hyp0))))))

end LeanProofs.IPRA.Algebra.QuadraticTowerFirstExtensionCongruence
