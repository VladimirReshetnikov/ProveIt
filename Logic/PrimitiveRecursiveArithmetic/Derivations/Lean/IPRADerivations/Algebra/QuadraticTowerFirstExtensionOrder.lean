import IPRADerivations.Algebra.QuadraticTowerFirstExtensionIdeal
import IPRADerivations.Algebra.QuadraticTowerDifferenceIdentities
import IPRADerivations.Core.CongruenceTactic

/-!
# Actual first-extension equivalence and order

Original raw numerical arrays are compared by the SAME difference and
sign programs. The true negation/addition height bounds compute a
sufficient sign cap. Native nonnegative-radicand order laws then apply
to the original pair values, including zero and redundant extensions.
The arbitrary-depth ordered-quotient provider remains separate.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Algebra.QuadraticTowerFirstExtensionOrder

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis
open QuadraticTowerArrayCodec (arrayHeight)
open QuadraticTowerScalarBudget (amp)
open QuadraticTowerCoefficientArithmetic (added negated)
open QuadraticTowerMultiplicationHeight (radicandsHeight)
open QuadraticTowerFirstExtensionSign (coefficients radicand)
open QuadraticTowerFirstExtensionIdeal (left_head right_head query_sign_original native_sign_code_congr)
open QuadraticTowerDifferenceIdentities (difference signDifference equivalent less)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem first_index : Γ ⊢[PRAAx] lt zero (QuadraticTowerCoefficients.width (one : PTm n)) :=
  lt_congr (.eqRefl _) (pw_one two).eqSymm (zero_lt_succ one)
theorem second_index : Γ ⊢[PRAAx] lt one (QuadraticTowerCoefficients.width (one : PTm n)) :=
  lt_congr (.eqRefl _) (pw_one two).eqSymm (le_refl two)
theorem coefficients_entries (A : PTm n) : Γ ⊢[PRAAx] coefficients A ≐ pairT (entry A zero) (entry A one) :=
  congrPairT (left_head A) (right_head A)

theorem native_difference_pair (a b c e : PTm n) : Γ ⊢[PRAAx]
    QuadraticRationalEqualityOrder.difference (pairT a b) (pairT c e) ≐
      pairT (QuadraticTowerDifferenceIdentities.scalarDifference a c)
        (QuadraticTowerDifferenceIdentities.scalarDifference b e) :=
  congrPairT (RationalAlgebra.add_congr (fst_pair _ _)
    ((fst_pair _ _).eqTrans (RationalAlgebra.negative_congr (fst_pair _ _))))
    (RationalAlgebra.add_congr (snd_pair _ _) ((snd_pair _ _).eqTrans (RationalAlgebra.negative_congr (snd_pair _ _))))
theorem native_difference_congr {A A' C C' : PTm n} (ha : Γ ⊢[PRAAx] A ≐ A') (hc : Γ ⊢[PRAAx] C ≐ C') :
    Γ ⊢[PRAAx] QuadraticRationalEqualityOrder.difference A C ≐ QuadraticRationalEqualityOrder.difference A' C' := by
  ipra_congr (QuadraticRationalEqualityOrder.difference (var 0) (var 1) : PTm 2) with [ha, hc]

/-- Literal pair equality is only for the actual two returned coefficients. -/
theorem difference_coefficients (A C : PTm n) : Γ ⊢[PRAAx]
    coefficients (difference one A C) ≐ QuadraticRationalEqualityOrder.difference (coefficients A) (coefficients C) :=
  (coefficients_entries _).eqTrans
    ((congrPairT (QuadraticTowerDifferenceIdentities.difference_lookup one A C zero first_index)
      (QuadraticTowerDifferenceIdentities.difference_lookup one A C one second_index)).eqTrans
        ((native_difference_pair _ _ _ _).eqSymm.eqTrans
          (native_difference_congr (coefficients_entries A).eqSymm (coefficients_entries C).eqSymm)))

theorem difference_height (h A C b : PTm n) (ha : Γ ⊢[PRAAx] arrayHeight h A b)
    (hc : Γ ⊢[PRAAx] arrayHeight h C b) : Γ ⊢[PRAAx] arrayHeight h (difference h A C) (amp b) :=
  QuadraticTowerMultiplicationHeight.added_height h A _ b ha (QuadraticTowerSignRecipe.negated_height h C b hc)

/-- No sign/correctness law is supplied for the constructed difference. -/
theorem sign_difference (S D A C b : PTm n) (hS : Γ ⊢[PRAAx] le (amp b) S)
    (hD : Γ ⊢[PRAAx] radicandsHeight D one b) (ha : Γ ⊢[PRAAx] arrayHeight one A b)
    (hc : Γ ⊢[PRAAx] arrayHeight one C b)
    (hn : Γ ⊢[PRAAx] QuadraticRationalNonnegativeRadicand.nonnegative (radicand D)) : Γ ⊢[PRAAx]
    signDifference one S D A C ≐ QuadraticRationalNonnegativeRadicand.sign (radicand D)
      (QuadraticRationalEqualityOrder.difference (coefficients A) (coefficients C)) :=
  (query_sign_original S D _ (QuadraticTowerMultiplicationHeight.radicands_mono _ _ _ _ hD
    (le_trans (QuadraticTowerGrowth.amp_inflation b) hS))
    (QuadraticTowerMultiplicationHeight.array_mono _ _ _ _ (difference_height one A C b ha hc) hS) hn).eqTrans
      (native_sign_code_congr _ (difference_coefficients A C))

theorem equivalent_native (S D A C b : PTm n) (hS : Γ ⊢[PRAAx] le (amp b) S)
    (hD : Γ ⊢[PRAAx] radicandsHeight D one b) (ha : Γ ⊢[PRAAx] arrayHeight one A b)
    (hc : Γ ⊢[PRAAx] arrayHeight one C b)
    (hn : Γ ⊢[PRAAx] QuadraticRationalNonnegativeRadicand.nonnegative (radicand D)) : Γ ⊢[PRAAx]
    Fm.iff (equivalent one S D A C)
      (QuadraticRationalNonnegativeRadicand.equivalent (radicand D) (coefficients A) (coefficients C)) :=
  .andI (.impI ((sign_difference S D A C b hS.wk hD.wk ha.wk hc.wk hn.wk).eqSymm.eqTrans Prf.hyp0))
    (.impI ((sign_difference S D A C b hS.wk hD.wk ha.wk hc.wk hn.wk).eqTrans Prf.hyp0))
theorem less_native (S D A C b : PTm n) (hS : Γ ⊢[PRAAx] le (amp b) S)
    (hD : Γ ⊢[PRAAx] radicandsHeight D one b) (ha : Γ ⊢[PRAAx] arrayHeight one A b)
    (hc : Γ ⊢[PRAAx] arrayHeight one C b)
    (hn : Γ ⊢[PRAAx] QuadraticRationalNonnegativeRadicand.nonnegative (radicand D)) : Γ ⊢[PRAAx]
    Fm.iff (less one S D A C)
      (QuadraticRationalNonnegativeRadicand.less (radicand D) (coefficients A) (coefficients C)) :=
  .andI (.impI ((sign_difference S D C A b hS.wk hD.wk hc.wk ha.wk hn.wk).eqSymm.eqTrans Prf.hyp0))
    (.impI ((sign_difference S D C A b hS.wk hD.wk hc.wk ha.wk hn.wk).eqTrans Prf.hyp0))

theorem equivalent_symmetric (S D A C b : PTm n) (hS : Γ ⊢[PRAAx] le (amp b) S)
    (hD : Γ ⊢[PRAAx] radicandsHeight D one b) (ha : Γ ⊢[PRAAx] arrayHeight one A b)
    (hc : Γ ⊢[PRAAx] arrayHeight one C b)
    (hn : Γ ⊢[PRAAx] QuadraticRationalNonnegativeRadicand.nonnegative (radicand D))
    (h : Γ ⊢[PRAAx] equivalent one S D A C) : Γ ⊢[PRAAx] equivalent one S D C A :=
  (sign_difference S D C A b hS hD hc ha hn).eqTrans
    (QuadraticRationalNonnegativeRadicand.equivalent_symm _ _ _ hn
      ((sign_difference S D A C b hS hD ha hc hn).eqSymm.eqTrans h))

theorem equivalent_transitive (S D A C E b : PTm n) (hS : Γ ⊢[PRAAx] le (amp b) S)
    (hD : Γ ⊢[PRAAx] radicandsHeight D one b) (ha : Γ ⊢[PRAAx] arrayHeight one A b)
    (hc : Γ ⊢[PRAAx] arrayHeight one C b) (he : Γ ⊢[PRAAx] arrayHeight one E b)
    (hn : Γ ⊢[PRAAx] QuadraticRationalNonnegativeRadicand.nonnegative (radicand D))
    (hAC : Γ ⊢[PRAAx] equivalent one S D A C) (hCE : Γ ⊢[PRAAx] equivalent one S D C E) : Γ ⊢[PRAAx]
    equivalent one S D A E :=
  (sign_difference S D A E b hS hD ha he hn).eqTrans
    (QuadraticRationalNonnegativeRadicand.equivalent_trans _ _ _ _ hn
      ((sign_difference S D A C b hS hD ha hc hn).eqSymm.eqTrans hAC)
      ((sign_difference S D C E b hS hD hc he hn).eqSymm.eqTrans hCE))

theorem less_transitive (S D A C E b : PTm n) (hS : Γ ⊢[PRAAx] le (amp b) S)
    (hD : Γ ⊢[PRAAx] radicandsHeight D one b) (ha : Γ ⊢[PRAAx] arrayHeight one A b)
    (hc : Γ ⊢[PRAAx] arrayHeight one C b) (he : Γ ⊢[PRAAx] arrayHeight one E b)
    (hn : Γ ⊢[PRAAx] QuadraticRationalNonnegativeRadicand.nonnegative (radicand D))
    (hAC : Γ ⊢[PRAAx] less one S D A C) (hCE : Γ ⊢[PRAAx] less one S D C E) : Γ ⊢[PRAAx]
    less one S D A E :=
  (sign_difference S D E A b hS hD he ha hn).eqTrans
    (QuadraticRationalNonnegativeRadicand.less_trans _ _ _ _ hn
      ((sign_difference S D C A b hS hD hc ha hn).eqSymm.eqTrans hAC)
      ((sign_difference S D E C b hS hD he hc hn).eqSymm.eqTrans hCE))

theorem trichotomy (S D A C b : PTm n) (hS : Γ ⊢[PRAAx] le (amp b) S)
    (hD : Γ ⊢[PRAAx] radicandsHeight D one b) (ha : Γ ⊢[PRAAx] arrayHeight one A b)
    (hc : Γ ⊢[PRAAx] arrayHeight one C b)
    (hn : Γ ⊢[PRAAx] QuadraticRationalNonnegativeRadicand.nonnegative (radicand D)) : Γ ⊢[PRAAx]
    less one S D A C ⋎ (less one S D C A ⋎ equivalent one S D A C) := by
  refine .orE (QuadraticRationalNonnegativeRadicand.trichotomy (radicand D) (coefficients A) (coefficients C) hn) ?_ ?_
  · exact .orI₁ ((sign_difference S D C A b hS.wk hD.wk hc.wk ha.wk hn.wk).eqTrans Prf.hyp0)
  · refine .orE Prf.hyp0 ?_ ?_
    · exact .orI₂ (.orI₁ ((sign_difference S D A C b hS.wk.wk hD.wk.wk ha.wk.wk hc.wk.wk hn.wk.wk).eqTrans Prf.hyp0))
    · exact .orI₂ (.orI₂ ((sign_difference S D A C b hS.wk.wk hD.wk.wk ha.wk.wk hc.wk.wk hn.wk.wk).eqTrans Prf.hyp0))

theorem native_add_pair (a b c e : PTm n) : Γ ⊢[PRAAx]
    QuadraticRationalPairArithmetic.add (pairT a b) (pairT c e) ≐
      pairT (RationalArithmetic.add a c) (RationalArithmetic.add b e) :=
  congrPairT (RationalAlgebra.add_congr (fst_pair _ _) (fst_pair _ _))
    (RationalAlgebra.add_congr (snd_pair _ _) (snd_pair _ _))
theorem native_add_congr {A A' C C' : PTm n} (ha : Γ ⊢[PRAAx] A ≐ A') (hc : Γ ⊢[PRAAx] C ≐ C') :
    Γ ⊢[PRAAx] QuadraticRationalPairArithmetic.add A C ≐ QuadraticRationalPairArithmetic.add A' C' := by
  ipra_congr (QuadraticRationalPairArithmetic.add (var 0) (var 1) : PTm 2) with [ha, hc]
theorem added_coefficients (A C : PTm n) : Γ ⊢[PRAAx]
    coefficients (added one A C) ≐ QuadraticRationalPairArithmetic.add (coefficients A) (coefficients C) :=
  (coefficients_entries _).eqTrans
    ((congrPairT (QuadraticTowerCoefficientArithmetic.added_lookup one A C zero first_index)
      (QuadraticTowerCoefficientArithmetic.added_lookup one A C one second_index)).eqTrans
        ((native_add_pair _ _ _ _).eqSymm.eqTrans
          (native_add_congr (coefficients_entries A).eqSymm (coefficients_entries C).eqSymm)))

theorem positive_add (S D A C b : PTm n) (hS : Γ ⊢[PRAAx] le (amp b) S)
    (hD : Γ ⊢[PRAAx] radicandsHeight D one b) (ha : Γ ⊢[PRAAx] arrayHeight one A b)
    (hc : Γ ⊢[PRAAx] arrayHeight one C b)
    (hn : Γ ⊢[PRAAx] QuadraticRationalNonnegativeRadicand.nonnegative (radicand D))
    (hA : Γ ⊢[PRAAx] QuadraticTowerSignTable.query one S D A ≐ one)
    (hC : Γ ⊢[PRAAx] QuadraticTowerSignTable.query one S D C ≐ one) : Γ ⊢[PRAAx]
    QuadraticTowerSignTable.query one S D (added one A C) ≐ one := by
  have bs := le_trans (QuadraticTowerGrowth.amp_inflation b) hS
  have ds := QuadraticTowerMultiplicationHeight.radicands_mono D one b S hD bs
  have sa := query_sign_original S D A ds (QuadraticTowerMultiplicationHeight.array_mono _ _ _ _ ha bs) hn
  have sc := query_sign_original S D C ds (QuadraticTowerMultiplicationHeight.array_mono _ _ _ _ hc bs) hn
  exact (query_sign_original S D _ ds
    (QuadraticTowerMultiplicationHeight.array_mono _ _ _ _ (QuadraticTowerMultiplicationHeight.added_height one A C b ha hc) hS) hn).eqTrans
      ((native_sign_code_congr _ (added_coefficients A C)).eqTrans
        (QuadraticRationalNonnegativeRadicand.positive_add _ _ _ hn (sa.eqSymm.eqTrans hA) (sc.eqSymm.eqTrans hC)))

/-! The actual comparison payload computes its own sufficient cap. -/
def output (b D A C : PTm n) : PTm n := pairT (difference one A C)
  (pairT (difference one C A) (pairT (signDifference one (amp b) D A C)
    (pairT (signDifference one (amp b) D C A) (amp b))))
def outputF : PR 4 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3))
def run (b D A C : PTm n) : PTm n := PTm.app outputF ![b,D,A,C]
@[simp] theorem subst_output {k : ℕ} (σ : Fin n → PTm k) (b D A C : PTm n) :
    Syn.subst σ (output b D A C) = output (Syn.subst σ b) (Syn.subst σ D) (Syn.subst σ A) (Syn.subst σ C) := by simp [output]
@[simp] theorem subst_run {k : ℕ} (σ : Fin n → PTm k) (b D A C : PTm n) :
    Syn.subst σ (run b D A C) = run (Syn.subst σ b) (Syn.subst σ D) (Syn.subst σ A) (Syn.subst σ C) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem program_at (b D A C : PTm n) : Γ ⊢[PRAAx] run b D A C ≐ output b D A C := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) : PTm 4) ![b,D,A,C]
theorem returned_difference (b D A C : PTm n) : Γ ⊢[PRAAx] fstT (run b D A C) ≐ difference one A C :=
  (congrFst (program_at _ _ _ _)).eqTrans (fst_pair _ _)
theorem returned_tail (b D A C : PTm n) : Γ ⊢[PRAAx] sndT (run b D A C) ≐
    pairT (difference one C A) (pairT (signDifference one (amp b) D A C) (pairT (signDifference one (amp b) D C A) (amp b))) :=
  (congrSnd (program_at _ _ _ _)).eqTrans (snd_pair _ _)
theorem returned_reverse (b D A C : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run b D A C)) ≐ difference one C A :=
  (congrFst (returned_tail _ _ _ _)).eqTrans (fst_pair _ _)
theorem returned_tags (b D A C : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run b D A C)) ≐
    pairT (signDifference one (amp b) D A C) (pairT (signDifference one (amp b) D C A) (amp b)) :=
  (congrSnd (returned_tail _ _ _ _)).eqTrans (snd_pair _ _)
theorem returned_tag (b D A C : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run b D A C))) ≐ signDifference one (amp b) D A C :=
  (congrFst (returned_tags _ _ _ _)).eqTrans (fst_pair _ _)
theorem returned_reverse_pair (b D A C : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (run b D A C))) ≐
    pairT (signDifference one (amp b) D C A) (amp b) :=
  (congrSnd (returned_tags _ _ _ _)).eqTrans (snd_pair _ _)
theorem returned_reverse_tag (b D A C : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (sndT (run b D A C)))) ≐ signDifference one (amp b) D C A :=
  (congrFst (returned_reverse_pair _ _ _ _)).eqTrans (fst_pair _ _)
theorem returned_cap (b D A C : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (sndT (run b D A C)))) ≐ amp b :=
  (congrSnd (returned_reverse_pair _ _ _ _)).eqTrans (snd_pair _ _)

theorem returned_trichotomy (b D A C : PTm n)
    (h : Γ ⊢[PRAAx] QuadraticTowerFirstExtensionIdeal.source D A C b) : Γ ⊢[PRAAx]
    (fstT (sndT (sndT (sndT (run b D A C)))) ≐ one) ⋎
      ((fstT (sndT (sndT (run b D A C))) ≐ one) ⋎ (fstT (sndT (sndT (run b D A C))) ≐ zero)) := by
  have actual := trichotomy (amp b) D A C b (le_refl _) h.andE₁ h.andE₂.andE₁ h.andE₂.andE₂.andE₁ h.andE₂.andE₂.andE₂
  refine .orE actual ?_ ?_
  · exact .orI₁ ((returned_reverse_tag b D A C).eqTrans Prf.hyp0)
  · refine .orE Prf.hyp0 ?_ ?_
    · exact .orI₂ (.orI₁ ((returned_tag b D A C).eqTrans Prf.hyp0))
    · exact .orI₂ (.orI₂ ((returned_tag b D A C).eqTrans Prf.hyp0))

theorem actual_first_extension_difference_coefficients_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (coefficients (difference one (var 0) (var 1)) ≐
      QuadraticRationalEqualityOrder.difference (coefficients (var 0)) (coefficients (var 1))) :=
  closeUniv 2 (difference_coefficients _ _)
theorem original_first_extension_difference_sign_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le (amp (var 4)) (var 0) ⟶ QuadraticTowerFirstExtensionIdeal.source (var 1) (var 2) (var 3) (var 4) ⟶
      signDifference one (var 0) (var 1) (var 2) (var 3) ≐
        QuadraticRationalNonnegativeRadicand.sign (radicand (var 1))
          (QuadraticRationalEqualityOrder.difference (coefficients (var 2)) (coefficients (var 3)))) :=
  closeUniv 5 (.impI (.impI (sign_difference _ _ _ _ (var 4) Prf.hyp1 Prf.hyp0.andE₁
    Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂)))
theorem original_first_extension_equivalence_symmetry_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le (amp (var 4)) (var 0) ⟶ QuadraticTowerFirstExtensionIdeal.source (var 1) (var 2) (var 3) (var 4) ⟶
      equivalent one (var 0) (var 1) (var 2) (var 3) ⟶ equivalent one (var 0) (var 1) (var 3) (var 2)) :=
  closeUniv 5 (.impI (.impI (.impI (equivalent_symmetric _ _ _ _ (var 4) (.hyp (by simp)) Prf.hyp1.andE₁
    Prf.hyp1.andE₂.andE₁ Prf.hyp1.andE₂.andE₂.andE₁ Prf.hyp1.andE₂.andE₂.andE₂ Prf.hyp0))))
theorem original_first_extension_trichotomy_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le (amp (var 4)) (var 0) ⟶ QuadraticTowerFirstExtensionIdeal.source (var 1) (var 2) (var 3) (var 4) ⟶
      less one (var 0) (var 1) (var 2) (var 3) ⋎
        (less one (var 0) (var 1) (var 3) (var 2) ⋎ equivalent one (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 5 (.impI (.impI (trichotomy _ _ _ _ (var 4) Prf.hyp1 Prf.hyp0.andE₁
    Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂)))
theorem actual_first_extension_order_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (run (var 0) (var 1) (var 2) (var 3) ≐ output (var 0) (var 1) (var 2) (var 3)) := closeUniv 4 (program_at _ _ _ _)
theorem actual_first_extension_order_returned_cap_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (sndT (sndT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3))))) ≐ amp (var 0)) := closeUniv 4 (returned_cap _ _ _ _)
theorem original_computed_first_extension_trichotomy_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (QuadraticTowerFirstExtensionIdeal.source (var 1) (var 2) (var 3) (var 0) ⟶
      (fstT (sndT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3))))) ≐ one) ⋎
        ((fstT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3)))) ≐ one) ⋎
          (fstT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3)))) ≐ zero))) :=
  closeUniv 4 (.impI (returned_trichotomy _ _ _ _ Prf.hyp0))

theorem original_first_extension_equivalence_transitivity_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le (amp (var 5)) (var 0) ⟶ arrayHeight one (var 4) (var 5) ⟶
      (equivalent one (var 0) (var 1) (var 2) (var 3) ⋏ equivalent one (var 0) (var 1) (var 3) (var 4)) ⟶
      QuadraticTowerFirstExtensionIdeal.source (var 1) (var 2) (var 3) (var 5) ⟶
        equivalent one (var 0) (var 1) (var 2) (var 4)) :=
  closeUniv 6 (.impI (.impI (.impI (.impI (equivalent_transitive _ _ _ _ _ (var 5)
    (.hyp (by simp)) Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁
    (.hyp (by simp)) Prf.hyp0.andE₂.andE₂.andE₂ Prf.hyp1.andE₁ Prf.hyp1.andE₂)))))
theorem original_first_extension_order_transitivity_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le (amp (var 5)) (var 0) ⟶ arrayHeight one (var 4) (var 5) ⟶
      (less one (var 0) (var 1) (var 2) (var 3) ⋏ less one (var 0) (var 1) (var 3) (var 4)) ⟶
      QuadraticTowerFirstExtensionIdeal.source (var 1) (var 2) (var 3) (var 5) ⟶
        less one (var 0) (var 1) (var 2) (var 4)) :=
  closeUniv 6 (.impI (.impI (.impI (.impI (less_transitive _ _ _ _ _ (var 5)
    (.hyp (by simp)) Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁
    (.hyp (by simp)) Prf.hyp0.andE₂.andE₂.andE₂ Prf.hyp1.andE₁ Prf.hyp1.andE₂)))))
theorem original_first_extension_positive_sum_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le (amp (var 4)) (var 0) ⟶ QuadraticTowerSignTable.query one (var 0) (var 1) (var 2) ≐ one ⟶
      QuadraticTowerSignTable.query one (var 0) (var 1) (var 3) ≐ one ⟶
      QuadraticTowerFirstExtensionIdeal.source (var 1) (var 2) (var 3) (var 4) ⟶
        QuadraticTowerSignTable.query one (var 0) (var 1) (added one (var 2) (var 3)) ≐ one) :=
  closeUniv 5 (.impI (.impI (.impI (.impI (positive_add _ _ _ _ (var 4)
    (.hyp (by simp)) Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₂ (.hyp (by simp)) Prf.hyp1)))))

end LeanProofs.IPRA.Algebra.QuadraticTowerFirstExtensionOrder
