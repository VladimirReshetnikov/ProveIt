import IPRADerivations.Algebra.QuadraticRationalSignDispatch
import IPRADerivations.Algebra.QuadraticTowerSignEmbedding

/-!
# Correctness of the actual first-extension sign-table query

The numerical table, its actual changed budget and all three actual lower
queries are retained. Original scalar bounds derive the required addresses;
the original rational-stage provider supplies the mathematical sign.
This is a first-extension scheduler theorem, not an arbitrary-depth claim.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Algebra.QuadraticTowerFirstExtensionSign

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis
open QuadraticTowerArrayCodec (arrayHeight normalized)
open QuadraticTowerScalarBudget (height)
open QuadraticTowerMultiplicationTable (budget leftHalf rightHalf)
open QuadraticTowerMultiplicationHeight (radicandsHeight array_mono)
open QuadraticTowerSignRecipe (read firstTag secondTag thirdTag thirdInput)
open QuadraticRationalSignDispatch (scalarTag)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (entry_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def coefficients (A : PTm n) : PTm n := pairT (entry (leftHalf zero A) zero) (entry (rightHalf zero A) zero)
def radicand (D : PTm n) : PTm n := entry (entry D zero) zero
@[simp] theorem subst_coefficients {k : ℕ} (σ : Fin n → PTm k) (A : PTm n) :
    Syn.subst σ (coefficients A) = coefficients (Syn.subst σ A) := by simp [coefficients]
@[simp] theorem subst_radicand {k : ℕ} (σ : Fin n → PTm k) (D : PTm n) :
    Syn.subst σ (radicand D) = radicand (Syn.subst σ D) := by simp [radicand]

theorem ground_read (B D A : PTm n) (ha : Γ ⊢[PRAAx] arrayHeight zero A B) : Γ ⊢[PRAAx]
    read zero B (QuadraticTowerSignTable.table zero B D) A ≐ scalarTag (entry A zero) :=
  QuadraticTowerSignTable.query_zero_original B D A ha
theorem ground_product_head (B D A C : PTm n) (ha : Γ ⊢[PRAAx] arrayHeight zero A B)
    (hc : Γ ⊢[PRAAx] arrayHeight zero C B) : Γ ⊢[PRAAx]
    entry (QuadraticTowerMultiplicationTable.query zero B D A C) zero ≐
      RationalArithmetic.multiply (entry A zero) (entry C zero) :=
  (entry_congr (QuadraticTowerOperandProperness.query_zero_original B D A C ha hc) (.eqRefl _)).eqTrans
    (QuadraticTowerCoefficients.singleton_entry _)

theorem scalar_tag_congr {q r : PTm n} (h : Γ ⊢[PRAAx] q ≐ r) : Γ ⊢[PRAAx] scalarTag q ≐ scalarTag r := by
  simpa [QuadraticRationalSignDispatch.subst_scalarTag] using Prf.eqCongr (scalarTag (var 0) : PTm 1)
    (σ := ![q]) (σ' := ![r]) (fun i => by fin_cases i; exact h)
theorem zero_test_congr {q r : PTm n} (h : Γ ⊢[PRAAx] q ≐ r) : Γ ⊢[PRAAx] eqb q zero ≐ eqb r zero := by
  simpa using Prf.eqCongr (eqb (var 0) zero : PTm 1)
    (σ := ![q]) (σ' := ![r]) (fun i => by fin_cases i; exact h)

theorem norm_pair (d a b : PTm n) : Γ ⊢[PRAAx]
    QuadraticRationalSignDispatch.norm d (pairT a b) ≐
      RationalArithmetic.add (RationalArithmetic.multiply a a)
        (RationalArithmetic.negative (RationalArithmetic.multiply d (RationalArithmetic.multiply b b))) :=
  RationalAlgebra.add_congr (RationalAlgebra.multiply_congr (fst_pair _ _) (fst_pair _ _))
    (RationalAlgebra.negative_congr (RationalAlgebra.multiply_congr (.eqRefl _)
      (RationalAlgebra.multiply_congr (snd_pair _ _) (snd_pair _ _))))

/-- Every native scalar in the computed norm is obtained by the actual
ground multiplication-table program, with its genuine operand bounds. -/
theorem actual_norm_head (B D A : PTm n) (hd : Γ ⊢[PRAAx] radicandsHeight D one B)
    (ha : Γ ⊢[PRAAx] arrayHeight one A B) : Γ ⊢[PRAAx]
    entry (QuadraticTowerSignRecipe.norm zero B D A) zero ≐
      QuadraticRationalSignDispatch.norm (radicand D) (coefficients A) := by
  let K := budget zero B D
  let a := leftHalf zero A
  let b := rightHalf zero A
  let bb := QuadraticTowerMultiplicationTable.query zero K D b b
  have bK := QuadraticTowerSignEmbedding.budget_inflation (Γ := Γ) zero B D
  have aH := QuadraticTowerMultiplicationHeight.left_height (Γ := Γ) zero A B ha
  have bH := QuadraticTowerMultiplicationHeight.right_height (Γ := Γ) zero A B ha
  have aa := ground_product_head K D a a (array_mono _ _ _ _ aH bK) (array_mono _ _ _ _ aH bK)
  have bbEq := ground_product_head K D b b (array_mono _ _ _ _ bH bK) (array_mono _ _ _ _ bH bK)
  have lowerD := QuadraticTowerMultiplicationHeight.radicands_prefix D zero one B hd (zero_le one)
  have bbH := QuadraticTowerMultiplicationHeight.query_height zero K D b b B bK lowerD bH bH
  have bbK := array_mono _ _ _ _ bbH (QuadraticTowerGrowth.lower_path_budget zero B D B (le_refl B))
  have dH := array_mono _ _ _ _ (QuadraticTowerMultiplicationHeight.radicand_at D one B zero hd (le_refl one)) bK
  have dbb := ground_product_head K D (entry D zero) bb dH bbK
  have native := (QuadraticTowerCoefficientArithmetic.added_lookup zero _ _ zero QuadraticTowerCoefficientArithmetic.base_index).eqTrans
    (RationalAlgebra.add_congr aa
      ((QuadraticTowerCoefficientArithmetic.negated_lookup zero _ zero QuadraticTowerCoefficientArithmetic.base_index).eqTrans
        (RationalAlgebra.negative_congr (dbb.eqTrans (RationalAlgebra.multiply_congr (.eqRefl _) bbEq)))))
  exact native.eqTrans (norm_pair (radicand D) (entry a zero) (entry b zero)).eqSymm

theorem first_tag (B D A : PTm n) (ha : Γ ⊢[PRAAx] arrayHeight one A B) : Γ ⊢[PRAAx]
    firstTag zero B D (QuadraticTowerSignTable.table zero (budget zero B D) D) A ≐
      scalarTag (fstT (coefficients A)) :=
  (ground_read _ D _ (array_mono _ _ _ _ (QuadraticTowerMultiplicationHeight.left_height zero A B ha)
    (QuadraticTowerSignEmbedding.budget_inflation zero B D))).eqTrans
      (scalar_tag_congr (fst_pair _ _).eqSymm)

theorem second_tag (B D A : PTm n) (ha : Γ ⊢[PRAAx] arrayHeight one A B) : Γ ⊢[PRAAx]
    secondTag zero B D (QuadraticTowerSignTable.table zero (budget zero B D) D) A ≐
      scalarTag (sndT (coefficients A)) :=
  (ground_read _ D _ (array_mono _ _ _ _ (QuadraticTowerMultiplicationHeight.right_height zero A B ha)
    (QuadraticTowerSignEmbedding.budget_inflation zero B D))).eqTrans (scalar_tag_congr (snd_pair _ _).eqSymm)

theorem third_tag (B D A : PTm n) (hd : Γ ⊢[PRAAx] radicandsHeight D one B)
    (ha : Γ ⊢[PRAAx] arrayHeight one A B) : Γ ⊢[PRAAx]
    thirdTag zero B D (QuadraticTowerSignTable.table zero (budget zero B D) D) A ≐
      QuadraticRationalSignDispatch.third (radicand D) (coefficients A) := by
  let K := budget zero B D
  let S := QuadraticTowerSignTable.table zero K D
  let a := firstTag zero B D S A
  have ar : Γ ⊢[PRAAx] a ≐ scalarTag (fstT (coefficients A)) := first_tag B D A ha
  have ground := ground_read K D (thirdInput zero B D S A)
    (QuadraticTowerSignRecipe.third_input_fits zero B D S A B (le_refl B) hd ha)
  refine ground.eqTrans (.orE (Foundations.BoundedReflection.eqb_cases a zero) ?_ ?_)
  · let Δ := (eqb a zero ≐ zero) :: Γ
    have selected : Δ ⊢[PRAAx] thirdInput zero B D S A ≐ QuadraticTowerSignRecipe.norm zero B D A :=
      Foundations.GuardedTotalization.sel_zero Prf.hyp0
    have newGuard : Δ ⊢[PRAAx] eqb (scalarTag (fstT (coefficients A))) zero ≐ zero :=
      (zero_test_congr ar.wk).eqSymm.eqTrans Prf.hyp0
    exact (scalar_tag_congr ((entry_congr selected (.eqRefl _)).eqTrans (actual_norm_head B D A hd.wk ha.wk))).eqTrans
      (Foundations.GuardedTotalization.sel_zero newGuard).eqSymm
  · let Δ := (eqb a zero ≐ one) :: Γ
    have selected : Δ ⊢[PRAAx] thirdInput zero B D S A ≐ entry D zero :=
      Foundations.GuardedTotalization.sel_one Prf.hyp0
    have newGuard : Δ ⊢[PRAAx] eqb (scalarTag (fstT (coefficients A))) zero ≐ one :=
      (zero_test_congr ar.wk).eqSymm.eqTrans Prf.hyp0
    exact (scalar_tag_congr (entry_congr selected (.eqRefl _))).eqTrans
      (Foundations.GuardedTotalization.sel_one newGuard).eqSymm

theorem actual_recipe (B D A : PTm n) (hd : Γ ⊢[PRAAx] radicandsHeight D one B)
    (ha : Γ ⊢[PRAAx] arrayHeight one A B) : Γ ⊢[PRAAx]
    QuadraticTowerSignRecipe.recipe zero B D (QuadraticTowerSignTable.table zero (budget zero B D) D) A ≐
      QuadraticRationalSignDispatch.recipe (radicand D) (coefficients A) :=
  QuadraticTowerSignCoherence.dispatch_congr (first_tag B D A ha) (second_tag B D A ha) (third_tag B D A hd ha)

theorem normalized_height (B A : PTm n) (ha : Γ ⊢[PRAAx] arrayHeight one A B) : Γ ⊢[PRAAx]
    arrayHeight one (normalized one A) B :=
  QuadraticTowerMultiplicationHeight.array_congr (.eqRefl _)
    (QuadraticTowerArrayNormalization.restored_normalized one A B ha) (.eqRefl _)
      (QuadraticTowerMultiplicationHeight.restored_height one A B B ha (le_refl B))

/-- Correctness of the actual first-depth table query on every original
bounded array. Its mathematical pair consists of its real normalized halves. -/
theorem query_sign (B D A : PTm n) (hd : Γ ⊢[PRAAx] radicandsHeight D one B)
    (ha : Γ ⊢[PRAAx] arrayHeight one A B)
    (hn : Γ ⊢[PRAAx] QuadraticRationalNonnegativeRadicand.nonnegative (radicand D)) : Γ ⊢[PRAAx]
    QuadraticTowerSignTable.query one B D A ≐
      QuadraticRationalNonnegativeRadicand.sign (radicand D) (coefficients (normalized one A)) :=
  (QuadraticTowerSignTable.query_succ zero B D A ha).eqTrans
    ((actual_recipe B D _ hd (normalized_height B A ha)).eqTrans
      (QuadraticRationalSignDispatch.nonnegative_dispatch _ _ hn))

def scalarArray (q : PTm n) : PTm n := QuadraticTowerScalarArrays.scalarArray zero q
def inputArray (x : PTm n) : PTm n := Foundations.SequenceComposition.append (scalarArray (fstT x)) (scalarArray (sndT x))
def radicandArray (d : PTm n) : PTm n := QuadraticTowerCoefficients.singleton (scalarArray d)
@[simp] theorem subst_scalarArray {k : ℕ} (σ : Fin n → PTm k) (q : PTm n) :
    Syn.subst σ (scalarArray q) = scalarArray (Syn.subst σ q) := by simp [scalarArray]
@[simp] theorem subst_inputArray {k : ℕ} (σ : Fin n → PTm k) (x : PTm n) :
    Syn.subst σ (inputArray x) = inputArray (Syn.subst σ x) := by simp [inputArray]
@[simp] theorem subst_radicandArray {k : ℕ} (σ : Fin n → PTm k) (d : PTm n) :
    Syn.subst σ (radicandArray d) = radicandArray (Syn.subst σ d) := by simp [radicandArray]

theorem input_height (B x : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (ha : Γ ⊢[PRAAx] height (fstT x) B) (hb : Γ ⊢[PRAAx] height (sndT x) B) : Γ ⊢[PRAAx]
    arrayHeight one (inputArray x) B :=
  QuadraticTowerMultiplicationHeight.append_height zero _ _ B
    (QuadraticTowerScalarArrays.scalar_array_height zero _ B hB ha)
    (QuadraticTowerScalarArrays.scalar_array_height zero _ B hB hb)
    (QuadraticTowerScalarArrays.scalar_length zero _) (QuadraticTowerScalarArrays.scalar_length zero _)
theorem below_one (i : PTm n) (hi : Γ ⊢[PRAAx] lt i one) : Γ ⊢[PRAAx] i ≐ zero :=
  (monus_zero i).eqSymm.eqTrans ((succ_monus_succ i zero).eqSymm.eqTrans hi)
theorem radicand_height (B d : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hd : Γ ⊢[PRAAx] height d B) : Γ ⊢[PRAAx] radicandsHeight (radicandArray d) one B := by
  have bs : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift B) := by simpa [Fm.shift,Syn.shift] using hB.shift
  have ds : Γ.map Fm.shift ⊢[PRAAx] height (Syn.shift d) (Syn.shift B) := by simpa [Fm.shift,Syn.shift] using hd.shift
  refine .allI (.impI ?_)
  let Δ := lt (var 0) one :: Γ.map Fm.shift
  have iz : Δ ⊢[PRAAx] var 0 ≐ zero := below_one _ Prf.hyp0
  have stored : Δ ⊢[PRAAx] entry (radicandArray (Syn.shift d)) (var 0) ≐ scalarArray (Syn.shift d) :=
    (entry_congr (.eqRefl _) iz).eqTrans (QuadraticTowerCoefficients.singleton_entry _)
  simpa only [Δ,Syn.shift,subst_radicandArray,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using QuadraticTowerMultiplicationHeight.array_congr iz.eqSymm stored.eqSymm (.eqRefl _)
    (QuadraticTowerScalarArrays.scalar_array_height zero (Syn.shift d) (Syn.shift B) bs.wk ds.wk)

theorem radicand_entry (d : PTm n) : Γ ⊢[PRAAx] radicand (radicandArray d) ≐ RationalArithmetic.recode d :=
  (entry_congr (QuadraticTowerCoefficients.singleton_entry _) (.eqRefl _)).eqTrans
    (QuadraticTowerScalarArrays.scalar_at_zero zero d)
theorem scalar_head (q : PTm n) : Γ ⊢[PRAAx] entry (scalarArray q) zero ≐ RationalArithmetic.recode q :=
  QuadraticTowerScalarArrays.scalar_at_zero zero q
theorem scalar_length (q : PTm n) : Γ ⊢[PRAAx] Foundations.SequenceComposition.length (scalarArray q) ≐ QuadraticTowerCoefficients.width zero :=
  QuadraticTowerScalarArrays.scalar_length zero q

theorem input_left_head (x : PTm n) : Γ ⊢[PRAAx]
    entry (leftHalf zero (inputArray x)) zero ≐ RationalArithmetic.recode (fstT x) := by
  have index : Γ ⊢[PRAAx] lt zero (Foundations.SequenceComposition.length (scalarArray (fstT x))) :=
    lt_congr (.eqRefl _) (scalar_length _).eqSymm QuadraticTowerCoefficientArithmetic.base_index
  exact (Foundations.RealizerComposition.slice_lookup _ zero _ zero QuadraticTowerCoefficientArithmetic.base_index).eqTrans
    ((entry_congr (.eqRefl _) (zero_add zero)).eqTrans ((Foundations.SequenceComposition.append_left index).eqTrans (scalar_head _)))
theorem input_right_head (x : PTm n) : Γ ⊢[PRAAx]
    entry (rightHalf zero (inputArray x)) zero ≐ RationalArithmetic.recode (sndT x) := by
  have index : Γ ⊢[PRAAx] lt zero (Foundations.SequenceComposition.length (scalarArray (sndT x))) :=
    lt_congr (.eqRefl _) (scalar_length _).eqSymm QuadraticTowerCoefficientArithmetic.base_index
  exact (Foundations.RealizerComposition.slice_lookup _ _ _ zero QuadraticTowerCoefficientArithmetic.base_index).eqTrans
    ((entry_congr (.eqRefl _) (congrAdd (scalar_length _).eqSymm (.eqRefl zero))).eqTrans
      ((Foundations.SequenceComposition.append_right index).eqTrans (scalar_head _)))

theorem normalized_input_left_head (x : PTm n) : Γ ⊢[PRAAx]
    entry (leftHalf zero (normalized one (inputArray x))) zero ≐ RationalArithmetic.recode (fstT x) :=
  (entry_congr (QuadraticTowerArrayNormalization.left_half_normalized zero _) (.eqRefl _)).eqTrans
    ((QuadraticTowerArrayCodec.normalized_lookup zero _ zero QuadraticTowerCoefficientArithmetic.base_index).eqTrans
      ((QuadraticTowerArrayNormalization.recode_congr (input_left_head x)).eqTrans
        (RationalNormalForm.normalize_fixed_point _ (RationalArithmetic.recode_guard _))))
theorem normalized_input_right_head (x : PTm n) : Γ ⊢[PRAAx]
    entry (rightHalf zero (normalized one (inputArray x))) zero ≐ RationalArithmetic.recode (sndT x) :=
  (entry_congr (QuadraticTowerArrayNormalization.right_half_normalized zero _) (.eqRefl _)).eqTrans
    ((QuadraticTowerArrayCodec.normalized_lookup zero _ zero QuadraticTowerCoefficientArithmetic.base_index).eqTrans
      ((QuadraticTowerArrayNormalization.recode_congr (input_right_head x)).eqTrans
        (RationalNormalForm.normalize_fixed_point _ (RationalArithmetic.recode_guard _))))

theorem input_coefficients_proper (x : PTm n) : Γ ⊢[PRAAx]
    QuadraticRationalClearing.sameCoefficients (coefficients (normalized one (inputArray x))) x :=
  .andI (RationalArgmin.rationalEq_congr ((fst_pair _ _).eqTrans (normalized_input_left_head x)).eqSymm (.eqRefl _) (RationalArithmetic.recode_equal _))
    (RationalArgmin.rationalEq_congr ((snd_pair _ _).eqTrans (normalized_input_right_head x)).eqSymm (.eqRefl _) (RationalArithmetic.recode_equal _))
theorem radicand_proper (d : PTm n) : Γ ⊢[PRAAx] RationalArgmin.rationalEq (radicand (radicandArray d)) d :=
  RationalArgmin.rationalEq_congr (radicand_entry d).eqSymm (.eqRefl _) (RationalArithmetic.recode_equal d)

/-- Original raw rational inputs supply every storage, address and
mathematical hypothesis of the SAME actual first-extension sign query. -/
theorem original_query (B d x : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hd : Γ ⊢[PRAAx] height d B) (ha : Γ ⊢[PRAAx] height (fstT x) B) (hb : Γ ⊢[PRAAx] height (sndT x) B)
    (hn : Γ ⊢[PRAAx] QuadraticRationalNonnegativeRadicand.nonnegative d) : Γ ⊢[PRAAx]
    QuadraticTowerSignTable.query one B (radicandArray d) (inputArray x) ≐ QuadraticRationalNonnegativeRadicand.sign d x := by
  have nativeNonnegative := QuadraticRationalRepresentationInvariance.nonnegative_congr d (radicand (radicandArray d)) hn (radicand_proper d).eqSymm
  exact (query_sign B _ _ (radicand_height B d hB hd) (input_height B x hB ha hb) nativeNonnegative).eqTrans
    (QuadraticRationalRepresentationInvariance.representation_invariance _ d _ x nativeNonnegative (radicand_proper d) (input_coefficients_proper x))

theorem original_returned_sign (B d x : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hd : Γ ⊢[PRAAx] height d B) (ha : Γ ⊢[PRAAx] height (fstT x) B) (hb : Γ ⊢[PRAAx] height (sndT x) B)
    (hn : Γ ⊢[PRAAx] QuadraticRationalNonnegativeRadicand.nonnegative d) : Γ ⊢[PRAAx]
    fstT (QuadraticTowerSignTable.run one B (radicandArray d) (inputArray x)) ≐ QuadraticRationalNonnegativeRadicand.sign d x :=
  (QuadraticTowerSignTable.returned_tag _ _ _ _).eqTrans (original_query B d x hB hd ha hb hn)

def output (B d x : PTm n) : PTm n := pairT (QuadraticTowerSignTable.query one B (radicandArray d) (inputArray x))
  (pairT (QuadraticRationalNonnegativeRadicand.sign d x) (pairT (inputArray x) (radicandArray d)))
def outputF : PR 3 := PTm.toPR (output (var 0) (var 1) (var 2))
def run (B d x : PTm n) : PTm n := ap3 outputF B d x
@[simp] theorem subst_output {k : ℕ} (σ : Fin n → PTm k) (B d x : PTm n) :
    Syn.subst σ (output B d x) = output (Syn.subst σ B) (Syn.subst σ d) (Syn.subst σ x) := by simp [output]
@[simp] theorem subst_run {k : ℕ} (σ : Fin n → PTm k) (B d x : PTm n) :
    Syn.subst σ (run B d x) = run (Syn.subst σ B) (Syn.subst σ d) (Syn.subst σ x) := by simp [run]
theorem program_at (B d x : PTm n) : Γ ⊢[PRAAx] run B d x ≐ output B d x := by
  simpa [run,outputF,ap3] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) : PTm 3) ![B,d,x]
theorem returned_query (B d x : PTm n) : Γ ⊢[PRAAx] fstT (run B d x) ≐ QuadraticTowerSignTable.query one B (radicandArray d) (inputArray x) :=
  (congrFst (program_at B d x)).eqTrans (fst_pair _ _)
theorem returned_tail (B d x : PTm n) : Γ ⊢[PRAAx] sndT (run B d x) ≐
    pairT (QuadraticRationalNonnegativeRadicand.sign d x) (pairT (inputArray x) (radicandArray d)) :=
  (congrSnd (program_at B d x)).eqTrans (snd_pair _ _)
theorem returned_source (B d x : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run B d x)) ≐ QuadraticRationalNonnegativeRadicand.sign d x :=
  (congrFst (returned_tail B d x)).eqTrans (fst_pair _ _)
theorem returned_arrays (B d x : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run B d x)) ≐ pairT (inputArray x) (radicandArray d) :=
  (congrSnd (returned_tail B d x)).eqTrans (snd_pair _ _)
theorem returned_input (B d x : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run B d x))) ≐ inputArray x :=
  (congrFst (returned_arrays B d x)).eqTrans (fst_pair _ _)
theorem returned_radicands (B d x : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (run B d x))) ≐ radicandArray d :=
  (congrSnd (returned_arrays B d x)).eqTrans (snd_pair _ _)
theorem returned_equal (B d x : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hd : Γ ⊢[PRAAx] height d B) (ha : Γ ⊢[PRAAx] height (fstT x) B) (hb : Γ ⊢[PRAAx] height (sndT x) B)
    (hn : Γ ⊢[PRAAx] QuadraticRationalNonnegativeRadicand.nonnegative d) : Γ ⊢[PRAAx]
    fstT (run B d x) ≐ fstT (sndT (run B d x)) :=
  (returned_query B d x).eqTrans ((original_query B d x hB hd ha hb hn).eqTrans (returned_source B d x).eqSymm)

theorem actual_first_extension_norm_head_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (radicandsHeight (var 1) one (var 0) ⟶ arrayHeight one (var 2) (var 0) ⟶
      entry (QuadraticTowerSignRecipe.norm zero (var 0) (var 1) (var 2)) zero ≐
        QuadraticRationalSignDispatch.norm (radicand (var 1)) (coefficients (var 2))) :=
  closeUniv 3 (.impI (.impI (actual_norm_head _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_first_extension_recipe_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (radicandsHeight (var 1) one (var 0) ⟶ arrayHeight one (var 2) (var 0) ⟶
      QuadraticTowerSignRecipe.recipe zero (var 0) (var 1) (QuadraticTowerSignTable.table zero (budget zero (var 0) (var 1)) (var 1)) (var 2) ≐
        QuadraticRationalSignDispatch.recipe (radicand (var 1)) (coefficients (var 2))) :=
  closeUniv 3 (.impI (.impI (actual_recipe _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_bounded_first_extension_query_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (radicandsHeight (var 1) one (var 0) ⟶ arrayHeight one (var 2) (var 0) ⟶
      QuadraticRationalNonnegativeRadicand.nonnegative (radicand (var 1)) ⟶
        QuadraticTowerSignTable.query one (var 0) (var 1) (var 2) ≐
          QuadraticRationalNonnegativeRadicand.sign (radicand (var 1)) (coefficients (normalized one (var 2)))) :=
  closeUniv 3 (.impI (.impI (.impI (query_sign _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))
theorem actual_first_extension_input_height_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le one (var 0) ⟶ height (fstT (var 1)) (var 0) ⟶ height (sndT (var 1)) (var 0) ⟶ arrayHeight one (inputArray (var 1)) (var 0)) :=
  closeUniv 2 (.impI (.impI (.impI (input_height _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))
theorem actual_first_extension_radicand_height_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le one (var 0) ⟶ height (var 1) (var 0) ⟶ radicandsHeight (radicandArray (var 1)) one (var 0)) :=
  closeUniv 2 (.impI (.impI (radicand_height _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_original_first_extension_sign_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 0) ⟶ height (var 1) (var 0) ⟶ height (fstT (var 2)) (var 0) ⟶ height (sndT (var 2)) (var 0) ⟶
      QuadraticRationalNonnegativeRadicand.nonnegative (var 1) ⟶
        QuadraticTowerSignTable.query one (var 0) (radicandArray (var 1)) (inputArray (var 2)) ≐ QuadraticRationalNonnegativeRadicand.sign (var 1) (var 2)) :=
  closeUniv 3 (.impI (.impI (.impI (.impI (.impI (original_query _ _ _
    (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp))))))))
theorem actual_original_returned_first_extension_sign_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 0) ⟶ height (var 1) (var 0) ⟶ height (fstT (var 2)) (var 0) ⟶ height (sndT (var 2)) (var 0) ⟶
      QuadraticRationalNonnegativeRadicand.nonnegative (var 1) ⟶
        fstT (QuadraticTowerSignTable.run one (var 0) (radicandArray (var 1)) (inputArray (var 2))) ≐ QuadraticRationalNonnegativeRadicand.sign (var 1) (var 2)) :=
  closeUniv 3 (.impI (.impI (.impI (.impI (.impI (original_returned_sign _ _ _
    (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp))))))))
theorem actual_first_extension_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (run (var 0) (var 1) (var 2) ≐ output (var 0) (var 1) (var 2)) := closeUniv 3 (program_at _ _ _)
theorem actual_first_extension_produced_equal_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 0) ⟶ height (var 1) (var 0) ⟶ height (fstT (var 2)) (var 0) ⟶ height (sndT (var 2)) (var 0) ⟶
      QuadraticRationalNonnegativeRadicand.nonnegative (var 1) ⟶ fstT (run (var 0) (var 1) (var 2)) ≐ fstT (sndT (run (var 0) (var 1) (var 2)))) :=
  closeUniv 3 (.impI (.impI (.impI (.impI (.impI (returned_equal _ _ _
    (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp))))))))

end LeanProofs.IPRA.Algebra.QuadraticTowerFirstExtensionSign
