import IPRADerivations.Algebra.QuadraticTowerMultiplicationRecurrence
import IPRADerivations.Algebra.QuadraticTowerFirstExtensionSign

/-!
# Semantic sign-zero products of the actual first extension

This is the first non-scalar stage, with arbitrary original raw bounded
arrays and nonnegative decoded rational radicand. Actual multiplication
and sign queries, their independent numerical caps and computed values
are retained. The arbitrary-depth ordered-quotient provider is separate.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Algebra.QuadraticTowerFirstExtensionIdeal

open_ipra
open LeanProofs.IPRA.Analysis
open QuadraticTowerArrayCodec (arrayHeight normalized)
open QuadraticTowerScalarBudget (height growth)
open QuadraticTowerCoefficientArithmetic (added)
open QuadraticTowerMultiplicationTable (budget leftHalf rightHalf query)
open QuadraticTowerMultiplicationHeight (radicandsHeight)
open QuadraticTowerFirstExtensionSign (coefficients radicand)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length append entry_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem left_head (A : PTm n) : Γ ⊢[PRAAx] entry (leftHalf zero A) zero ≐ entry A zero :=
  (Foundations.RealizerComposition.slice_lookup A zero _ zero QuadraticTowerCoefficientArithmetic.base_index).eqTrans
    (entry_congr (.eqRefl _) (zero_add zero))
theorem right_head (A : PTm n) : Γ ⊢[PRAAx] entry (rightHalf zero A) zero ≐ entry A one :=
  (Foundations.RealizerComposition.slice_lookup A (QuadraticTowerCoefficients.width zero) _ zero
    QuadraticTowerCoefficientArithmetic.base_index).eqTrans
      (entry_congr (.eqRefl _) ((add_zero _).eqTrans QuadraticTowerCoefficients.width_zero))

theorem native_product_pair (d a b c e : PTm n) : Γ ⊢[PRAAx]
    QuadraticRationalRadicand.multiply d (pairT a b) (pairT c e) ≐
      pairT (RationalArithmetic.add (RationalArithmetic.multiply a c) (RationalArithmetic.multiply d (RationalArithmetic.multiply b e)))
        (RationalArithmetic.add (RationalArithmetic.multiply a e) (RationalArithmetic.multiply b c)) :=
  congrPairT (RationalAlgebra.add_congr (RationalAlgebra.multiply_congr (fst_pair _ _) (fst_pair _ _))
    (RationalAlgebra.multiply_congr (.eqRefl d) (RationalAlgebra.multiply_congr (snd_pair _ _) (snd_pair _ _))))
    (RationalAlgebra.add_congr (RationalAlgebra.multiply_congr (fst_pair _ _) (snd_pair _ _))
      (RationalAlgebra.multiply_congr (snd_pair _ _) (fst_pair _ _)))

theorem coefficients_normalized (A : PTm n) : Γ ⊢[PRAAx]
    QuadraticRationalClearing.sameCoefficients (coefficients (normalized one A)) (coefficients A) := by
  have left : Γ ⊢[PRAAx] entry (leftHalf zero (normalized one A)) zero ≐ RationalArithmetic.recode (entry (leftHalf zero A) zero) :=
    (entry_congr (QuadraticTowerArrayNormalization.left_half_normalized zero A) (.eqRefl zero)).eqTrans
      (QuadraticTowerArrayCodec.normalized_lookup _ _ _ QuadraticTowerCoefficientArithmetic.base_index)
  have right : Γ ⊢[PRAAx] entry (rightHalf zero (normalized one A)) zero ≐ RationalArithmetic.recode (entry (rightHalf zero A) zero) :=
    (entry_congr (QuadraticTowerArrayNormalization.right_half_normalized zero A) (.eqRefl zero)).eqTrans
      (QuadraticTowerArrayCodec.normalized_lookup _ _ _ QuadraticTowerCoefficientArithmetic.base_index)
  exact .andI (RationalArgmin.rationalEq_congr ((fst_pair _ _).eqTrans left).eqSymm (fst_pair _ _).eqSymm (RationalArithmetic.recode_equal _))
    (RationalArgmin.rationalEq_congr ((snd_pair _ _).eqTrans right).eqSymm (snd_pair _ _).eqSymm (RationalArithmetic.recode_equal _))

/-- The actual sign scheduler at depth one reads the original raw pair
values; coefficient normalization is discharged by a proved provider. -/
theorem query_sign_original (S D A : PTm n) (hD : Γ ⊢[PRAAx] radicandsHeight D one S)
    (ha : Γ ⊢[PRAAx] arrayHeight one A S)
    (hn : Γ ⊢[PRAAx] QuadraticRationalNonnegativeRadicand.nonnegative (radicand D)) : Γ ⊢[PRAAx]
    QuadraticTowerSignTable.query one S D A ≐ QuadraticRationalNonnegativeRadicand.sign (radicand D) (coefficients A) :=
  (QuadraticTowerFirstExtensionSign.query_sign S D A hD ha hn).eqTrans
    (QuadraticRationalRepresentationInvariance.same_coefficients_sign _ _ _ hn (coefficients_normalized A))

/-- Both returned coefficients are derived from the SAME five actual
lower products, including the real computed be third operand. -/
theorem product_coefficients (M D A C b : PTm n) (hb : Γ ⊢[PRAAx] le b M)
    (hD : Γ ⊢[PRAAx] radicandsHeight D one b) (ha : Γ ⊢[PRAAx] arrayHeight one A b)
    (hc : Γ ⊢[PRAAx] arrayHeight one C b) : Γ ⊢[PRAAx]
    coefficients (query one M D A C) ≐ QuadraticRationalRadicand.multiply (radicand D) (coefficients A) (coefficients C) := by
  let K := budget zero M D
  let a := leftHalf zero A
  let c := leftHalf zero C
  let v := rightHalf zero A
  let w := rightHalf zero C
  let ac := query zero K D a c
  let be := query zero K D v w
  let bed := query zero K D be (entry D zero)
  let ae := query zero K D a w
  let bc := query zero K D v c
  let L := added zero ac bed
  let R := added zero ae bc
  have bK := le_trans hb (QuadraticTowerSignEmbedding.budget_inflation zero M D)
  have aH := QuadraticTowerMultiplicationHeight.left_height zero A b ha
  have cH := QuadraticTowerMultiplicationHeight.left_height zero C b hc
  have vH := QuadraticTowerMultiplicationHeight.right_height zero A b ha
  have wH := QuadraticTowerMultiplicationHeight.right_height zero C b hc
  have ground (X Y : PTm n) (hx : Γ ⊢[PRAAx] arrayHeight zero X b) (hy : Γ ⊢[PRAAx] arrayHeight zero Y b) : Γ ⊢[PRAAx]
      entry (query zero K D X Y) zero ≐ RationalArithmetic.multiply (entry X zero) (entry Y zero) :=
    QuadraticTowerFirstExtensionSign.ground_product_head K D X Y
      (QuadraticTowerMultiplicationHeight.array_mono _ _ _ _ hx bK) (QuadraticTowerMultiplicationHeight.array_mono _ _ _ _ hy bK)
  have acHead := ground a c aH cH
  have beHead := ground v w vH wH
  have aeHead := ground a w aH wH
  have bcHead := ground v c vH cH
  have lowerD := QuadraticTowerMultiplicationHeight.radicands_prefix D zero one b hD (zero_le one)
  have beH := QuadraticTowerMultiplicationHeight.query_height zero K D v w b bK lowerD vH wH
  have beK := QuadraticTowerMultiplicationHeight.array_mono _ _ _ _ beH (QuadraticTowerGrowth.lower_path_budget zero M D b hb)
  have dK := QuadraticTowerMultiplicationHeight.array_mono _ _ _ _
    (QuadraticTowerMultiplicationHeight.radicand_at D one b zero hD (le_refl one)) bK
  have bedHead := (QuadraticTowerFirstExtensionSign.ground_product_head K D be (entry D zero) beK dK).eqTrans
    ((RationalAlgebra.multiply_congr beHead (.eqRefl _)).eqTrans (RationalAlgebra.multiply_commutative _ _))
  have Lhead := (QuadraticTowerCoefficientArithmetic.added_lookup zero ac bed zero QuadraticTowerCoefficientArithmetic.base_index).eqTrans
    (RationalAlgebra.add_congr acHead bedHead)
  have Rhead := (QuadraticTowerCoefficientArithmetic.added_lookup zero ae bc zero QuadraticTowerCoefficientArithmetic.base_index).eqTrans
    (RationalAlgebra.add_congr aeHead bcHead)
  have produced : Γ ⊢[PRAAx] query one M D A C ≐ append L R :=
    QuadraticTowerMultiplicationRecurrence.query_succ_original zero M D A C
      (QuadraticTowerMultiplicationHeight.array_mono _ _ _ _ ha hb) (QuadraticTowerMultiplicationHeight.array_mono _ _ _ _ hc hb)
  have lenL : Γ ⊢[PRAAx] length L ≐ one :=
    (QuadraticTowerCoefficientArithmetic.added_length _ _ _).eqTrans QuadraticTowerCoefficients.width_zero
  have lenR : Γ ⊢[PRAAx] length R ≐ one :=
    (QuadraticTowerCoefficientArithmetic.added_length _ _ _).eqTrans QuadraticTowerCoefficients.width_zero
  have first := (left_head (query one M D A C)).eqTrans ((entry_congr produced (.eqRefl zero)).eqTrans
    ((Foundations.SequenceComposition.append_left (Order.zero_lt_of_eq_succ lenL)).eqTrans Lhead))
  have atRight : Γ ⊢[PRAAx] one ≐ length L+zero :=
    ((add_zero one).eqSymm).eqTrans (congrAdd lenL.eqSymm (.eqRefl zero))
  have second := (right_head (query one M D A C)).eqTrans ((entry_congr produced atRight).eqTrans
    ((Foundations.SequenceComposition.append_right (Order.zero_lt_of_eq_succ lenR)).eqTrans Rhead))
  exact (congrPairT first second).eqTrans (native_product_pair (radicand D) (entry a zero) (entry v zero) (entry c zero) (entry w zero)).eqSymm

theorem native_sign_code_congr (d : PTm n) {x y : PTm n} (e : Γ ⊢[PRAAx] x ≐ y) : Γ ⊢[PRAAx]
    QuadraticRationalNonnegativeRadicand.sign d x ≐ QuadraticRationalNonnegativeRadicand.sign d y := by
  ipra_congr (QuadraticRationalNonnegativeRadicand.sign (var 0) (var 1) : PTm 2) with [.eqRefl d, e]

theorem projection_sign_code_congr {x y : PTm n} (e : Γ ⊢[PRAAx] x ≐ y) : Γ ⊢[PRAAx]
    QuadraticRationalZeroProjection.sign x ≐ QuadraticRationalZeroProjection.sign y := by
  ipra_congr (QuadraticRationalZeroProjection.sign (var 0) : PTm 1) with [e]

theorem native_zero_multiply (d x y : PTm n)
    (hn : Γ ⊢[PRAAx] QuadraticRationalNonnegativeRadicand.nonnegative d)
    (hx : Γ ⊢[PRAAx] QuadraticRationalNonnegativeRadicand.isZero d x) : Γ ⊢[PRAAx]
    QuadraticRationalNonnegativeRadicand.isZero d (QuadraticRationalRadicand.multiply d x y) := by
  refine .orE (QuadraticRationalNonnegativeRadicand.radicand_cases d hn) ?_ ?_
  · have hp : (QuadraticRationalRadicand.isPositive d) :: Γ ⊢[PRAAx] QuadraticRationalRadicand.isPositive d := Prf.hyp0
    exact (QuadraticRationalNonnegativeRadicand.positive_branch d _ hp).eqTrans
      (QuadraticRationalRadicandOrder.zero_multiply d x y hp
        ((QuadraticRationalNonnegativeRadicand.positive_branch d x hp).eqSymm.eqTrans hx.wk))
  · have hz : (QuadraticRationalNonnegativeRadicand.radicandZero d) :: Γ ⊢[PRAAx]
        QuadraticRationalNonnegativeRadicand.radicandZero d := Prf.hyp0
    exact (QuadraticRationalNonnegativeRadicand.zero_branch d _ hz).eqTrans
      ((projection_sign_code_congr (QuadraticRationalNonnegativeRadicand.raw_zero_product d x y hz)).eqTrans
        (QuadraticRationalZeroProjection.zero_multiply x y
          ((QuadraticRationalNonnegativeRadicand.zero_branch d x hz).eqSymm.eqTrans hx.wk)))

def productBound (b : PTm n) : PTm n := growth (QuadraticTowerGrowth.path one) b
ipra_subst productBound

theorem source_input_sign (S D A b : PTm n) (hS : Γ ⊢[PRAAx] le (productBound b) S)
    (hD : Γ ⊢[PRAAx] radicandsHeight D one b) (ha : Γ ⊢[PRAAx] arrayHeight one A b)
    (hn : Γ ⊢[PRAAx] QuadraticRationalNonnegativeRadicand.nonnegative (radicand D)) : Γ ⊢[PRAAx]
    QuadraticTowerSignTable.query one S D A ≐ QuadraticRationalNonnegativeRadicand.sign (radicand D) (coefficients A) := by
  have bs := le_trans (QuadraticTowerGrowth.growth_inflation (QuadraticTowerGrowth.path one) b) hS
  exact query_sign_original S D A (QuadraticTowerMultiplicationHeight.radicands_mono _ _ _ _ hD bs)
    (QuadraticTowerMultiplicationHeight.array_mono _ _ _ _ ha bs) hn

/-- Mathematical sign correctness for the SAME actual computed product,
with separate actual multiplication and sign caps. -/
theorem product_sign (M S D A C b : PTm n) (hM : Γ ⊢[PRAAx] le b M)
    (hS : Γ ⊢[PRAAx] le (productBound b) S) (hD : Γ ⊢[PRAAx] radicandsHeight D one b)
    (ha : Γ ⊢[PRAAx] arrayHeight one A b) (hc : Γ ⊢[PRAAx] arrayHeight one C b)
    (hn : Γ ⊢[PRAAx] QuadraticRationalNonnegativeRadicand.nonnegative (radicand D)) : Γ ⊢[PRAAx]
    QuadraticTowerSignTable.query one S D (query one M D A C) ≐
      QuadraticRationalNonnegativeRadicand.sign (radicand D)
        (QuadraticRationalRadicand.multiply (radicand D) (coefficients A) (coefficients C)) := by
  have bs := le_trans (QuadraticTowerGrowth.growth_inflation (QuadraticTowerGrowth.path one) b) hS
  have heightP := QuadraticTowerMultiplicationHeight.query_height one M D A C b hM hD ha hc
  exact (query_sign_original S D _ (QuadraticTowerMultiplicationHeight.radicands_mono _ _ _ _ hD bs)
    (QuadraticTowerMultiplicationHeight.array_mono _ _ _ _ heightP hS) hn).eqTrans
      (native_sign_code_congr _ (product_coefficients M D A C b hM hD ha hc))

theorem zero_multiply (M S D A C b : PTm n) (hM : Γ ⊢[PRAAx] le b M)
    (hS : Γ ⊢[PRAAx] le (productBound b) S) (hD : Γ ⊢[PRAAx] radicandsHeight D one b)
    (ha : Γ ⊢[PRAAx] arrayHeight one A b) (hc : Γ ⊢[PRAAx] arrayHeight one C b)
    (hn : Γ ⊢[PRAAx] QuadraticRationalNonnegativeRadicand.nonnegative (radicand D))
    (hz : Γ ⊢[PRAAx] QuadraticTowerSignTable.query one S D A ≐ zero) : Γ ⊢[PRAAx]
    QuadraticTowerSignTable.query one S D (query one M D A C) ≐ zero :=
  (product_sign M S D A C b hM hS hD ha hc hn).eqTrans
    (native_zero_multiply _ _ _ hn ((source_input_sign S D A b hS hD ha hn).eqSymm.eqTrans hz))

theorem actual_sign_code_congr (S D : PTm n) {A C : PTm n} (e : Γ ⊢[PRAAx] A ≐ C) : Γ ⊢[PRAAx]
    QuadraticTowerSignTable.query one S D A ≐ QuadraticTowerSignTable.query one S D C := by
  ipra_congr (QuadraticTowerSignTable.query (var 0) (var 1) (var 2) (var 3) : PTm 4) with
    [.eqRefl one, .eqRefl S, .eqRefl D, e]

theorem zero_multiply_right (M S D A C b : PTm n) (hM : Γ ⊢[PRAAx] le b M)
    (hS : Γ ⊢[PRAAx] le (productBound b) S) (hD : Γ ⊢[PRAAx] radicandsHeight D one b)
    (ha : Γ ⊢[PRAAx] arrayHeight one A b) (hc : Γ ⊢[PRAAx] arrayHeight one C b)
    (hn : Γ ⊢[PRAAx] QuadraticRationalNonnegativeRadicand.nonnegative (radicand D))
    (hz : Γ ⊢[PRAAx] QuadraticTowerSignTable.query one S D C ≐ zero) : Γ ⊢[PRAAx]
    QuadraticTowerSignTable.query one S D (query one M D A C) ≐ zero :=
  (actual_sign_code_congr S D (QuadraticTowerMultiplicationCommutativity.query_commutative one M D A C b hM hD ha hc)).eqTrans
    (zero_multiply M S D C A b hM hS hD hc ha hn hz)

theorem zero_product_reflect (M S D A C b : PTm n) (hM : Γ ⊢[PRAAx] le b M)
    (hS : Γ ⊢[PRAAx] le (productBound b) S) (hD : Γ ⊢[PRAAx] radicandsHeight D one b)
    (ha : Γ ⊢[PRAAx] arrayHeight one A b) (hc : Γ ⊢[PRAAx] arrayHeight one C b)
    (hn : Γ ⊢[PRAAx] QuadraticRationalNonnegativeRadicand.nonnegative (radicand D))
    (hz : Γ ⊢[PRAAx] QuadraticTowerSignTable.query one S D (query one M D A C) ≐ zero) : Γ ⊢[PRAAx]
    (QuadraticTowerSignTable.query one S D A ≐ zero) ⋎ (QuadraticTowerSignTable.query one S D C ≐ zero) := by
  have native := QuadraticRationalNonnegativeRadicand.zero_product_reflect _ _ _ hn
    ((product_sign M S D A C b hM hS hD ha hc hn).eqSymm.eqTrans hz)
  exact .orE native (.orI₁ ((source_input_sign S D A b hS.wk hD.wk ha.wk hn.wk).eqTrans Prf.hyp0))
    (.orI₂ ((source_input_sign S D C b hS.wk hD.wk hc.wk hn.wk).eqTrans Prf.hyp0))

theorem zero_product_iff (M S D A C b : PTm n) (hM : Γ ⊢[PRAAx] le b M)
    (hS : Γ ⊢[PRAAx] le (productBound b) S) (hD : Γ ⊢[PRAAx] radicandsHeight D one b)
    (ha : Γ ⊢[PRAAx] arrayHeight one A b) (hc : Γ ⊢[PRAAx] arrayHeight one C b)
    (hn : Γ ⊢[PRAAx] QuadraticRationalNonnegativeRadicand.nonnegative (radicand D)) : Γ ⊢[PRAAx]
    Fm.iff (QuadraticTowerSignTable.query one S D (query one M D A C) ≐ zero)
      ((QuadraticTowerSignTable.query one S D A ≐ zero) ⋎ (QuadraticTowerSignTable.query one S D C ≐ zero)) :=
  .andI (.impI (zero_product_reflect M S D A C b hM.wk hS.wk hD.wk ha.wk hc.wk hn.wk Prf.hyp0))
    (.impI (.orE Prf.hyp0
      (zero_multiply M S D A C b hM.wk.wk hS.wk.wk hD.wk.wk ha.wk.wk hc.wk.wk hn.wk.wk Prf.hyp0)
      (zero_multiply_right M S D A C b hM.wk.wk hS.wk.wk hD.wk.wk ha.wk.wk hc.wk.wk hn.wk.wk Prf.hyp0)))

theorem positive_multiply (M S D A C b : PTm n) (hM : Γ ⊢[PRAAx] le b M)
    (hS : Γ ⊢[PRAAx] le (productBound b) S) (hD : Γ ⊢[PRAAx] radicandsHeight D one b)
    (ha : Γ ⊢[PRAAx] arrayHeight one A b) (hc : Γ ⊢[PRAAx] arrayHeight one C b)
    (hn : Γ ⊢[PRAAx] QuadraticRationalNonnegativeRadicand.nonnegative (radicand D))
    (hA : Γ ⊢[PRAAx] QuadraticTowerSignTable.query one S D A ≐ one)
    (hC : Γ ⊢[PRAAx] QuadraticTowerSignTable.query one S D C ≐ one) : Γ ⊢[PRAAx]
    QuadraticTowerSignTable.query one S D (query one M D A C) ≐ one :=
  (product_sign M S D A C b hM hS hD ha hc hn).eqTrans
    (QuadraticRationalNonnegativeRadicand.positive_multiply _ _ _ hn
      ((source_input_sign S D A b hS hD ha hn).eqSymm.eqTrans hA)
      ((source_input_sign S D C b hS hD hc hn).eqSymm.eqTrans hC))

def source (D A C b : PTm n) : Fm PTm n := radicandsHeight D one b ⋏
  (arrayHeight one A b ⋏ (arrayHeight one C b ⋏ QuadraticRationalNonnegativeRadicand.nonnegative (radicand D)))
def input (M S D A C b : PTm n) : Fm PTm n := le b M ⋏ (le (productBound b) S ⋏ source D A C b)
ipra_subst source [QuadraticRationalNonnegativeRadicand.nonnegative, radicand]
ipra_subst input

def output (b D A C : PTm n) : PTm n := pairT (query one b D A C)
  (pairT (QuadraticTowerSignTable.query one (productBound b) D (query one b D A C))
    (pairT (QuadraticTowerSignTable.query one (productBound b) D A)
      (pairT (QuadraticTowerSignTable.query one (productBound b) D C) (productBound b))))
def outputF : PR 4 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3))
def run (b D A C : PTm n) : PTm n := PTm.app outputF ![b,D,A,C]
ipra_subst output
ipra_subst run

theorem program_at (b D A C : PTm n) : Γ ⊢[PRAAx] run b D A C ≐ output b D A C := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) : PTm 4) ![b,D,A,C]
theorem returned_product (b D A C : PTm n) : Γ ⊢[PRAAx] fstT (run b D A C) ≐ query one b D A C :=
  (program_at _ _ _ _).fstE
theorem returned_tail (b D A C : PTm n) : Γ ⊢[PRAAx] sndT (run b D A C) ≐
    pairT (QuadraticTowerSignTable.query one (productBound b) D (query one b D A C))
      (pairT (QuadraticTowerSignTable.query one (productBound b) D A) (pairT (QuadraticTowerSignTable.query one (productBound b) D C) (productBound b))) :=
  (program_at _ _ _ _).sndE
theorem returned_product_tag (b D A C : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run b D A C)) ≐
    QuadraticTowerSignTable.query one (productBound b) D (query one b D A C) :=
  (returned_tail _ _ _ _).fstE
theorem returned_inputs (b D A C : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run b D A C)) ≐
    pairT (QuadraticTowerSignTable.query one (productBound b) D A) (pairT (QuadraticTowerSignTable.query one (productBound b) D C) (productBound b)) :=
  (returned_tail _ _ _ _).sndE
theorem returned_left_tag (b D A C : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run b D A C))) ≐
    QuadraticTowerSignTable.query one (productBound b) D A :=
  (returned_inputs _ _ _ _).fstE
theorem returned_right_pair (b D A C : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (run b D A C))) ≐
    pairT (QuadraticTowerSignTable.query one (productBound b) D C) (productBound b) :=
  (returned_inputs _ _ _ _).sndE
theorem returned_right_tag (b D A C : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (sndT (run b D A C)))) ≐
    QuadraticTowerSignTable.query one (productBound b) D C :=
  (returned_right_pair _ _ _ _).fstE
theorem returned_cap (b D A C : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (sndT (run b D A C)))) ≐ productBound b :=
  (returned_right_pair _ _ _ _).sndE

theorem returned_zero_iff (b D A C : PTm n) (h : Γ ⊢[PRAAx] source D A C b) : Γ ⊢[PRAAx]
    Fm.iff (fstT (sndT (run b D A C)) ≐ zero)
      ((fstT (sndT (sndT (run b D A C))) ≐ zero) ⋎ (fstT (sndT (sndT (sndT (run b D A C)))) ≐ zero)) := by
  have actual := zero_product_iff b (productBound b) D A C b (le_refl _) (le_refl _)
    h.andE₁ h.andE₂.andE₁ h.andE₂.andE₂.andE₁ h.andE₂.andE₂.andE₂
  have proof := Prf.eqSubst (Γ := Γ) (Ax := PRAAx)
    (Fm.iff (var 0 ≐ zero) ((var 1 ≐ zero) ⋎ (var 2 ≐ zero)) : Fm PTm 3)
    ![QuadraticTowerSignTable.query one (productBound b) D (query one b D A C),
      QuadraticTowerSignTable.query one (productBound b) D A,QuadraticTowerSignTable.query one (productBound b) D C]
    ![fstT (sndT (run b D A C)),fstT (sndT (sndT (run b D A C))),fstT (sndT (sndT (sndT (run b D A C))))]
    (fun i => by fin_cases i; exact (returned_product_tag _ _ _ _).eqSymm; exact (returned_left_tag _ _ _ _).eqSymm; exact (returned_right_tag _ _ _ _).eqSymm)
    (by simpa [Fm.iff] using actual)
  simpa [Fm.iff] using proof

theorem original_first_extension_product_coefficients_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le (var 4) (var 0) ⟶ radicandsHeight (var 1) one (var 4) ⟶ arrayHeight one (var 2) (var 4) ⟶ arrayHeight one (var 3) (var 4) ⟶
      coefficients (query one (var 0) (var 1) (var 2) (var 3)) ≐ QuadraticRationalRadicand.multiply (radicand (var 1)) (coefficients (var 2)) (coefficients (var 3))) :=
  closeUniv 5 (.impI (.impI (.impI (.impI (product_coefficients _ _ _ _ (var 4) (.hyp (by simp)) (.hyp (by simp)) Prf.hyp1 Prf.hyp0)))))
theorem original_first_extension_actual_product_sign_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
      QuadraticTowerSignTable.query one (var 1) (var 2) (query one (var 0) (var 2) (var 3) (var 4)) ≐
        QuadraticRationalNonnegativeRadicand.sign (radicand (var 2)) (QuadraticRationalRadicand.multiply (radicand (var 2)) (coefficients (var 3)) (coefficients (var 4)))) :=
  closeUniv 6 (.impI (product_sign _ _ _ _ _ (var 5) Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₂))
theorem original_first_extension_actual_zero_product_iff_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
      Fm.iff (QuadraticTowerSignTable.query one (var 1) (var 2) (query one (var 0) (var 2) (var 3) (var 4)) ≐ zero)
        ((QuadraticTowerSignTable.query one (var 1) (var 2) (var 3) ≐ zero) ⋎ (QuadraticTowerSignTable.query one (var 1) (var 2) (var 4) ≐ zero))) :=
  closeUniv 6 (.impI (zero_product_iff _ _ _ _ _ (var 5) Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₂))
theorem original_first_extension_actual_positive_product_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶ QuadraticTowerSignTable.query one (var 1) (var 2) (var 3) ≐ one ⟶
      QuadraticTowerSignTable.query one (var 1) (var 2) (var 4) ≐ one ⟶
        QuadraticTowerSignTable.query one (var 1) (var 2) (query one (var 0) (var 2) (var 3) (var 4)) ≐ one) := by
  refine closeUniv 6 (.impI (.impI (.impI ?_)))
  have h : [QuadraticTowerSignTable.query one (var 1) (var 2) (var 4) ≐ one,
      QuadraticTowerSignTable.query one (var 1) (var 2) (var 3) ≐ one,
      input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)] ⊢[PRAAx]
      input (var 0 : PTm 6) (var 1) (var 2) (var 3) (var 4) (var 5) := .hyp (by simp)
  exact positive_multiply _ _ _ _ _ (var 5) h.andE₁ h.andE₂.andE₁ h.andE₂.andE₂.andE₁ h.andE₂.andE₂.andE₂.andE₁
    h.andE₂.andE₂.andE₂.andE₂.andE₁ h.andE₂.andE₂.andE₂.andE₂.andE₂ Prf.hyp1 Prf.hyp0

theorem original_nonnegative_rational_native_zero_multiply_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (QuadraticRationalNonnegativeRadicand.nonnegative (var 0) ⟶ QuadraticRationalNonnegativeRadicand.isZero (var 0) (var 1) ⟶
      QuadraticRationalNonnegativeRadicand.isZero (var 0) (QuadraticRationalRadicand.multiply (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (.impI (native_zero_multiply _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_first_extension_ideal_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (run (var 0) (var 1) (var 2) (var 3) ≐ output (var 0) (var 1) (var 2) (var 3)) := closeUniv 4 (program_at _ _ _ _)
theorem actual_first_extension_ideal_returned_cap_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (sndT (sndT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3))))) ≐ productBound (var 0)) := closeUniv 4 (returned_cap _ _ _ _)
theorem original_computed_first_extension_zero_product_iff_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 1) (var 2) (var 3) (var 0) ⟶
      Fm.iff (fstT (sndT (run (var 0) (var 1) (var 2) (var 3))) ≐ zero)
        ((fstT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3)))) ≐ zero) ⋎
          (fstT (sndT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3))))) ≐ zero))) :=
  closeUniv 4 (.impI (returned_zero_iff _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Algebra.QuadraticTowerFirstExtensionIdeal
