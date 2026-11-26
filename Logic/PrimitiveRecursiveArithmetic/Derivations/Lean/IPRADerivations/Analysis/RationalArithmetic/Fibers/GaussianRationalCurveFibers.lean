import IPRADerivations.Analysis.RationalArithmetic.Fibers.GaussianRationalFiberGrouping
import IPRADerivations.Analysis.Polynomials.CompanionMatrices.GaussianPolynomialMonicCompanion
import IPRADerivations.Analysis.Polynomials.RootFinding.Reconstruction.GaussianRationalFiniteRoots

/-!
# Actual ordinate lists and specialized curve roots in each x fiber

Source05's finite norm proof starts with distinct FIELD-valued original
points and their actual F/G zero equations. Every original fiber position
is mapped to its original ordinate. Root transfer and ordinate distinction
are derived from exact x-value grouping; no root-list or distinct-output law
is supplied. The exact cardinal partition remains the sum of fiber sizes.
The determinant/factor-multiplicity argument is a separate source step.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalCurveFibers

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (evaluate horner hornerF qzero)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision (qone qsub_congr)
open LeanProofs.IPRA.Analysis.GaussianRationalFiberGrouping
  (abscissa ordinate fiber fiberCount groupCount representative member_abscissa)
open LeanProofs.IPRA.Analysis.GaussianRationalValueEquality
  (valueEqual subst_valueEqual value_equal_symm value_equal_trans evaluation_value_proper difference_zero_iff)
open LeanProofs.IPRA.Analysis.GaussianPolynomialMonicCompanion
  (values monicValues values_length values_lookup monic_length monic_head monic_tail)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (qsub)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem values_evaluation_proper (A m x x' y : PTm n) (h : Γ ⊢[PRAAx] valueEqual x x') : Γ ⊢[PRAAx]
    evaluate (values A m x) y ≐ evaluate (values A m x') y := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] valueEqual (Syn.shift x) (Syn.shift x') := by
    simpa only [Fm.shift,subst_valueEqual,Syn.shift] using h.shift
  have entries : Γ ⊢[PRAAx] .all (lt (var 0) (Syn.shift m) ⟶
      entry (Syn.shift (values A m x)) (var 0) ≐ entry (Syn.shift (values A m x')) (var 0)) := by
    refine .allI (.impI ?_)
    have hr : lt (var 0) (Syn.shift m) :: Γ.map Fm.shift ⊢[PRAAx] lt (var 0) (Syn.shift m) := Prf.hyp0
    have e := (values_lookup (Syn.shift A) (Syn.shift m) (Syn.shift x) (var 0) hr).eqTrans
      ((evaluation_value_proper _ _ _ hs.wk).eqTrans (values_lookup (Syn.shift A) (Syn.shift m) (Syn.shift x') (var 0) hr).eqSymm)
    simpa only [Syn.shift,GaussianPolynomialMonicCompanion.subst_values] using e
  exact (congrAp3 hornerF (values_length A m x) (.eqRefl _) (.eqRefl _)).eqTrans
    ((GaussianRationalLinearProduct.horner_ext _ _ _ m m entries (le_refl _)).eqTrans
      (congrAp3 hornerF (values_length A m x').eqSymm (.eqRefl _) (.eqRefl _)))

theorem monic_values_evaluation_proper (F m x x' y : PTm n) (h : Γ ⊢[PRAAx] valueEqual x x') : Γ ⊢[PRAAx]
    evaluate (monicValues F m x) y ≐ evaluate (monicValues F m x') y := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] valueEqual (Syn.shift x) (Syn.shift x') := by
    simpa only [Fm.shift,subst_valueEqual,Syn.shift] using h.shift
  have entries : Γ ⊢[PRAAx] .all (lt (var 0) (Syn.shift (succ m)) ⟶
      entry (Syn.shift (monicValues F m x)) (var 0) ≐ entry (Syn.shift (monicValues F m x')) (var 0)) := by
    refine .allI (.impI (.orE (zero_or_succ (var 0)) ?_ ?_))
    · have e := (entry_congr (.eqRefl _) (Prf.hyp0 : (var 0 ≐ zero) :: lt (var 0) (Syn.shift (succ m)) :: Γ.map Fm.shift ⊢[PRAAx] _)).eqTrans
        ((monic_head (Syn.shift F) (Syn.shift m) (Syn.shift x)).eqTrans
          ((monic_head (Syn.shift F) (Syn.shift m) (Syn.shift x')).eqSymm.eqTrans
            (entry_congr (.eqRefl _) Prf.hyp0.eqSymm)))
      simpa only [Syn.shift,GaussianPolynomialMonicCompanion.subst_monicValues] using e
    · let Δ := (var 0 ≐ succ (pred (var 0))) :: lt (var 0) (Syn.shift (succ m)) :: Γ.map Fm.shift
      have r : Δ ⊢[PRAAx] lt (pred (var 0)) (Syn.shift m) :=
        (succ_monus_succ _ _).eqSymm.eqTrans
          (lt_congr (Prf.hyp0 : Δ ⊢[PRAAx] _) (.eqRefl _) (by simpa only [Δ,Syn.shift,ConciseIPRA.PTm.subst_succ] using (Prf.hyp1 : Δ ⊢[PRAAx] _)))
      have e := (entry_congr (Γ := Δ) (.eqRefl _) Prf.hyp0).eqTrans
        ((monic_tail (Syn.shift F) (Syn.shift m) (Syn.shift x) (pred (var 0)) r).eqTrans
          ((evaluation_value_proper _ _ _ hs.wk.wk).eqTrans
            ((monic_tail (Syn.shift F) (Syn.shift m) (Syn.shift x') (pred (var 0)) r).eqSymm.eqTrans
              (entry_congr (.eqRefl _) Prf.hyp0.eqSymm))))
      simpa only [Δ,Syn.shift,GaussianPolynomialMonicCompanion.subst_monicValues] using e
  exact (congrAp3 hornerF (monic_length F m x) (.eqRefl _) (.eqRefl _)).eqTrans
    ((GaussianRationalLinearProduct.horner_ext _ _ _ (succ m) (succ m) entries (le_refl _)).eqTrans
      (congrAp3 hornerF (monic_length F m x').eqSymm (.eqRefl _) (.eqRefl _)))

def data (L p g : PTm n) : PTm n := pairT L (pairT p g)
def yBody : PTm 2 := ordinate (fstT (var 1))
  (entry (fiber (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1)))) (var 0))
def yList (L p g : PTm n) : PTm n := sequence yBody (fiberCount L p g) (data L p g)
def yListF : PR 3 := PTm.toPR (yList (var 0) (var 1) (var 2))
def yRun (L p g : PTm n) : PTm n := ap3 yListF L p g
@[simp] theorem subst_data {l : ℕ} (σ : Fin n → PTm l) (L p g : PTm n) :
    Syn.subst σ (data L p g) = data (Syn.subst σ L) (Syn.subst σ p) (Syn.subst σ g) := by simp [data]
@[simp] theorem subst_yList {l : ℕ} (σ : Fin n → PTm l) (L p g : PTm n) :
    Syn.subst σ (yList L p g) = yList (Syn.subst σ L) (Syn.subst σ p) (Syn.subst σ g) := by simp [yList]
@[simp] theorem subst_yRun {l : ℕ} (σ : Fin n → PTm l) (L p g : PTm n) :
    Syn.subst σ (yRun L p g) = yRun (Syn.subst σ L) (Syn.subst σ p) (Syn.subst σ g) := by simp [yRun]
theorem y_body_at (L p g r : PTm n) : Γ ⊢[PRAAx]
    inst2 yBody r (data L p g) ≐ ordinate L (entry (fiber L p g) r) := by
  simp only [yBody,inst2,GaussianRationalFiberGrouping.subst_ordinate,Foundations.MasterCertificate.subst_entry,
    Foundations.FiniteFiberGrouping.subst_fiber,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  apply congrSnd
  apply entry_congr (fst_pair L (pairT p g))
  apply entry_congr
  · apply Foundations.FiniteFiberGrouping.fiber_congr GaussianRationalFiberGrouping.xKeyF
      (fst_pair L (pairT p g))
      ((congrFst (snd_pair L (pairT p g))).eqTrans (fst_pair p g))
      ((congrSnd (snd_pair L (pairT p g))).eqTrans (snd_pair p g))
  · exact .eqRefl _
theorem y_length (L p g : PTm n) : Γ ⊢[PRAAx] length (yList L p g) ≐ fiberCount L p g :=
  Foundations.MasterCertificate.sequence_length _ _ _
theorem y_lookup (L p g r : PTm n) (hr : Γ ⊢[PRAAx] lt r (fiberCount L p g)) : Γ ⊢[PRAAx]
    entry (yList L p g) r ≐ ordinate L (entry (fiber L p g) r) :=
  (Foundations.MasterCertificate.sequence_decode yBody hr).eqTrans (y_body_at L p g r)
theorem y_program_at (L p g : PTm n) : Γ ⊢[PRAAx] yRun L p g ≐ yList L p g := by
  simpa [yRun,yListF,ap3] using toPR_eq (Γ := Γ) (yList (var 0) (var 1) (var 2)) ![L,p,g]

def pointDistinctFrom (L i : PTm n) : Fm PTm n := .all
  (lt (var 0) (length (Syn.shift L)) ⟶ lt (Syn.shift i) (var 0) ⟶
    neg (valueEqual (abscissa (Syn.shift L) (var 0)) (abscissa (Syn.shift L) (Syn.shift i)) ⋏
      valueEqual (ordinate (Syn.shift L) (var 0)) (ordinate (Syn.shift L) (Syn.shift i))))
def pointDistinct (L : PTm n) : Fm PTm n := .all
  (lt (var 0) (length (Syn.shift L)) ⟶ pointDistinctFrom (Syn.shift L) (var 0))
def curveZeros (F m L : PTm n) : Fm PTm n := .all
  (lt (var 0) (length (Syn.shift L)) ⟶
    evaluate (monicValues (Syn.shift F) (Syn.shift m) (abscissa (Syn.shift L) (var 0)))
      (ordinate (Syn.shift L) (var 0)) ≐ qzero)
def functionZeros (G m L : PTm n) : Fm PTm n := .all
  (lt (var 0) (length (Syn.shift L)) ⟶
    evaluate (values (Syn.shift G) (Syn.shift m) (abscissa (Syn.shift L) (var 0)))
      (ordinate (Syn.shift L) (var 0)) ≐ qzero)
@[simp] theorem subst_pointDistinctFrom {l : ℕ} (σ : Fin n → PTm l) (L i : PTm n) :
    (pointDistinctFrom L i).subst σ = pointDistinctFrom (Syn.subst σ L) (Syn.subst σ i) := by
  simp [pointDistinctFrom,Syn.subst_shift,Syn.shift_subst]
@[simp] theorem subst_pointDistinct {l : ℕ} (σ : Fin n → PTm l) (L : PTm n) :
    (pointDistinct L).subst σ = pointDistinct (Syn.subst σ L) := by simp [pointDistinct,Syn.subst_shift,Syn.shift_subst]
@[simp] theorem subst_curveZeros {l : ℕ} (σ : Fin n → PTm l) (F m L : PTm n) :
    (curveZeros F m L).subst σ = curveZeros (Syn.subst σ F) (Syn.subst σ m) (Syn.subst σ L) := by
  simp [curveZeros,Syn.subst_shift,Syn.shift_subst]
@[simp] theorem subst_functionZeros {l : ℕ} (σ : Fin n → PTm l) (G m L : PTm n) :
    (functionZeros G m L).subst σ = functionZeros (Syn.subst σ G) (Syn.subst σ m) (Syn.subst σ L) := by
  simp [functionZeros,Syn.subst_shift,Syn.shift_subst]

theorem point_distinct_at (L i j : PTm n) (h : Γ ⊢[PRAAx] pointDistinct L)
    (hi : Γ ⊢[PRAAx] lt i (length L)) (hj : Γ ⊢[PRAAx] lt j (length L)) (hij : Γ ⊢[PRAAx] lt i j) : Γ ⊢[PRAAx]
    neg (valueEqual (abscissa L j) (abscissa L i) ⋏ valueEqual (ordinate L j) (ordinate L i)) := by
  have outer : Γ ⊢[PRAAx] lt i (length L) ⟶ pointDistinctFrom L i := by
    simpa [pointDistinct] using h.allE i
  have inner := (Prf.impE outer hi).allE j
  have gate : Γ ⊢[PRAAx] lt j (length L) ⟶ lt i j ⟶
      neg (valueEqual (abscissa L j) (abscissa L i) ⋏ valueEqual (ordinate L j) (ordinate L i)) := by
    simpa [pointDistinctFrom,neg] using inner
  exact .impE (.impE gate hj) hij
theorem curve_at (F m L i : PTm n) (h : Γ ⊢[PRAAx] curveZeros F m L)
    (hi : Γ ⊢[PRAAx] lt i (length L)) : Γ ⊢[PRAAx]
    evaluate (monicValues F m (abscissa L i)) (ordinate L i) ≐ qzero := by
  have e : Γ ⊢[PRAAx] lt i (length L) ⟶ evaluate (monicValues F m (abscissa L i)) (ordinate L i) ≐ qzero := by
    simpa [curveZeros] using h.allE i
  exact .impE e hi
theorem function_at (G m L i : PTm n) (h : Γ ⊢[PRAAx] functionZeros G m L)
    (hi : Γ ⊢[PRAAx] lt i (length L)) : Γ ⊢[PRAAx]
    evaluate (values G m (abscissa L i)) (ordinate L i) ≐ qzero := by
  have e : Γ ⊢[PRAAx] lt i (length L) ⟶ evaluate (values G m (abscissa L i)) (ordinate L i) ≐ qzero := by
    simpa [functionZeros] using h.allE i
  exact .impE e hi

theorem fiber_index_bound (L p g r : PTm n) (hr : Γ ⊢[PRAAx] lt r (fiberCount L p g)) : Γ ⊢[PRAAx]
    lt (entry (fiber L p g) r) (length L) := Foundations.FiniteFiberGrouping.fiber_bound _ _ _ _ _ hr
theorem fiber_indices_increasing (L p g r s : PTm n)
    (hrs : Γ ⊢[PRAAx] lt r s) (hs : Γ ⊢[PRAAx] lt s (fiberCount L p g)) : Γ ⊢[PRAAx]
    lt (entry (fiber L p g) r) (entry (fiber L p g) s) :=
  Foundations.FiniteFiberGrouping.members_increasing _ _ _ _ _ _ hrs hs
theorem ordinate_distinct_at (L p g r s : PTm n) (h : Γ ⊢[PRAAx] pointDistinct L)
    (hr : Γ ⊢[PRAAx] lt r (fiberCount L p g)) (hs : Γ ⊢[PRAAx] lt s (fiberCount L p g))
    (hrs : Γ ⊢[PRAAx] lt r s) : Γ ⊢[PRAAx]
    neg (qsub (entry (yList L p g) s) (entry (yList L p g) r) ≐ qzero) := by
  have source := point_distinct_at L _ _ h (fiber_index_bound L p g r hr) (fiber_index_bound L p g s hs)
    (fiber_indices_increasing L p g r s hrs hs)
  have hx := value_equal_trans _ _ _ (member_abscissa L p g s hs)
    (value_equal_symm _ _ (member_abscissa L p g r hr))
  refine .impI (.impE source.wk (.andI hx.wk ?_))
  apply (difference_zero_iff _ _).iffMp
  exact (qsub_congr (y_lookup L p g s hs) (y_lookup L p g r hr)).wk.eqSymm.eqTrans Prf.hyp0

theorem curve_root_at (F m L p g r : PTm n) (h : Γ ⊢[PRAAx] curveZeros F m L)
    (hr : Γ ⊢[PRAAx] lt r (fiberCount L p g)) : Γ ⊢[PRAAx]
    evaluate (monicValues F m (abscissa L (representative L p g))) (entry (yList L p g) r) ≐ qzero :=
  (GaussianRationalFiniteRoots.evaluate_congr (.eqRefl _) (y_lookup L p g r hr)).eqTrans
    ((monic_values_evaluation_proper _ _ _ _ _ (member_abscissa L p g r hr)).eqSymm.eqTrans
      (curve_at F m L _ h (fiber_index_bound L p g r hr)))
theorem function_root_at (G m L p g r : PTm n) (h : Γ ⊢[PRAAx] functionZeros G m L)
    (hr : Γ ⊢[PRAAx] lt r (fiberCount L p g)) : Γ ⊢[PRAAx]
    evaluate (values G m (abscissa L (representative L p g))) (entry (yList L p g) r) ≐ qzero :=
  (GaussianRationalFiniteRoots.evaluate_congr (.eqRefl _) (y_lookup L p g r hr)).eqTrans
    ((values_evaluation_proper _ _ _ _ _ (member_abscissa L p g r hr)).eqSymm.eqTrans
      (function_at G m L _ h (fiber_index_bound L p g r hr)))

theorem fiber_curve_roots (F m L p g : PTm n) (h : Γ ⊢[PRAAx] curveZeros F m L) : Γ ⊢[PRAAx]
    GaussianRationalFiniteRoots.roots (monicValues F m (abscissa L (representative L p g))) (yList L p g) := by
  unfold GaussianRationalFiniteRoots.roots
  refine .allI (.impI ?_)
  have original : Γ.map Fm.shift ⊢[PRAAx] curveZeros (Syn.shift F) (Syn.shift m) (Syn.shift L) := by
    simpa only [Fm.shift,subst_curveZeros,Syn.shift] using h.shift
  have range : lt (var 0) (length (Syn.shift (yList L p g))) :: Γ.map Fm.shift ⊢[PRAAx]
      lt (var 0) (fiberCount (Syn.shift L) (Syn.shift p) (Syn.shift g)) :=
    lt_congr (.eqRefl _) (y_length _ _ _) (by simpa only [Syn.shift,subst_yList] using
      (Prf.hyp0 : lt (var 0) (length (Syn.shift (yList L p g))) :: Γ.map Fm.shift ⊢[PRAAx] _))
  simpa only [Syn.shift,GaussianPolynomialMonicCompanion.subst_monicValues,
    GaussianRationalFiberGrouping.subst_abscissa,Foundations.FiniteFiberGrouping.subst_representative,subst_yList] using
    curve_root_at (Syn.shift F) (Syn.shift m) (Syn.shift L) (Syn.shift p) (Syn.shift g) (var 0) original.wk range
theorem fiber_function_roots (G m L p g : PTm n) (h : Γ ⊢[PRAAx] functionZeros G m L) : Γ ⊢[PRAAx]
    GaussianRationalFiniteRoots.roots (values G m (abscissa L (representative L p g))) (yList L p g) := by
  unfold GaussianRationalFiniteRoots.roots
  refine .allI (.impI ?_)
  have original : Γ.map Fm.shift ⊢[PRAAx] functionZeros (Syn.shift G) (Syn.shift m) (Syn.shift L) := by
    simpa only [Fm.shift,subst_functionZeros,Syn.shift] using h.shift
  have range : lt (var 0) (length (Syn.shift (yList L p g))) :: Γ.map Fm.shift ⊢[PRAAx]
      lt (var 0) (fiberCount (Syn.shift L) (Syn.shift p) (Syn.shift g)) :=
    lt_congr (.eqRefl _) (y_length _ _ _) (by simpa only [Syn.shift,subst_yList] using
      (Prf.hyp0 : lt (var 0) (length (Syn.shift (yList L p g))) :: Γ.map Fm.shift ⊢[PRAAx] _))
  simpa only [Syn.shift,GaussianPolynomialMonicCompanion.subst_values,
    GaussianRationalFiberGrouping.subst_abscissa,Foundations.FiniteFiberGrouping.subst_representative,subst_yList] using
    function_root_at (Syn.shift G) (Syn.shift m) (Syn.shift L) (Syn.shift p) (Syn.shift g) (var 0) original.wk range

theorem fiber_ordinates_distinct (L p g : PTm n) (h : Γ ⊢[PRAAx] pointDistinct L) : Γ ⊢[PRAAx]
    GaussianRationalFiniteRoots.distinct (yList L p g) := by
  unfold GaussianRationalFiniteRoots.distinct
  refine .allI (.impI ?_)
  unfold GaussianRationalFiniteRoots.distinctFrom
  refine .allI (.impI (.impI ?_))
  let Δ : List (Fm PTm (n+2)) :=
    lt (var 1) (var 0) :: lt (var 0) (length (Syn.shift (Syn.shift (yList L p g)))) ::
      Fm.shift (lt (var 0) (length (Syn.shift (yList L p g)))) :: (Γ.map Fm.shift).map Fm.shift
  have original : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] pointDistinct (Syn.shift (Syn.shift L)) := by
    simpa only [Fm.shift,subst_pointDistinct,Syn.shift] using h.shift.shift
  have irange : Δ ⊢[PRAAx] lt (var 1) (fiberCount (Syn.shift (Syn.shift L)) (Syn.shift (Syn.shift p)) (Syn.shift (Syn.shift g))) := by
    apply lt_congr (.eqRefl _) (y_length _ _ _)
    simpa only [Δ,Fm.shift,subst_lt,Foundations.SequenceComposition.subst_length,subst_yList,Syn.shift,Syn.subst_var,Fin.succ_zero_eq_one] using
      (Prf.hyp (by simp [Δ]) : Δ ⊢[PRAAx] Fm.shift (lt (var 0) (length (Syn.shift (yList L p g)))))
  have jrange : Δ ⊢[PRAAx] lt (var 0) (fiberCount (Syn.shift (Syn.shift L)) (Syn.shift (Syn.shift p)) (Syn.shift (Syn.shift g))) := by
    apply lt_congr (.eqRefl _) (y_length _ _ _)
    simpa only [Δ,subst_yList,Syn.shift] using (Prf.hyp1 : Δ ⊢[PRAAx] _)
  have out := ordinate_distinct_at (Syn.shift (Syn.shift L)) (Syn.shift (Syn.shift p)) (Syn.shift (Syn.shift g))
    (var 1) (var 0) (original.wk.wk.wk : Δ ⊢[PRAAx] _) irange jrange (Prf.hyp0 : Δ ⊢[PRAAx] _)
  simpa only [Δ,Syn.shift,subst_yList,Syn.subst_var,Fin.succ_zero_eq_one,List.map_cons] using out

theorem gaussian_one_nonzero : Γ ⊢[PRAAx] neg ((qone : PTm n) ≐ qzero) := by
  refine .impI ?_
  let Δ := (qone ≐ qzero) :: Γ
  have zeroBound : Δ ⊢[PRAAx] GaussianRationalMetric.bounded qzero zero one := by
    apply (GaussianRationalMetric.bounded_iff qzero ComplexLogarithmRemainder.zeroCode one zero one
      (le_refl _) (le_refl _) (GaussianRationalHorner.zero_represents _)).iffMpr
    exact le_congr ((congrMul (.eqRefl _) ComplexLogarithmRemainder.normSq_zero).eqTrans (mul_zero _)).eqSymm
      (by ipra_ring) (le_refl zero)
  have impossible := (GaussianRationalMetric.bounded_iff qone ComplexLogarithmRemainder.oneCode one zero one
    (le_refl _) (le_refl _) (GaussianRationalHorner.ofGaussian_represents _ _ (le_refl _))).iffMp
      (GaussianRationalReciprocal.bound_congr (Prf.hyp0 : Δ ⊢[PRAAx] _).eqSymm (.eqRefl _) (.eqRefl _) zeroBound)
  have bad : Δ ⊢[PRAAx] le one zero := le_congr
    ((congrMul (one_mul one) ComplexLogarithmRemainder.normSq_one).eqTrans (one_mul one))
    (by ipra_ring) impossible
  exact lt_zero_absurd Fm.bot bad
theorem monic_nonzero_head (F m x : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalFiniteRoots.nonzeroHead (monicValues F m x) := by
  have head : Γ ⊢[PRAAx] GaussianRationalFiniteRoots.head (monicValues F m x) ≐ qone :=
    (GaussianTranslatedNonconstant.recode_congr (monic_head F m x)).eqTrans
      (GaussianTranslatedNonconstant.recode_eq qone GaussianRationalSyntheticDivision.qone_canonical)
  exact .impI (.impE gaussian_one_nonzero (head.wk.eqSymm.eqTrans Prf.hyp0))

/-- The same actually produced ordinate list supplies both root membership
and field distinctness. This bound never replaces the exact cardinal sum. -/
theorem fiber_size_bound (F m L p g : PTm n) (hCurve : Γ ⊢[PRAAx] curveZeros F m L)
    (hDistinct : Γ ⊢[PRAAx] pointDistinct L) : Γ ⊢[PRAAx] le (fiberCount L p g) m :=
  le_congr (y_length L p g) (.eqRefl _)
    (GaussianRationalFiniteRoots.finite_root_bound _ m _ (monic_length _ _ _)
      (monic_nonzero_head _ _ _) (fiber_curve_roots F m L p g hCurve) (fiber_ordinates_distinct L p g hDistinct))

def sourceInput (F G m L : PTm n) : Fm PTm n := pointDistinct L ⋏ (curveZeros F m L ⋏ functionZeros G m L)
def selectedX (L p g : PTm n) : PTm n := abscissa L (representative L p g)
def specializedCurve (F m L p g : PTm n) : PTm n := monicValues F m (selectedX L p g)
def specializedFunction (G m L p g : PTm n) : PTm n := values G m (selectedX L p g)
def certificate (C D R K m : PTm n) : Fm PTm n := (length R ≐ K) ⋏
  (GaussianRationalFiniteRoots.roots C R ⋏ (GaussianRationalFiniteRoots.roots D R ⋏
    (GaussianRationalFiniteRoots.distinct R ⋏ le K m)))
@[simp] theorem subst_sourceInput {l : ℕ} (σ : Fin n → PTm l) (F G m L : PTm n) :
    (sourceInput F G m L).subst σ = sourceInput (Syn.subst σ F) (Syn.subst σ G) (Syn.subst σ m) (Syn.subst σ L) := by simp [sourceInput]
@[simp] theorem subst_selectedX {l : ℕ} (σ : Fin n → PTm l) (L p g : PTm n) :
    Syn.subst σ (selectedX L p g) = selectedX (Syn.subst σ L) (Syn.subst σ p) (Syn.subst σ g) := by simp [selectedX]
@[simp] theorem subst_specializedCurve {l : ℕ} (σ : Fin n → PTm l) (F m L p g : PTm n) :
    Syn.subst σ (specializedCurve F m L p g) = specializedCurve (Syn.subst σ F) (Syn.subst σ m)
      (Syn.subst σ L) (Syn.subst σ p) (Syn.subst σ g) := by simp [specializedCurve]
@[simp] theorem subst_specializedFunction {l : ℕ} (σ : Fin n → PTm l) (G m L p g : PTm n) :
    Syn.subst σ (specializedFunction G m L p g) = specializedFunction (Syn.subst σ G) (Syn.subst σ m)
      (Syn.subst σ L) (Syn.subst σ p) (Syn.subst σ g) := by simp [specializedFunction]
@[simp] theorem subst_certificate {l : ℕ} (σ : Fin n → PTm l) (C D R K m : PTm n) :
    (certificate C D R K m).subst σ = certificate (Syn.subst σ C) (Syn.subst σ D) (Syn.subst σ R)
      (Syn.subst σ K) (Syn.subst σ m) := by simp [certificate]

theorem curve_fiber (F G m L p g : PTm n) (h : Γ ⊢[PRAAx] sourceInput F G m L) : Γ ⊢[PRAAx]
    certificate (specializedCurve F m L p g) (specializedFunction G m L p g) (yList L p g) (fiberCount L p g) m :=
  .andI (y_length _ _ _) (.andI (fiber_curve_roots _ _ _ _ _ (.andE₁ (.andE₂ h)))
    (.andI (fiber_function_roots _ _ _ _ _ (.andE₂ (.andE₂ h)))
      (.andI (fiber_ordinates_distinct _ _ _ (.andE₁ h)) (fiber_size_bound _ _ _ _ _ (.andE₁ (.andE₂ h)) (.andE₁ h)))))

def output (F G m L p g : PTm n) : PTm n := pairT (yList L p g)
  (pairT (specializedCurve F m L p g) (pairT (specializedFunction G m L p g)
    (pairT (fiberCount L p g) (pairT (selectedX L p g) (GaussianRationalFiberGrouping.partitionTotal L p)))))
def outputF : PR 6 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
def run (F G m L p g : PTm n) : PTm n := PTm.app outputF ![F,G,m,L,p,g]
@[simp] theorem subst_output {l : ℕ} (σ : Fin n → PTm l) (F G m L p g : PTm n) :
    Syn.subst σ (output F G m L p g) = output (Syn.subst σ F) (Syn.subst σ G) (Syn.subst σ m)
      (Syn.subst σ L) (Syn.subst σ p) (Syn.subst σ g) := by simp [output]
@[simp] theorem subst_run {l : ℕ} (σ : Fin n → PTm l) (F G m L p g : PTm n) :
    Syn.subst σ (run F G m L p g) = run (Syn.subst σ F) (Syn.subst σ G) (Syn.subst σ m)
      (Syn.subst σ L) (Syn.subst σ p) (Syn.subst σ g) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl
theorem program_at (F G m L p g : PTm n) : Γ ⊢[PRAAx] run F G m L p g ≐ output F G m L p g := by
  simpa [outputF,run] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) ![F,G,m,L,p,g]
theorem returned_yList (F G m L p g : PTm n) : Γ ⊢[PRAAx] fstT (run F G m L p g) ≐ yList L p g :=
  (congrFst (program_at _ _ _ _ _ _)).eqTrans (fst_pair _ _)
theorem returned_curve (F G m L p g : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (run F G m L p g)) ≐ specializedCurve F m L p g :=
  (congrFst ((congrSnd (program_at _ _ _ _ _ _)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_function (F G m L p g : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (sndT (run F G m L p g))) ≐ specializedFunction G m L p g :=
  (congrFst ((congrSnd ((congrSnd (program_at _ _ _ _ _ _)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_count (F G m L p g : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (sndT (sndT (run F G m L p g)))) ≐ fiberCount L p g :=
  (congrFst ((congrSnd ((congrSnd ((congrSnd (program_at _ _ _ _ _ _)).eqTrans (snd_pair _ _))).eqTrans
    (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_x (F G m L p g : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (sndT (sndT (sndT (run F G m L p g))))) ≐ selectedX L p g :=
  (congrFst ((congrSnd ((congrSnd ((congrSnd ((congrSnd (program_at _ _ _ _ _ _)).eqTrans
    (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_partition (F G m L p g : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (sndT (sndT (sndT (run F G m L p g))))) ≐ GaussianRationalFiberGrouping.partitionTotal L p :=
  (congrSnd ((congrSnd ((congrSnd ((congrSnd ((congrSnd (program_at _ _ _ _ _ _)).eqTrans
    (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _)
theorem returned_cardinal_partition (F G m L p g : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (sndT (sndT (sndT (run F G m L p g))))) ≐ length L :=
  (returned_partition _ _ _ _ _ _).eqTrans (GaussianRationalFiberGrouping.cardinal_partition _ _)

theorem roots_congr {C D R S : PTm n} (hC : Γ ⊢[PRAAx] C ≐ D) (hR : Γ ⊢[PRAAx] R ≐ S)
    (h : Γ ⊢[PRAAx] GaussianRationalFiniteRoots.roots C R) : Γ ⊢[PRAAx] GaussianRationalFiniteRoots.roots D S := by
  have hs : Γ ⊢[PRAAx] (GaussianRationalFiniteRoots.roots (var 0) (var 1) : Fm PTm 2).subst ![C,R] := by simpa using h
  have out := Prf.eqSubst (GaussianRationalFiniteRoots.roots (var 0) (var 1) : Fm PTm 2)
    ![C,R] ![D,S] (fun i => by fin_cases i; exact hC; exact hR) hs
  simpa using out
theorem distinct_congr {R S : PTm n} (hR : Γ ⊢[PRAAx] R ≐ S)
    (h : Γ ⊢[PRAAx] GaussianRationalFiniteRoots.distinct R) : Γ ⊢[PRAAx] GaussianRationalFiniteRoots.distinct S := by
  have hs : Γ ⊢[PRAAx] (GaussianRationalFiniteRoots.distinct (var 0) : Fm PTm 1).subst ![R] := by simpa using h
  have out := Prf.eqSubst (GaussianRationalFiniteRoots.distinct (var 0) : Fm PTm 1)
    ![R] ![S] (fun i => by fin_cases i; exact hR) hs
  simpa using out
theorem returned_certificate (F G m L p g : PTm n) (h : Γ ⊢[PRAAx] sourceInput F G m L) : Γ ⊢[PRAAx]
    certificate (fstT (sndT (run F G m L p g))) (fstT (sndT (sndT (run F G m L p g))))
      (fstT (run F G m L p g)) (fstT (sndT (sndT (sndT (run F G m L p g))))) m :=
  .andI ((congrFst (returned_yList _ _ _ _ _ _)).eqTrans
      ((y_length _ _ _).eqTrans (returned_count _ _ _ _ _ _).eqSymm))
    (.andI (roots_congr (returned_curve _ _ _ _ _ _).eqSymm (returned_yList _ _ _ _ _ _).eqSymm
        (fiber_curve_roots _ _ _ _ _ (.andE₁ (.andE₂ h))))
      (.andI (roots_congr (returned_function _ _ _ _ _ _).eqSymm (returned_yList _ _ _ _ _ _).eqSymm
          (fiber_function_roots _ _ _ _ _ (.andE₂ (.andE₂ h))))
        (.andI (distinct_congr (returned_yList _ _ _ _ _ _).eqSymm (fiber_ordinates_distinct _ _ _ (.andE₁ h)))
          (le_congr (returned_count _ _ _ _ _ _).eqSymm (.eqRefl _) (fiber_size_bound _ _ _ _ _ (.andE₁ (.andE₂ h)) (.andE₁ h))))))

theorem scalar_specialization_proper_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (valueEqual (var 2) (var 3) ⟶
      evaluate (values (var 0) (var 1) (var 2)) (var 4) ≐ evaluate (values (var 0) (var 1) (var 3)) (var 4)) :=
  closeUniv 5 (.impI (values_evaluation_proper _ _ _ _ _ Prf.hyp0))
theorem monic_specialization_proper_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (valueEqual (var 2) (var 3) ⟶
      evaluate (monicValues (var 0) (var 1) (var 2)) (var 4) ≐ evaluate (monicValues (var 0) (var 1) (var 3)) (var 4)) :=
  closeUniv 5 (.impI (monic_values_evaluation_proper _ _ _ _ _ Prf.hyp0))
theorem fiber_ordinate_list_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((length (yList (var 0) (var 1) (var 2)) ≐ fiberCount (var 0) (var 1) (var 2)) ⋏
      (yRun (var 0) (var 1) (var 2) ≐ yList (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.andI (y_length _ _ _) (y_program_at _ _ _))
theorem fiber_ordinate_lookup_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (var 3) (fiberCount (var 0) (var 1) (var 2)) ⟶
      entry (yList (var 0) (var 1) (var 2)) (var 3) ≐ ordinate (var 0) (entry (fiber (var 0) (var 1) (var 2)) (var 3))) :=
  closeUniv 4 (.impI (y_lookup _ _ _ _ Prf.hyp0))
theorem fiber_distinct_ordinates_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (pointDistinct (var 0) ⟶ GaussianRationalFiniteRoots.distinct (yList (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (fiber_ordinates_distinct _ _ _ Prf.hyp0))
theorem original_curve_fiber_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (curveZeros (var 0) (var 1) (var 2) ⟶ pointDistinct (var 2) ⟶ le (fiberCount (var 2) (var 3) (var 4)) (var 1)) :=
  closeUniv 5 (.impI (.impI (fiber_size_bound _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem original_common_zeros_fiber_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (sourceInput (var 0) (var 1) (var 2) (var 3) ⟶
      certificate (specializedCurve (var 0) (var 2) (var 3) (var 4) (var 5))
        (specializedFunction (var 1) (var 2) (var 3) (var 4) (var 5))
        (yList (var 3) (var 4) (var 5)) (fiberCount (var 3) (var 4) (var 5)) (var 2)) :=
  closeUniv 6 (.impI (curve_fiber _ _ _ _ _ _ Prf.hyp0))
theorem curve_fiber_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    ((run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ≐ output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) ⋏
      (sndT (sndT (sndT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)))))) ≐ length (var 3))) :=
  closeUniv 6 (.andI (program_at _ _ _ _ _ _) (returned_cardinal_partition _ _ _ _ _ _))
theorem returned_curve_fiber_certificate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (sourceInput (var 0) (var 1) (var 2) (var 3) ⟶
      certificate (fstT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))))
        (fstT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)))))
        (fstT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)))
        (fstT (sndT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)))))) (var 2)) :=
  closeUniv 6 (.impI (returned_certificate _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianRationalCurveFibers
