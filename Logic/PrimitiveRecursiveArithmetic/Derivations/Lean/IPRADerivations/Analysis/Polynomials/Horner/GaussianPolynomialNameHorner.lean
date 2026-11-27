import IPRADerivations.Analysis.Names.Arithmetic.GaussianNameRingLaws
import IPRADerivations.Analysis.Polynomials.Evaluation.NamedValues.GaussianGeneralPolynomialValueName

/-!
# Actual numerical-prefix Horner interpretation of polynomial value names

All prefixes, degrees, coefficient data, point data and observation precisions
are internal numbers. The fixed PR2 prefix observer executes the original
rational Horner program. Its properness and its represented add/multiply
recurrence are derived from original coefficient CN and point CN. No evaluator,
normalization, prefix or completed-field operation law is an input.
-/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace LeanProofs.IPRA.Analysis.GaussianPolynomialNameHorner

open_ipra
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (horner qzero qadd qmul positive_product)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (bounded distanceBounded)
open LeanProofs.IPRA.Analysis.GaussianGeneralCoefficientNames (generalCN)
open LeanProofs.IPRA.Analysis.GaussianEuclideanDistanceName (pointCN subst_pointCN)
open LeanProofs.IPRA.Analysis.GaussianRootApproximationWitness (pointBounds subst_pointBounds)
open LeanProofs.IPRA.Analysis.GaussianCoefficientNameBounds (unit unit_positive subst_unit)
open LeanProofs.IPRA.Analysis.GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open LeanProofs.IPRA.Analysis.GaussianNameEquivalence (crossEquivalent)
open LeanProofs.IPRA.Analysis.GaussianGeneralPolynomialEvaluation (A C M T subst_T)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def coefficientData (i x : PTm n) : PTm n := pairT i x
def coefficientF (a : PR 3) : PR 2 := PTm.toPR
  (ap3 a (fstT (var 1)) (var 0) (sndT (var 1)) : PTm 2)
def data (N j x y : PTm n) : PTm n := pairT N (pairT j (pairT x y))
def raw (a : PR 3) (point : PR 2) (N j x y s : PTm n) : PTm n :=
  horner (GaussianGeneralPolynomialSamples.sample a N s x) (ap2 point s y) j
def rawBody (a : PR 3) (point : PR 2) : PTm 2 := raw a point
  (fstT (var 1)) (fstT (sndT (var 1))) (fstT (sndT (sndT (var 1))))
  (sndT (sndT (sndT (var 1)))) (var 0)
def rawF (a : PR 3) (point : PR 2) : PR 2 := PTm.toPR (rawBody a point)
def prefixF (a : PR 3) (point : PR 2) : PR 2 := GaussianFastValueCut.nameF (rawF a point)
def nameData (a : PR 3) (N U j x y : PTm n) : PTm n :=
  GaussianFastValueCut.nameData (T a N U x) (data N j x y)
def computedData (a : PR 3) (point : PR 2) (N j x y : PTm n) : PTm n :=
  nameData a N (GaussianNameBounds.U point y) j x y

ipra_subst coefficientData
ipra_subst data
ipra_subst raw
ipra_subst nameData
ipra_subst computedData

theorem coefficient_at (a : PR 3) (i s x : PTm n) : Γ ⊢[PRAAx]
    ap2 (coefficientF a) s (coefficientData i x) ≐ ap3 a i s x := by
  simpa [coefficientF, coefficientData] using
    (toPR_pair_eq (Γ := Γ) (ap3 a (var 1) (var 0) (var 2)) s i x)

theorem coefficient_fast (a : PR 3) (N i x : PTm n) (hCN : Γ ⊢[PRAAx] generalCN a N x)
    (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx] pointCN (coefficientF a) (coefficientData i x) := by
  refine .allI (.allI ?_)
  have cn : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] generalCN a (Syn.shift (Syn.shift N)) (Syn.shift (Syn.shift x)) := by
    simpa only [Fm.shift,GaussianGeneralCoefficientNames.subst_generalCN,Syn.shift] using hCN.shift.shift
  have idx : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] le (Syn.shift (Syn.shift i)) (Syn.shift (Syn.shift N)) := by
    simpa only [Fm.shift,subst_le,Syn.shift] using hi.shift.shift
  simpa only [Syn.shift,subst_coefficientData,GaussianEuclideanPointDistance.unit,GaussianCoefficientNameBounds.unit] using distance_congr
    (coefficient_at a (Syn.shift (Syn.shift i)) (var 1) (Syn.shift (Syn.shift x))).eqSymm
    (coefficient_at a (Syn.shift (Syn.shift i)) (var 0) (Syn.shift (Syn.shift x))).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianGeneralCoefficientNames.coherence a _ _ _ _ _ cn idx)

theorem raw_congr (a : PR 3) (point : PR 2) {N N' j j' x x' y y' s s' : PTm n}
    (hN : Γ ⊢[PRAAx] N ≐ N') (hj : Γ ⊢[PRAAx] j ≐ j') (hx : Γ ⊢[PRAAx] x ≐ x')
    (hy : Γ ⊢[PRAAx] y ≐ y') (hs : Γ ⊢[PRAAx] s ≐ s') : Γ ⊢[PRAAx]
    raw a point N j x y s ≐ raw a point N' j' x' y' s' := by
  have sample := (GaussianGeneralPolynomialSamples.program_at a N s x).eqSymm.eqTrans
    ((congrAp3 (GaussianGeneralPolynomialSamples.sampleF a) hN hs hx).eqTrans
      (GaussianGeneralPolynomialSamples.program_at a N' s' x'))
  exact congrAp3 GaussianRationalHorner.hornerF hj sample (congrAp2 point hs hy)

theorem raw_at (a : PR 3) (point : PR 2) (N j x y s : PTm n) : Γ ⊢[PRAAx]
    ap2 (rawF a point) s (data N j x y) ≐ raw a point N j x y s := by
  simpa [rawF, rawBody, data, pairVector, pairVectorField] using
    (toPR_pairVector_eq (Γ := Γ) (k := 3)
      (raw a point (var 1) (var 2) (var 3) (var 4) (var 0)) s ![N, j, x, y])

theorem weighted_monotone (U k N : PTm n) (hk : Γ ⊢[PRAAx] le k N) : Γ ⊢[PRAAx]
    le (GaussianRationalHornerLipschitz.weighted U k) (GaussianRationalHornerLipschitz.weighted U N) :=
  le_of_eq_add ((congrAp2 (sumF GaussianRationalHornerLipschitz.weightedBody) (eq_add_of_le hk) (.eqRefl U)).eqTrans
    (sum_split _ k (monus N k) U))

theorem coefficient_budget (N U p k : PTm n) (hU : Γ ⊢[PRAAx] le one U) (hk : Γ ⊢[PRAAx] le k N) : Γ ⊢[PRAAx]
    le (GaussianRationalHornerPerturbation.budget U p (succ k)) (C N U*p) := by
  have native := AnalyticNumberTheory.PhiLower.le_mul_mono
    (AnalyticNumberTheory.PhiLower.le_mul_mono ((succ_monus_succ k N).eqTrans hk)
      (GaussianFactorBudget.power_monotone_length U k N hU hk)) (le_refl p)
  exact le_congr (GaussianRationalHornerPerturbation.budget_succ U p k).eqSymm (.eqRefl _) native

theorem point_budget (a : PR 3) (N U x p k : PTm n) (hk : Γ ⊢[PRAAx] le k N) : Γ ⊢[PRAAx]
    le (GaussianRationalHornerLipschitz.constant k U (A a N x)*p) (M a N U x*p) :=
  AnalyticNumberTheory.PhiLower.le_mul_mono
    (AnalyticNumberTheory.PhiLower.le_mul_mono (le_refl (A a N x)) (weighted_monotone U k N hk)) (le_refl p)

theorem raw_zero (a : PR 3) (point : PR 2) (N x y s : PTm n) : Γ ⊢[PRAAx]
    raw a point N zero x y s ≐ qzero := GaussianRationalHorner.horner_zero _ _
theorem raw_succ (a : PR 3) (point : PR 2) (N j x y s : PTm n) (hj : Γ ⊢[PRAAx] le j N) : Γ ⊢[PRAAx]
    raw a point N (succ j) x y s ≐
      qadd (qmul (raw a point N j x y s) (ap2 point s y)) (ap3 a (monus N j) s x) :=
  (GaussianRationalHorner.horner_succ _ _ j).eqTrans
    (GaussianRationalSyntheticDivision.qadd_congr (.eqRefl _) (GaussianGeneralPolynomialSamples.sample_lookup a N s x j hj))
theorem raw_full (a : PR 3) (point : PR 2) (N x y s : PTm n) : Γ ⊢[PRAAx]
    raw a point N (succ N) x y s ≐ GaussianGeneralPolynomialEvaluation.observation a point N x y s :=
  congrAp3 GaussianRationalHorner.hornerF (GaussianGeneralPolynomialSamples.sample_length a N s x).eqSymm
    (.eqRefl _) (.eqRefl _)

/-- The old two genuine prefix estimates imply a uniform ORIGINAL modulus T.
The positive-prefix split handles zero degree/counter without cancellation. -/
theorem raw_regular_at (a : PR 3) (point : PR 2) (N U j x y s t : PTm n)
    (hCN : Γ ⊢[PRAAx] generalCN a N x) (hPoint : Γ ⊢[PRAAx] pointCN point y)
    (hBounds : Γ ⊢[PRAAx] pointBounds point U y) (hU : Γ ⊢[PRAAx] le one U)
    (hj : Γ ⊢[PRAAx] le j (succ N)) : Γ ⊢[PRAAx]
    distanceBounded (raw a point N j x y s) (raw a point N j x y t)
      (T a N U x*(unit s+unit t)) (unit s*unit t) := by
  have pos := positive_product (Γ := Γ) _ _ (unit_positive s) (unit_positive t)
  refine .orE (zero_or_succ j) ?_ ?_
  · have hs := (raw_congr (Γ := (j ≐ zero)::Γ) a point (.eqRefl _) Prf.hyp0 (.eqRefl _) (.eqRefl _) (.eqRefl s)).eqTrans (raw_zero a point N x y s)
    have ht := (raw_congr (Γ := (j ≐ zero)::Γ) a point (.eqRefl _) Prf.hyp0 (.eqRefl _) (.eqRefl _) (.eqRefl t)).eqTrans (raw_zero a point N x y t)
    exact GaussianRationalReciprocal.bound_congr
      ((GaussianRationalSyntheticDivision.qsub_congr hs ht).eqTrans (GaussianCoefficientNormOrder.qsub_self qzero)).eqSymm
      (.eqRefl _) (.eqRefl _) (GaussianMonicResidualRadius.zero_bounded _ _ pos.wk)
  · let Δ := (j ≐ succ (pred j))::Γ
    have correct : Δ ⊢[PRAAx] j ≐ succ (pred j) := Prf.hyp0
    have range : Δ ⊢[PRAAx] le (pred j) N :=
      (succ_monus_succ _ _).eqSymm.eqTrans (le_congr correct (.eqRefl _) hj.wk)
    have first := GaussianRationalAllCoefficientPerturbation.prefix_bound
      (GaussianGeneralPolynomialSamples.sample a N s x) (GaussianGeneralPolynomialSamples.sample a N t x)
      (ap2 point s y) N U (unit s+unit t) (unit s*unit t) (succ (pred j))
      hU.wk pos.wk (GaussianGeneralPolynomialSamples.all_coefficient_coherence a N s t x hCN.wk)
      (GaussianRootApproximationWitness.point_at point U y s hBounds.wk) ((succ_monus_succ _ _).eqTrans range)
    have first' := GaussianRationalHornerPerturbation.bounded_weaken _ _ _ _ pos.wk
      (coefficient_budget N U (unit s+unit t) (pred j) hU.wk range) first
    have second := GaussianRationalHornerLipschitz.difference_prefix
      (GaussianGeneralPolynomialSamples.sample a N t x) (ap2 point s y) (ap2 point t y)
      N U (A a N x) (unit s+unit t) (unit s*unit t) (pred j)
      (GaussianGeneralPolynomialSamples.sample_length a N t x)
      (GaussianGeneralPolynomialEvaluation.sample_coefficients a N t x hCN.wk)
      (GaussianRootApproximationWitness.point_at point U y s hBounds.wk)
      (GaussianRootApproximationWitness.point_at point U y t hBounds.wk) pos.wk
      (GaussianEuclideanDistanceName.point_cn_at point y s t hPoint.wk) range
    have second' := GaussianRationalHornerPerturbation.bounded_weaken _ _ _ _ pos.wk
      (point_budget a N U x (unit s+unit t) (pred j) range) second
    exact distance_congr (congrAp3 GaussianRationalHorner.hornerF correct.eqSymm (.eqRefl _) (.eqRefl _))
      (congrAp3 GaussianRationalHorner.hornerF correct.eqSymm (.eqRefl _) (.eqRefl _))
      (by unfold T; ipra_ring) (.eqRefl _) (distance_triangle_same _ _ _ _ _ _ pos.wk first' second')

/-- The actual runtime-prefix observer is regular, not assumed regular. -/
theorem raw_regular (a : PR 3) (point : PR 2) (N U j x y : PTm n)
    (hCN : Γ ⊢[PRAAx] generalCN a N x) (hPoint : Γ ⊢[PRAAx] pointCN point y)
    (hBounds : Γ ⊢[PRAAx] pointBounds point U y) (hU : Γ ⊢[PRAAx] le one U)
    (hj : Γ ⊢[PRAAx] le j (succ N)) : Γ ⊢[PRAAx]
    GaussianFastValueCut.regular (rawF a point) (T a N U x) (data N j x y) := by
  refine .allI (.allI ?_)
  have cn : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] generalCN a (Syn.shift (Syn.shift N)) (Syn.shift (Syn.shift x)) := by
    simpa only [Fm.shift,GaussianGeneralCoefficientNames.subst_generalCN,Syn.shift] using hCN.shift.shift
  have hp : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] pointCN point (Syn.shift (Syn.shift y)) := by
    simpa only [Fm.shift,subst_pointCN,Syn.shift] using hPoint.shift.shift
  have hb : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] pointBounds point (Syn.shift (Syn.shift U)) (Syn.shift (Syn.shift y)) := by
    simpa only [Fm.shift,subst_pointBounds,Syn.shift] using hBounds.shift.shift
  have hu : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] le one (Syn.shift (Syn.shift U)) := by
    simpa only [Fm.shift,subst_le,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift] using hU.shift.shift
  have idx : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] le (Syn.shift (Syn.shift j)) (succ (Syn.shift (Syn.shift N))) := by
    simpa only [Fm.shift,subst_le,ConciseIPRA.PTm.subst_succ,Syn.shift] using hj.shift.shift
  simpa only [Syn.shift,subst_data,subst_T] using distance_congr
    (raw_at a point (Syn.shift (Syn.shift N)) (Syn.shift (Syn.shift j)) (Syn.shift (Syn.shift x)) (Syn.shift (Syn.shift y)) (var 1)).eqSymm
    (raw_at a point (Syn.shift (Syn.shift N)) (Syn.shift (Syn.shift j)) (Syn.shift (Syn.shift x)) (Syn.shift (Syn.shift y)) (var 0)).eqSymm
    (.eqRefl _) (.eqRefl _) (raw_regular_at a point _ _ _ _ _ (var 1) (var 0) cn hp hb hu idx)

theorem prefix_at (a : PR 3) (point : PR 2) (N U j x y k : PTm n) : Γ ⊢[PRAAx]
    ap2 (prefixF a point) k (nameData a N U j x y) ≐ GaussianFastValueCut.recode
      (raw a point N j x y (GaussianFastValueCut.exponent (T a N U x) k)) :=
  (GaussianFastValueCut.name_at (rawF a point) (T a N U x) (data N j x y) k).eqTrans
    (GaussianNameArithmetic.recode_congr (raw_at a point N j x y _))

theorem prefix_canonical (a : PR 3) (point : PR 2) (N U j x y k : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalHorner.canonical (ap2 (prefixF a point) k (nameData a N U j x y)) :=
  GaussianFastValueCut.name_canonical _ _ _ _
theorem prefix_fast (a : PR 3) (point : PR 2) (N U j x y : PTm n)
    (hCN : Γ ⊢[PRAAx] generalCN a N x) (hPoint : Γ ⊢[PRAAx] pointCN point y)
    (hBounds : Γ ⊢[PRAAx] pointBounds point U y) (hU : Γ ⊢[PRAAx] le one U)
    (hj : Γ ⊢[PRAAx] le j (succ N)) : Γ ⊢[PRAAx]
    pointCN (prefixF a point) (nameData a N U j x y) :=
  GaussianFastValueCut.name_fast _ _ _ (raw_regular a point N U j x y hCN hPoint hBounds hU hj)

theorem prefix_sample_error (a : PR 3) (point : PR 2) (N U j x y k : PTm n)
    (hCN : Γ ⊢[PRAAx] generalCN a N x) (hPoint : Γ ⊢[PRAAx] pointCN point y)
    (hBounds : Γ ⊢[PRAAx] pointBounds point U y) (hU : Γ ⊢[PRAAx] le one U)
    (hj : Γ ⊢[PRAAx] le j (succ N)) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (prefixF a point) k (nameData a N U j x y)) (raw a point N j x y k)
      (T a N U x+one) (unit k) :=
  distance_congr (.eqRefl _) (raw_at a point N j x y k) (.eqRefl _) (.eqRefl _)
    (GaussianNameRingLaws.normalized_to_sample (rawF a point) (T a N U x) (data N j x y) k
      (raw_regular a point N U j x y hCN hPoint hBounds hU hj))

def productData (a : PR 3) (point : PR 2) (N U j x y : PTm n) : PTm n :=
  GaussianNameArithmetic.multiplyData (prefixF a point) point (nameData a N U j x y) y
def stepData (a : PR 3) (point : PR 2) (N U j x y : PTm n) : PTm n :=
  GaussianNameArithmetic.addData (productData a point N U j x y) (coefficientData (monus N j) x)
def stepF (a : PR 3) (point : PR 2) : PR 2 :=
  GaussianNameArithmetic.addF (GaussianNameArithmetic.multiplyF (prefixF a point) point) (coefficientF a)
def stepBudget (a : PR 3) (point : PR 2) (N U j x y : PTm n) : PTm n :=
  (T a N U x+one)+GaussianNameRingLaws.three+
    (GaussianNameArithmetic.multiplyModulus (prefixF a point) point (nameData a N U j x y) y+one)+
      (T a N U x+one)*U
ipra_subst productData
ipra_subst stepData
ipra_subst stepBudget [GaussianNameRingLaws.three]

theorem step_fast (a : PR 3) (point : PR 2) (N U j x y : PTm n)
    (hCN : Γ ⊢[PRAAx] generalCN a N x) (hPoint : Γ ⊢[PRAAx] pointCN point y)
    (hBounds : Γ ⊢[PRAAx] pointBounds point U y) (hU : Γ ⊢[PRAAx] le one U)
    (hj : Γ ⊢[PRAAx] le j N) : Γ ⊢[PRAAx] pointCN (stepF a point) (stepData a point N U j x y) :=
  GaussianNameArithmetic.add_fast _ _ _ _
    (GaussianNameArithmetic.multiply_fast _ _ _ _
      (prefix_fast a point N U j x y hCN hPoint hBounds hU (le_trans hj (le_succ_self N))) hPoint)
    (coefficient_fast a N _ x hCN (GaussianMonicResidualRadius.monus_le_left N j))

/-- Every inner and outer normalization is compared to the same literal
rational Horner successor. The auxiliary disk for that raw prefix is computed,
not an input, and its unused zero-weight contribution disappears algebraically. -/
theorem step_error (a : PR 3) (point : PR 2) (N U j x y k : PTm n)
    (hCN : Γ ⊢[PRAAx] generalCN a N x) (hPoint : Γ ⊢[PRAAx] pointCN point y)
    (hBounds : Γ ⊢[PRAAx] pointBounds point U y) (hU : Γ ⊢[PRAAx] le one U)
    (hj : Γ ⊢[PRAAx] le j N) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (stepF a point) k (stepData a point N U j x y)) (raw a point N (succ j) x y k)
      (GaussianNameRingLaws.three+
        (GaussianNameArithmetic.multiplyModulus (prefixF a point) point (nameData a N U j x y) y+one)+
          (T a N U x+one)*U) (unit k) := by
  have hp := prefix_fast a point N U j x y hCN hPoint hBounds hU (le_trans hj (le_succ_self N))
  have hc := coefficient_fast a N (monus N j) x hCN (GaussianMonicResidualRadius.monus_le_left N j)
  have hm := GaussianNameArithmetic.multiply_fast _ _ _ _ hp hPoint
  have first := GaussianNameRingLaws.multiply_sample_error (prefixF a point) point (nameData a N U j x y) y k hp hPoint
  have second := GaussianNameRingLaws.product_left_error _ _ _ (T a N U x+one) (unit k) U
    (GaussianGeneralFTAConstants.ceilL1 (raw a point N j x y k)) (unit_positive k)
    (prefix_sample_error a point N U j x y k hCN hPoint hBounds hU (le_trans hj (le_succ_self N)))
    (GaussianRootApproximationWitness.point_at point U y k hBounds)
    (GaussianGeneralFTAConstants.ceil_norm_bound _)
  have product := distance_triangle_same _ _ _ _ _ _ (unit_positive k) first second
  have outer := GaussianNameRingLaws.add_sample_error (GaussianNameArithmetic.multiplyF (prefixF a point) point)
    (coefficientF a) (productData a point N U j x y) (coefficientData (monus N j) x) k hm hc
  have lift := GaussianNameRingLaws.sum_left_error _ _ (ap2 (coefficientF a) k (coefficientData (monus N j) x))
    _ _ (unit_positive k) product
  have actual : Γ ⊢[PRAAx]
      qadd (qmul (raw a point N j x y k) (ap2 point k y))
        (ap2 (coefficientF a) k (coefficientData (monus N j) x)) ≐ raw a point N (succ j) x y k :=
    (GaussianRationalSyntheticDivision.qadd_congr (.eqRefl _) (coefficient_at a (monus N j) k x)).eqTrans
      (raw_succ a point N j x y k hj).eqSymm
  exact distance_congr (.eqRefl _) actual (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ (unit_positive k) outer lift)

theorem recurrence_at (a : PR 3) (point : PR 2) (N U j x y k : PTm n)
    (hCN : Γ ⊢[PRAAx] generalCN a N x) (hPoint : Γ ⊢[PRAAx] pointCN point y)
    (hBounds : Γ ⊢[PRAAx] pointBounds point U y) (hU : Γ ⊢[PRAAx] le one U)
    (hj : Γ ⊢[PRAAx] le j N) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (prefixF a point) k (nameData a N U (succ j) x y))
      (ap2 (stepF a point) k (stepData a point N U j x y)) (stepBudget a point N U j x y) (unit k) :=
  distance_congr (.eqRefl _) (.eqRefl _) (by unfold stepBudget; ipra_ring) (.eqRefl _)
    (GaussianNameRingLaws.through_identity _ _ _ _ _ _ _ (unit_positive k)
      (prefix_sample_error a point N U (succ j) x y k hCN hPoint hBounds hU ((succ_monus_succ j N).eqTrans hj))
      (step_error a point N U j x y k hCN hPoint hBounds hU hj) (.eqRefl _))

/-- The actual prefix name obeys the represented Horner step, for every
internal prefix count, using actual normalized addition and multiplication. -/
theorem recurrence (a : PR 3) (point : PR 2) (N U j x y : PTm n)
    (hCN : Γ ⊢[PRAAx] generalCN a N x) (hPoint : Γ ⊢[PRAAx] pointCN point y)
    (hBounds : Γ ⊢[PRAAx] pointBounds point U y) (hU : Γ ⊢[PRAAx] le one U)
    (hj : Γ ⊢[PRAAx] le j N) : Γ ⊢[PRAAx]
    crossEquivalent (prefixF a point) (stepF a point)
      (nameData a N U (succ j) x y) (stepData a point N U j x y) := by
  apply GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ (stepBudget a point N U j x y)
    (prefix_fast a point N U (succ j) x y hCN hPoint hBounds hU ((succ_monus_succ j N).eqTrans hj))
    (step_fast a point N U j x y hCN hPoint hBounds hU hj)
  refine .allI ?_
  have cn : Γ.map Fm.shift ⊢[PRAAx] generalCN a (Syn.shift N) (Syn.shift x) := by
    simpa only [Fm.shift,GaussianGeneralCoefficientNames.subst_generalCN,Syn.shift] using hCN.shift
  have hp : Γ.map Fm.shift ⊢[PRAAx] pointCN point (Syn.shift y) := by
    simpa only [Fm.shift,subst_pointCN,Syn.shift] using hPoint.shift
  have hb : Γ.map Fm.shift ⊢[PRAAx] pointBounds point (Syn.shift U) (Syn.shift y) := by
    simpa only [Fm.shift,subst_pointBounds,Syn.shift] using hBounds.shift
  have hu : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift U) := by
    simpa only [Fm.shift,subst_le,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift] using hU.shift
  have idx : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift j) (Syn.shift N) := by
    simpa only [Fm.shift,subst_le,Syn.shift] using hj.shift
  simpa only [Syn.shift,subst_nameData,subst_stepData,subst_stepBudget,ConciseIPRA.PTm.subst_succ] using
    recurrence_at a point (Syn.shift N) (Syn.shift U) (Syn.shift j) (Syn.shift x) (Syn.shift y) (var 0) cn hp hb hu idx

/-- Empty prefix represents zero; no raw coefficient is falsely identified
with its canonical recoding. -/
theorem zero_prefix_distance (a : PR 3) (point : PR 2) (N U x y k : PTm n) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (prefixF a point) k (nameData a N U zero x y))
      (ap2 GaussianNameRingLaws.zeroF k zero) zero one := by
  have actual := (prefix_at (Γ := Γ) a point N U zero x y k).eqTrans
    (GaussianNameArithmetic.recode_congr (raw_zero a point N x y _))
  exact distance_congr actual.eqSymm (GaussianNameRingLaws.zero_at k zero).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianFastValueCut.recode_distance qzero)

theorem zero_prefix (a : PR 3) (point : PR 2) (N U x y : PTm n)
    (hCN : Γ ⊢[PRAAx] generalCN a N x) (hPoint : Γ ⊢[PRAAx] pointCN point y)
    (hBounds : Γ ⊢[PRAAx] pointBounds point U y) (hU : Γ ⊢[PRAAx] le one U) : Γ ⊢[PRAAx]
    crossEquivalent (prefixF a point) GaussianNameRingLaws.zeroF (nameData a N U zero x y) zero := by
  apply GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ zero
    (prefix_fast a point N U zero x y hCN hPoint hBounds hU (zero_le _)) (GaussianNameRingLaws.zero_fast zero)
  refine .allI ?_
  simpa only [Syn.shift,subst_nameData,ConciseIPRA.PTm.subst_zero] using
    distance_radius_mono _ _ zero one zero (unit (var 0)) (le_refl _) (unit_positive _)
      (le_of_eq_add (d := zero) (by ipra_ring))
      (zero_prefix_distance a point (Syn.shift N) (Syn.shift U) (Syn.shift x) (Syn.shift y) (var 0))

/-- At the full numerical prefix the original value-program query is
literally retained, with its original degree, disk, data and precision shift. -/
theorem full_prefix_at (a : PR 3) (point : PR 2) (N U x y k : PTm n) : Γ ⊢[PRAAx]
    ap2 (prefixF a point) k (nameData a N U (succ N) x y) ≐
      ap2 (GaussianGeneralPolynomialValueName.nameF a point) k
        (GaussianGeneralPolynomialValueName.nameData a N U x y) :=
  (prefix_at a point N U (succ N) x y k).eqTrans
    ((GaussianNameArithmetic.recode_congr (raw_full a point N x y _)).eqTrans
      (GaussianGeneralPolynomialValueName.name_observation a point N U x y k).eqSymm)

theorem full_prefix (a : PR 3) (point : PR 2) (N U x y : PTm n)
    (hCN : Γ ⊢[PRAAx] generalCN a N x) (hPoint : Γ ⊢[PRAAx] pointCN point y)
    (hBounds : Γ ⊢[PRAAx] pointBounds point U y) (hU : Γ ⊢[PRAAx] le one U) : Γ ⊢[PRAAx]
    crossEquivalent (prefixF a point) (GaussianGeneralPolynomialValueName.nameF a point)
      (nameData a N U (succ N) x y) (GaussianGeneralPolynomialValueName.nameData a N U x y) := by
  apply GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ zero
    (prefix_fast a point N U (succ N) x y hCN hPoint hBounds hU (le_refl _))
    (GaussianGeneralPolynomialValueName.name_fast a point N U x y hCN hPoint hBounds hU)
  refine .allI ?_
  have same := full_prefix_at (Γ := Γ.map Fm.shift) a point (Syn.shift N) (Syn.shift U) (Syn.shift x) (Syn.shift y) (var 0)
  simpa only [Syn.shift,subst_nameData,GaussianGeneralPolynomialValueName.subst_nameData,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    distance_congr same.eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
      (GaussianRationalPowerDifference.distance_refl_zero _ _ (unit_positive (var 0)))

/-- Source properness needs no externally supplied disk. -/
theorem computed_prefix_fast (a : PR 3) (point : PR 2) (N j x y : PTm n)
    (hCN : Γ ⊢[PRAAx] generalCN a N x) (hPoint : Γ ⊢[PRAAx] pointCN point y)
    (hj : Γ ⊢[PRAAx] le j (succ N)) : Γ ⊢[PRAAx] pointCN (prefixF a point) (computedData a point N j x y) :=
  prefix_fast a point N (GaussianNameBounds.U point y) j x y hCN hPoint
    (GaussianNameBounds.all_samples_bounded point y hPoint) (GaussianNameBounds.U_positive point y) hj

theorem computed_recurrence (a : PR 3) (point : PR 2) (N j x y : PTm n)
    (hCN : Γ ⊢[PRAAx] generalCN a N x) (hPoint : Γ ⊢[PRAAx] pointCN point y)
    (hj : Γ ⊢[PRAAx] le j N) : Γ ⊢[PRAAx]
    crossEquivalent (prefixF a point) (stepF a point) (computedData a point N (succ j) x y)
      (stepData a point N (GaussianNameBounds.U point y) j x y) :=
  recurrence a point N (GaussianNameBounds.U point y) j x y hCN hPoint
    (GaussianNameBounds.all_samples_bounded point y hPoint) (GaussianNameBounds.U_positive point y) hj

theorem computed_zero_prefix (a : PR 3) (point : PR 2) (N x y : PTm n)
    (hCN : Γ ⊢[PRAAx] generalCN a N x) (hPoint : Γ ⊢[PRAAx] pointCN point y) : Γ ⊢[PRAAx]
    crossEquivalent (prefixF a point) GaussianNameRingLaws.zeroF (computedData a point N zero x y) zero :=
  zero_prefix a point N (GaussianNameBounds.U point y) x y hCN hPoint
    (GaussianNameBounds.all_samples_bounded point y hPoint) (GaussianNameBounds.U_positive point y)

theorem computed_full_prefix (a : PR 3) (point : PR 2) (N x y : PTm n)
    (hCN : Γ ⊢[PRAAx] generalCN a N x) (hPoint : Γ ⊢[PRAAx] pointCN point y) : Γ ⊢[PRAAx]
    crossEquivalent (prefixF a point) (GaussianGeneralPolynomialValueName.nameF a point)
      (computedData a point N (succ N) x y)
      (GaussianGeneralPolynomialValueName.nameData a N (GaussianNameBounds.U point y) x y) :=
  full_prefix a point N (GaussianNameBounds.U point y) x y hCN hPoint
    (GaussianNameBounds.all_samples_bounded point y hPoint) (GaussianNameBounds.U_positive point y)

/-- The represented prefix interpretation and the original polynomial-value
zero predicate agree; this uses actual program equivalence, not code equality
between names with different normalization exponents. -/
theorem full_zero_iff (a : PR 3) (point : PR 2) (N U x y : PTm n)
    (hCN : Γ ⊢[PRAAx] generalCN a N x) (hPoint : Γ ⊢[PRAAx] pointCN point y)
    (hBounds : Γ ⊢[PRAAx] pointBounds point U y) (hU : Γ ⊢[PRAAx] le one U) : Γ ⊢[PRAAx]
    Fm.iff (GaussianGeneralPolynomialValueName.programZero (prefixF a point) (nameData a N U (succ N) x y))
      (GaussianGeneralPolynomialValueName.valueZero a point N U x y) :=
  (GaussianNameEquivalence.cross_zero_iff _ _ _ _ (full_prefix a point N U x y hCN hPoint hBounds hU)).iffTrans
    (GaussianGeneralPolynomialValueName.value_zero_iff_name_zero a point N U x y).iffSymm

theorem computed_full_zero_iff (a : PR 3) (point : PR 2) (N x y : PTm n)
    (hCN : Γ ⊢[PRAAx] generalCN a N x) (hPoint : Γ ⊢[PRAAx] pointCN point y) : Γ ⊢[PRAAx]
    Fm.iff (GaussianGeneralPolynomialValueName.programZero (prefixF a point) (computedData a point N (succ N) x y))
      (GaussianGeneralPolynomialValueName.valueZero a point N (GaussianNameBounds.U point y) x y) :=
  full_zero_iff a point N (GaussianNameBounds.U point y) x y hCN hPoint
    (GaussianNameBounds.all_samples_bounded point y hPoint) (GaussianNameBounds.U_positive point y)

/-! Closed ordinary PRAAx endpoints. Fixed coefficient/point schemas are the
only external parameters; numerical degree and prefix indices are never
replaced by an externally fixed polynomial or a runtime syntax evaluator. -/
theorem actual_coefficient_program_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (ap2 (coefficientF a) (var 1) (coefficientData (var 0) (var 2)) ≐ ap3 a (var 0) (var 1) (var 2)) :=
  closeUniv 3 (coefficient_at a _ _ _)
theorem original_coefficient_name_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (generalCN a (var 0) (var 2) ⟶ le (var 1) (var 0) ⟶
      pointCN (coefficientF a) (coefficientData (var 1) (var 2))) :=
  closeUniv 3 (.impI (.impI (coefficient_fast a _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_normalized_prefix_program_closed (a : PR 3) (point : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (ap2 (prefixF a point) (var 5) (nameData a (var 0) (var 1) (var 2) (var 3) (var 4)) ≐
      GaussianFastValueCut.recode (raw a point (var 0) (var 2) (var 3) (var 4)
        (GaussianFastValueCut.exponent (T a (var 0) (var 1) (var 3)) (var 5)))) :=
  closeUniv 6 (prefix_at a point _ _ _ _ _ _)
theorem actual_rational_prefix_step_closed (a : PR 3) (point : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le (var 1) (var 0) ⟶ raw a point (var 0) (succ (var 1)) (var 2) (var 3) (var 4) ≐
      qadd (qmul (raw a point (var 0) (var 1) (var 2) (var 3) (var 4)) (ap2 point (var 4) (var 3)))
        (ap3 a (monus (var 0) (var 1)) (var 4) (var 2))) :=
  closeUniv 5 (.impI (raw_succ a point _ _ _ _ _ Prf.hyp0))
theorem source_proper_prefix_name_closed (a : PR 3) (point : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (generalCN a (var 0) (var 2) ⟶ pointCN point (var 3) ⟶ le (var 1) (succ (var 0)) ⟶
      pointCN (prefixF a point) (computedData a point (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (.impI (.impI (computed_prefix_fast a point _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))
theorem source_represented_horner_step_closed (a : PR 3) (point : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (generalCN a (var 0) (var 2) ⟶ pointCN point (var 3) ⟶ le (var 1) (var 0) ⟶
      crossEquivalent (prefixF a point) (stepF a point)
        (computedData a point (var 0) (succ (var 1)) (var 2) (var 3))
        (stepData a point (var 0) (GaussianNameBounds.U point (var 3)) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (.impI (.impI (computed_recurrence a point _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))
theorem source_represented_horner_zero_closed (a : PR 3) (point : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (generalCN a (var 0) (var 1) ⟶ pointCN point (var 2) ⟶
      crossEquivalent (prefixF a point) GaussianNameRingLaws.zeroF (computedData a point (var 0) zero (var 1) (var 2)) zero) :=
  closeUniv 3 (.impI (.impI (computed_zero_prefix a point _ _ _ Prf.hyp1 Prf.hyp0)))
theorem literal_original_polynomial_program_closed (a : PR 3) (point : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (ap2 (prefixF a point) (var 4) (nameData a (var 0) (var 1) (succ (var 0)) (var 2) (var 3)) ≐
      ap2 (GaussianGeneralPolynomialValueName.nameF a point) (var 4)
        (GaussianGeneralPolynomialValueName.nameData a (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 5 (full_prefix_at a point _ _ _ _ _)
theorem source_represented_polynomial_closed (a : PR 3) (point : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (generalCN a (var 0) (var 1) ⟶ pointCN point (var 2) ⟶
      crossEquivalent (prefixF a point) (GaussianGeneralPolynomialValueName.nameF a point)
        (computedData a point (var 0) (succ (var 0)) (var 1) (var 2))
        (GaussianGeneralPolynomialValueName.nameData a (var 0) (GaussianNameBounds.U point (var 2)) (var 1) (var 2))) :=
  closeUniv 3 (.impI (.impI (computed_full_prefix a point _ _ _ Prf.hyp1 Prf.hyp0)))
theorem source_represented_polynomial_zero_closed (a : PR 3) (point : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (generalCN a (var 0) (var 1) ⟶ pointCN point (var 2) ⟶
      Fm.iff (GaussianGeneralPolynomialValueName.programZero (prefixF a point)
        (computedData a point (var 0) (succ (var 0)) (var 1) (var 2)))
        (GaussianGeneralPolynomialValueName.valueZero a point (var 0) (GaussianNameBounds.U point (var 2)) (var 1) (var 2))) :=
  closeUniv 3 (.impI (.impI (computed_full_zero_iff a point _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianPolynomialNameHorner
