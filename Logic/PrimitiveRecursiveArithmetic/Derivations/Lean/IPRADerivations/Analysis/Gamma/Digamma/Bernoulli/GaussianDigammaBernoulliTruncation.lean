import IPRADerivations.Analysis.Gamma.Digamma.Bernoulli.GaussianDigammaBernoulliImproperName
import IPRADerivations.Analysis.Gamma.Digamma.Bernoulli.GaussianDigammaBernoulliCoefficients
import IPRADerivations.Analysis.Stirling.AllOrders.ImproperBounds.GaussianStirlingAllOrderSignedParityAlgebra

/-!
# Literal digamma truncation and the actual improper recurrence

The normalized error uses the original harmonic logarithm, the
half reciprocal, the native digamma and the first m literal
correction terms. The exact cofinal weighted folds give this
same named quantity with independent observation clocks.
-/

set_option autoImplicit false
set_option maxHeartbeats 1100000

namespace LeanProofs.IPRA.Analysis.GaussianDigammaBernoulliTruncation

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.PTm (num)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianDigammaBernoulliCoefficients (correction sign_step oriented_correction)
open GaussianDigammaBernoulliImproperName (recurrenceF recurrenceData recurrence_regular original_improper_cross)
open GaussianDigammaBernoulliRecurrence (weightedPrimitive)
open GaussianDigammaFirstBernoulliImproper (baseF baseData base_regular)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNameEquivalence (crossEquivalent cross_trans)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric distance_triangle_same reversed_difference)
open GaussianRationalHorner (qadd qmul qzero)
open GaussianRationalInverseQuadraticAlgebra (subtract_sum)
open GaussianRationalMetric (qsub distanceBounded)
open GaussianRationalPowerDifference (distance_refl_zero)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalSyntheticDivision (qsub_congr qmul_congr)
open GaussianReciprocalHorner (qmul_one_right)
open GaussianStirlingAllOrderPanelPartsNames
  (constantCap constant_bound fixed_product_distance normalized_product_error)
open GaussianStirlingAllOrderSignedLowerAlgebra (orientationPoint)
open GaussianStirlingAllOrderSignedParityAlgebra (orientation_even)
open GaussianStirlingNames (source)
open GaussianValueNormalizerExtensionality (rawDiagonal)
open ConciseIPRA.PTm (zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "subF" => GaussianNamedDifference.nameF
local notation "subData" => GaussianNamedDifference.data
local notation "scaleF" => GaussianBoundedConstantProductName.nameF
local notation "scaleData" => GaussianBoundedConstantProductName.data

def truncation : ℕ → PTm n → PTm n → PTm n
  | 0,_,_ => qzero
  | m+1,A,B => qadd (truncation m A B) (correction m A B)

def errorF : PR 2 := subF baseF constantF
def errorData (m : ℕ) (A B : PTm n) : PTm n := subData (baseData A B) (truncation m A B)
def orientedF : PR 2 := scaleF errorF
def orientedData (m : ℕ) (A B : PTm n) : PTm n :=
  scaleData (constantCap (orientationPoint m)) (orientationPoint m) (errorData m A B)

@[simp] theorem subst_truncation {l : ℕ} (σ : Fin n → PTm l) (m : ℕ) (A B : PTm n) :
    Syn.subst σ (truncation m A B) = truncation m (Syn.subst σ A) (Syn.subst σ B) := by
  induction m with
  | zero => simp [truncation]
  | succ m ih => simp [truncation,ih]

@[simp] theorem subst_orientedData {l : ℕ} (σ : Fin n → PTm l) (m : ℕ) (A B : PTm n) :
    Syn.subst σ (orientedData m A B) = orientedData m (Syn.subst σ A) (Syn.subst σ B) := by
  simp [orientedData,errorData]

private theorem oriented_step (m : ℕ) (A B s : PTm n) (ha : Γ ⊢[PRAAx] le one A) :
    Γ ⊢[PRAAx] qmul (orientationPoint (m+1)) (qsub s (truncation (m+1) A B)) ≐
      qsub (weightedPrimitive m A B) (qmul (orientationPoint m) (qsub s (truncation m A B))) := by
  let w := orientationPoint (n := n) m
  let t := truncation m A B
  let c := correction m A B
  have first : Γ ⊢[PRAAx] qmul (orientationPoint (m+1)) (qsub s (truncation (m+1) A B)) ≐
      qmul (GaussianRationalMetric.qnegative w) (qsub (qsub s t) c) :=
    qmul_congr (sign_step m) (subtract_sum s t c).eqSymm
  exact first.eqTrans ((GaussianInverseBinomialRows.negative_product w (qsub (qsub s t) c)).eqSymm.eqTrans
    ((RationalGaussianEmbedding.negative_congr (GaussianRationalRoundedPower.multiplication_difference w (qsub s t) c).eqSymm).eqTrans
      ((reversed_difference (qmul w (qsub s t)) (qmul w c)).eqTrans
        (qsub_congr (oriented_correction m A B ha) (.eqRefl _)))))

private def projectionRadius : ℕ → PTm n
  | 0 => zero
  | m+1 => num 6+projectionRadius m

private theorem subst_projectionRadius {l : ℕ} (σ : Fin n → PTm l) (m : ℕ) :
    Syn.subst σ (projectionRadius m : PTm n) = (projectionRadius m : PTm l) := by
  induction m with
  | zero => simp [projectionRadius]
  | succ m ih => simp [projectionRadius,ih]

private theorem projection_error (m : ℕ) (p A B : PTm n) (hs : Γ ⊢[PRAAx] source A B) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (recurrenceF m) p (recurrenceData m A B))
      (qmul (orientationPoint m) (qsub (ap2 baseF p (baseData A B)) (truncation m A B)))
      (projectionRadius m) (unit p) := by
  let s := ap2 baseF p (baseData A B)
  have hp := unit_positive (Γ := Γ) p
  induction m with
  | zero =>
    have hc : Γ ⊢[PRAAx] GaussianRationalHorner.canonical s :=
      GaussianNameArithmetic.add_canonical _ _ _ _ _
    have q := (qmul_congr (orientation_even (Γ := Γ) 0 (by decide))
      (GaussianRationalReconstruction.qsub_zero_right s hc)).eqTrans
      ((qmul_commutative _ _).eqTrans (qmul_one_right s hc))
    exact distance_congr (.eqRefl _) q.eqSymm (.eqRefl _) (.eqRefl _) (distance_refl_zero s (unit p) hp)
  | succ m ih =>
    let W := weightedPrimitive m A B
    let F := recurrenceF m
    let X := recurrenceData m A B
    let u := ap2 F p X
    have err := GaussianNamedDifference.sample_error constantF F W X p
      (constant_regular W) (recurrence_regular m A B hs)
    have first := distance_congr (.eqRefl _) (qsub_congr (constant_at p W) (.eqRefl u)) (.eqRefl _) (.eqRefl _) err
    have next := GaussianNamedDifference.difference_distance _ _ _ _ _ _ _ hp (distance_refl_zero W (unit p) hp) ih
    have second := distance_congr (.eqRefl _) (oriented_step m A B s hs.andE₁).eqSymm
      (LeanProofs.IPRA.zero_add _) (.eqRefl _) next
    exact distance_triangle_same _ _ _ _ _ _ hp first second

theorem error_regular (m : ℕ) (A B : PTm n) (hs : Γ ⊢[PRAAx] source A B) :
    Γ ⊢[PRAAx] pointCN errorF (errorData m A B) :=
  GaussianNamedDifference.name_regular _ _ _ _ (base_regular A B hs) (constant_regular _)

theorem oriented_regular (m : ℕ) (A B : PTm n) (hs : Γ ⊢[PRAAx] source A B) :
    Γ ⊢[PRAAx] pointCN orientedF (orientedData m A B) :=
  GaussianBoundedConstantProductName.name_regular _ _ _ _ (.andI (error_regular m A B hs) (constant_bound _))

private def orientedRadius (m : ℕ) : PTm n :=
  constantCap (orientationPoint m)+one+constantCap (orientationPoint m)*num 6

private theorem oriented_error (m : ℕ) (p A B : PTm n) (hs : Γ ⊢[PRAAx] source A B) :
    Γ ⊢[PRAAx] distanceBounded (ap2 orientedF p (orientedData m A B))
      (qmul (orientationPoint m) (qsub (ap2 baseF p (baseData A B)) (truncation m A B)))
      (orientedRadius m) (unit p) := by
  let w := orientationPoint (n := n) m
  let c := truncation m A B
  let x := baseData A B
  let y := errorData m A B
  have hp := unit_positive (Γ := Γ) p
  have first := normalized_product_error errorF w y p (error_regular m A B hs)
  have h := GaussianNamedDifference.sample_error baseF constantF x c p (base_regular A B hs) (constant_regular c)
  have h' := distance_congr (.eqRefl _) (qsub_congr (.eqRefl _) (constant_at p c)) (.eqRefl _) (.eqRefl _) h
  exact distance_triangle_same _ _ _ _ _ _ hp first (fixed_product_distance w _ _ _ _ hp h')

theorem named_truncation (m : ℕ) (A B : PTm n) (hs : Γ ⊢[PRAAx] source A B) :
    Γ ⊢[PRAAx] crossEquivalent (recurrenceF m) orientedF (recurrenceData m A B) (orientedData m A B) := by
  apply GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ (projectionRadius m+orientedRadius m)
    (recurrence_regular m A B hs) (oriented_regular m A B hs)
  refine .allI ?_
  let a := Syn.shift A
  let b := Syn.shift B
  let p : PTm (n+1) := var 0
  let Δ := Γ.map Fm.shift
  have h : Δ ⊢[PRAAx] source a b := by simpa [Δ,a,b,Fm.shift,Syn.shift] using hs.shift
  have hp := unit_positive (Γ := Δ) p
  have e := distance_triangle_same _ _ _ _ _ _ hp (projection_error m p a b h)
    (distance_symmetric _ _ _ _ hp (oriented_error m p a b h))
  simpa [rawDiagonal,Syn.shift,Δ,a,b,p,subst_projectionRadius,orientedRadius,one,
    GaussianCoefficientNameBounds.unit,GaussianEuclideanPointDistance.unit] using e

theorem actual_improper_truncation (m : ℕ) (A B : PTm n) (hs : Γ ⊢[PRAAx] source A B) :
    Γ ⊢[PRAAx] crossEquivalent (GaussianDigammaBernoulliImproperName.nameF m) orientedF
      (GaussianDigammaBernoulliImproperName.data m A B) (orientedData m A B) :=
  cross_trans _ _ _ _ _ _ (original_improper_cross m A B hs) (named_truncation m A B hs)

theorem actual_fixed_order_digamma_truncation_identity_closed (m : ℕ) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (source (var 0) (var 1) ⟶ crossEquivalent (GaussianDigammaBernoulliImproperName.nameF m) orientedF
        (GaussianDigammaBernoulliImproperName.data m (var 0) (var 1)) (orientedData m (var 0) (var 1))) :=
  closeUniv 2 (.impI (actual_improper_truncation m _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianDigammaBernoulliTruncation
