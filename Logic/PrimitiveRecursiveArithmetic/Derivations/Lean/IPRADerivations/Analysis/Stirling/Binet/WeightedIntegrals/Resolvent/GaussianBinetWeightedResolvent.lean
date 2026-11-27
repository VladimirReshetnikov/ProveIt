import IPRADerivations.Analysis.Stirling.Binet.WeightedIntegrals.Resolvent.GaussianBinetWeightedResolventGrid
import IPRADerivations.Analysis.Stirling.Binet.StirlingBounds.GaussianBinetLogCellGrid
import IPRADerivations.Analysis.Stirling.Binet.StirlingBounds.GaussianBinetStirlingUnitDifference

/-!
# Cofinal evaluation of the weighted Binet resolvent

Use the literal weighted sums on the regular unit grid. The canonical
logarithm is observed at a clock that pays for the whole chosen mesh.
The checked unit-cell estimate then identifies the actual regular
weighted-resolvent name with the canonical Stirling unit difference.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianBinetWeightedResolvent

open_ipra
open GaussianBinetLogCellGrid (requiredMesh)
open GaussianBinetStirlingUnitDifference (logDifferenceF logDifferenceData productF productData log_difference_regular)
open GaussianBinetStirlingUnitDifferenceAlgebra (coefficient)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianLogGammaEulerHead (rowData subst_rowData)
open GaussianLogGammaEulerRecurrenceFinite (shift_source)
open GaussianNameArithmetic (multiplyModulus)
open GaussianNameBounds (U sample_bound)
open GaussianNameEquivalence (crossEquivalent cross_at cross_symm point_at point_at_later)
open GaussianNameRingLaws (multiply_sample_error product_right_error)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (positive_product qmul)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalPowerDifference (distance_refl_zero)
open GaussianRationalReciprocal (bound_congr)
open GaussianRationalSyntheticDivision (qone qmul_congr qsub_congr)
open GaussianRightHalfPlaneLogarithm (source)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)
local notation "Lf" => GaussianRightHalfPlaneLogarithm.nameF
local notation "ld" => GaussianRightHalfPlaneLogarithm.data
local notation "targetF" => GaussianBinetStirlingUnitDifference.nameF
local notation "targetData" => GaussianBinetStirlingUnitDifference.data

def mesh (p A B D : PTm n) : PTm n := requiredMesh A B D zero+unit p
def logBudget (D : PTm n) : PTm n := num 4*D*D+num 21

def budget (A B D sign : PTm n) : PTm n :=
  num 7+multiplyModulus constantF logDifferenceF (coefficient A B D sign) (logDifferenceData A B D sign)+
    U constantF (coefficient A B D sign)*logBudget D

ipra_subst mesh

ipra_subst budget [logBudget]

private theorem scaled_log (p A B D sign M : PTm n) (h : Γ ⊢[PRAAx] source A D sign) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] distanceBounded (ap2 Lf p (ld A B D sign)) (ap2 Lf p (ld (M*A) (M*B) (M*D) sign)) two (unit p) := by
  have he := GaussianRightHalfPlaneLogarithmRescale.rescale A B D sign M h hM
  have hp := unit_positive (Γ := Γ) p
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hp hp) hp (le_of_eq_add (d := zero) (by ipra_ring))
    (cross_at _ _ _ _ p p (cross_symm _ _ _ _ he))

private theorem log_data_congr {a b B D sign : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) :
    Γ ⊢[PRAAx] ld a B D sign ≐ ld b B D sign := by
  simpa only [GaussianRightHalfPlaneLogarithm.subst_data,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] using Prf.eqCongr (Γ := Γ) (Ax := PRAAx)
      (ld (var 0) (var 1) (var 2) (var 3) : PTm 4) (σ := ![a,B,D,sign]) (σ' := ![b,B,D,sign])
      (fun i => by fin_cases i; exact h; exact .eqRefl _; exact .eqRefl _; exact .eqRefl _)

private theorem zero_endpoint (p A B D sign M : PTm n) :
    Γ ⊢[PRAAx] GaussianBinetLogCellGrid.endpoint p A B D sign zero M ≐
      qsub (ap2 Lf p (ld (M*(A+D)) (M*B) (M*D) sign)) (ap2 Lf p (ld (M*A) (M*B) (M*D) sign)) :=
  qsub_congr
    (congrAp2 Lf (.eqRefl p) (log_data_congr (by ipra_ring)))
    (congrAp2 Lf (.eqRefl p) (log_data_congr (by ipra_ring)))

private theorem endpoint_error (p s A B D sign M : PTm n) (h : Γ ⊢[PRAAx] source A D sign)
    (hM : Γ ⊢[PRAAx] le one M) (hs : Γ ⊢[PRAAx] le p s) :
    Γ ⊢[PRAAx] distanceBounded (ap2 logDifferenceF p (logDifferenceData A B D sign))
      (GaussianBinetLogCellGrid.endpoint s A B D sign zero M) (num 12) (unit p) := by
  let x := ld (A+D) B D sign
  let y := ld A B D sign
  let d := logDifferenceData A B D sign
  have hp := unit_positive (Γ := Γ) p
  have hu := unit_positive (Γ := Γ) s
  have near := distance_symmetric _ _ _ _ hp
    (point_at_later logDifferenceF d p s (log_difference_regular A B D sign h) hs)
  have read := GaussianNamedDifference.sample_error Lf Lf x y s
    (GaussianRightHalfPlaneLogarithm.regular (A+D) B D sign (shift_source A D sign h))
    (GaussianRightHalfPlaneLogarithm.regular A B D sign h)
  have scaled := GaussianNamedDifference.difference_distance _ _ _ _ _ _ _ hu
    (scaled_log s (A+D) B D sign M (shift_source A D sign h) hM) (scaled_log s A B D sign M h hM)
  have last : Γ ⊢[PRAAx] distanceBounded (ap2 logDifferenceF s d)
      (GaussianBinetLogCellGrid.endpoint s A B D sign zero M) (num 10) (unit s) :=
    distance_congr (.eqRefl _) (zero_endpoint s A B D sign M).eqSymm (by ipra_ring) (.eqRefl _)
      (distance_triangle_same _ _ _ _ _ _ hu read scaled)
  have up := GaussianExponentialReference.dyadic_weaken _ _ _ p s hs last
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hp near up)

theorem logarithm_to_mean (p A B D sign M : PTm n) (h : Γ ⊢[PRAAx] source A D sign)
    (hmesh : Γ ⊢[PRAAx] le (requiredMesh A B D zero) M) (hpM : Γ ⊢[PRAAx] le (unit p) M) :
    Γ ⊢[PRAAx] distanceBounded (ap2 logDifferenceF p (logDifferenceData A B D sign))
      (GaussianBinetReciprocalMean.value A B D sign zero M) (logBudget D) (unit p) := by
  let s := p+M
  let P := unit p
  let S := unit s
  let A₂ := A*A
  have hA := h.andE₁.andE₁
  have hA₂ : Γ ⊢[PRAAx] le one A₂ := positive_product _ _ hA hA
  have hP := unit_positive (Γ := Γ) p
  have hM := le_trans hP hpM
  have hS := unit_positive (Γ := Γ) s
  have hMS : Γ ⊢[PRAAx] le (M*P) S := by
    have grow := le_trans (le_succ_self (Γ := Γ) M) (RationalClosure.succ_le_two_pow M)
    exact le_congr (.eqRefl _) ((mul_comm (unit M) P).eqTrans (pw_add two p M).eqSymm)
      (mul_le_mul_right P grow)
  have hMA : Γ ⊢[PRAAx] le P (M*A₂) :=
    le_trans hpM (le_congr (one_mul M) (mul_comm _ _) (mul_le_mul_right M hA₂))
  have original := GaussianBinetLogCellGrid.finite_grid s A B D sign zero M h hM hmesh
  have estimate : Γ ⊢[PRAAx] distanceBounded (GaussianBinetLogCellGrid.endpoint s A B D sign zero M)
      (GaussianBinetReciprocalMean.value A B D sign zero M) (num 4*D*D+num 9) P := by
    have lifted : Γ ⊢[PRAAx] distanceBounded (GaussianBinetLogCellGrid.endpoint s A B D sign zero M)
        (GaussianBinetReciprocalMean.value A B D sign zero M) (num 4*D*D*S+num 9*(M*M)*A₂) ((M*A₂)*S) :=
      distance_congr (.eqRefl _) (.eqRefl _)
        (by dsimp only [S,A₂,GaussianBinetLogCellGrid.numerator]; ipra_ring)
        (by dsimp only [S,A₂,GaussianBinetLogCellGrid.denominator]; ipra_ring) original
    exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (positive_product _ _ hM hA₂) hS) hP
      (by ipra_le 4*𝔞(D*D)*𝔞(S)*sl hMA+9*𝔞(M*A₂)*sl hMS) lifted
  exact distance_congr (.eqRefl _) (.eqRefl _) (by dsimp only [logBudget]; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hP (endpoint_error p s A B D sign M h hM (le_add_right p M)) estimate)

theorem finite_error (p A B D sign M : PTm n) (h : Γ ⊢[PRAAx] source A D sign)
    (hmesh : Γ ⊢[PRAAx] le (requiredMesh A B D zero) M) (hpM : Γ ⊢[PRAAx] le (unit p) M) :
    Γ ⊢[PRAAx] distanceBounded (GaussianBinetWeightedResolventGrid.value A B D sign M)
      (ap2 targetF p (targetData A B D sign)) (budget A B D sign) (unit p) := by
  let c := coefficient A B D sign
  let d := logDifferenceData A B D sign
  let w := GaussianBinetReciprocalMean.value A B D sign zero M
  let v := productData A B D sign
  have hp := unit_positive (Γ := Γ) p
  have hM := le_trans hp hpM
  have hg := log_difference_regular A B D sign h
  have hc := constant_regular (Γ := Γ) c
  have hv := GaussianBinetStirlingUnitDifference.product_regular A B D sign h
  have near : Γ ⊢[PRAAx] distanceBounded (ap2 logDifferenceF p d) w (logBudget D) (unit p) :=
    logarithm_to_mean p A B D sign M h hmesh hpM
  have cb := bound_congr (constant_at (Γ := Γ) p c) (.eqRefl _) (.eqRefl _)
    (sample_bound constantF c p hc)
  have times := product_right_error c _ w (logBudget D) (unit p) (U logDifferenceF d) (U constantF c) hp near
    (sample_bound logDifferenceF d p hg) cb
  have mul := distance_congr (.eqRefl _) (qmul_congr (constant_at p c) (.eqRefl _)) (.eqRefl _) (.eqRefl _)
    (multiply_sample_error constantF logDifferenceF c d p hc hg)
  have compared := distance_triangle_same _ _ _ _ _ _ hp mul times
  have triv := distance_congr (constant_at (Γ := Γ) p qone).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (distance_refl_zero qone (unit p) hp)
  have read := GaussianNamedDifference.sample_error productF constantF v qone p hv (constant_regular _)
  have joined := distance_triangle_same _ _ _ _ _ _ hp read
    (GaussianNamedDifference.difference_distance _ _ _ _ _ _ _ hp compared triv)
  exact distance_symmetric _ _ _ _ hp
    (distance_congr (.eqRefl _) (GaussianBinetWeightedResolventGrid.finite_identity A B D sign M h hM).eqSymm
      (by dsimp only [c,d,budget]; ipra_ring) (.eqRefl _) joined)

def rawSample (p A B D sign : PTm n) : PTm n := GaussianBinetWeightedResolventGrid.value A B D sign (mesh p A B D)
def rawF : PR 2 := PTm.toPR
  (rawSample (var 0) (fstT (var 1)) (fstT (sndT (var 1))) (fstT (sndT (sndT (var 1)))) (sndT (sndT (sndT (var 1)))) : PTm 2)

ipra_subst rawSample

theorem raw_at (p A B D sign : PTm n) :
    Γ ⊢[PRAAx] ap2 rawF p (rowData A B D sign) ≐ rawSample p A B D sign := by
  simpa [rawF, rowData, pairVector, pairVectorField] using
    (toPR_pairVector_eq (Γ := Γ) (k := 3)
      (rawSample (var 0) (var 1) (var 2) (var 3) (var 4)) p ![A, B, D, sign])

theorem raw_error (p A B D sign : PTm n) (h : Γ ⊢[PRAAx] source A D sign) :
    Γ ⊢[PRAAx] distanceBounded (ap2 rawF p (rowData A B D sign)) (ap2 targetF p (targetData A B D sign))
      (budget A B D sign) (unit p) :=
  distance_congr (raw_at p A B D sign).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (finite_error p A B D sign (mesh p A B D) h (le_add_right _ _) (le_add_left _ _))

private theorem raw_observations (p q A B D sign : PTm n) (h : Γ ⊢[PRAAx] source A D sign) :
    Γ ⊢[PRAAx] distanceBounded (ap2 rawF p (rowData A B D sign)) (ap2 rawF q (rowData A B D sign))
      ((budget A B D sign+one)*(unit p+unit q)) (unit p*unit q) := by
  let K := budget A B D sign
  let P := unit p
  let Q := unit q
  let E := P*Q
  have hp := unit_positive (Γ := Γ) p
  have hq := unit_positive (Γ := Γ) q
  have hE := positive_product _ _ hp hq
  have l := distance_radius_mono _ _ _ _ (K*Q) E hp hE
    (le_of_eq_add (d := zero) (by dsimp only [E]; ipra_ring)) (raw_error p A B D sign h)
  have r := distance_radius_mono _ _ _ _ (K*P) E hq hE
    (le_of_eq_add (d := zero) (by dsimp only [E]; ipra_ring)) (raw_error q A B D sign h)
  have m := point_at targetF (targetData A B D sign) p q (GaussianBinetStirlingUnitDifference.regular A B D sign h)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by dsimp only [K,P,Q]; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hE (distance_triangle_same _ _ _ _ _ _ hE l m)
      (distance_symmetric _ _ _ _ hE r))

theorem raw_regular (A B D sign : PTm n) (h : Γ ⊢[PRAAx] source A D sign) :
    Γ ⊢[PRAAx] GaussianFastValueCut.regular rawF (budget A B D sign+one) (rowData A B D sign) := by
  refine .allI (.allI ?_)
  let s (v : PTm n) := Syn.shift (Syn.shift v)
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] source (s A) (s D) (s sign) := by
    simpa [Fm.shift,Syn.shift,s,source,GaussianRightHalfPlaneArgument.source] using h.shift.shift
  simpa only [GaussianFastValueCut.regular,Syn.shift,s,subst_budget,subst_rowData,PTm.subst_add,
    one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    raw_observations (var 1) (var 0) (s A) (s B) (s D) (s sign) hs

abbrev nameF : PR 2 := GaussianFastValueCut.nameF rawF
def data (A B D sign : PTm n) : PTm n := GaussianFastValueCut.nameData (budget A B D sign+one) (rowData A B D sign)
def clock (p A B D sign : PTm n) : PTm n := GaussianFastValueCut.exponent (budget A B D sign+one) p

ipra_subst data [one]

theorem sample_at (p A B D sign : PTm n) :
    Γ ⊢[PRAAx] ap2 nameF p (data A B D sign) ≐ rawSample (clock p A B D sign) A B D sign :=
  (GaussianFastValueCut.name_at rawF (budget A B D sign+one) (rowData A B D sign) p).eqTrans
    ((GaussianNameArithmetic.recode_congr (raw_at (clock p A B D sign) A B D sign)).eqTrans
      (GaussianExponentialReference.recode_fixed _ (GaussianRationalHorner.qmul_canonical _ _)))

theorem regular (A B D sign : PTm n) (h : Γ ⊢[PRAAx] source A D sign) :
    Γ ⊢[PRAAx] pointCN nameF (data A B D sign) :=
  GaussianFastValueCut.name_fast rawF _ _ (raw_regular A B D sign h)

private theorem error_at (p A B D sign : PTm n) (h : Γ ⊢[PRAAx] source A D sign) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (data A B D sign)) (ap2 targetF p (targetData A B D sign))
      (budget A B D sign+two) (unit p) := by
  let s := clock p A B D sign
  have hp := unit_positive (Γ := Γ) p
  have later : Γ ⊢[PRAAx] le p s := le_add_right _ _
  have raw := distance_congr (sample_at p A B D sign).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (distance_congr (raw_at s A B D sign) (.eqRefl _) (.eqRefl _) (.eqRefl _) (raw_error s A B D sign h))
  have compare := GaussianExponentialReference.dyadic_weaken _ _ _ p s later raw
  have point := point_at_later targetF (targetData A B D sign) p s
    (GaussianBinetStirlingUnitDifference.regular A B D sign h) later
  exact distance_triangle_same _ _ _ _ _ _ hp compare point

theorem equivalent (A B D sign : PTm n) (h : Γ ⊢[PRAAx] source A D sign) :
    Γ ⊢[PRAAx] crossEquivalent nameF targetF (data A B D sign) (targetData A B D sign) := by
  refine GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ (budget A B D sign+two)
    (regular A B D sign h) (GaussianBinetStirlingUnitDifference.regular A B D sign h) (.allI ?_)
  let s (v : PTm n) := Syn.shift v
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (s A) (s D) (s sign) := by
    simpa [Fm.shift,Syn.shift,s,source,GaussianRightHalfPlaneArgument.source] using h.shift
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal,Syn.shift,s,subst_budget,subst_data,
    GaussianBinetStirlingUnitDifference.subst_data,PTm.subst_add,two,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    error_at (var 0) (s A) (s B) (s D) (s sign) hs

theorem remainder_difference (A B D sign x : PTm n) (h : Γ ⊢[PRAAx] source A D sign) :
    Γ ⊢[PRAAx] crossEquivalent GaussianBinetStirlingUnitDifference.remainderDifferenceF nameF
      (GaussianBinetStirlingUnitDifference.remainderDifferenceData A B D sign x) (data A B D sign) :=
  GaussianNameEquivalence.cross_trans _ _ _ _ _ _
    (GaussianBinetStirlingUnitDifference.recurrence A B D sign x h)
    (cross_symm _ _ _ _ (equivalent A B D sign h))

theorem actual_weighted_resolvent_limit_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (source (var 0) (var 2) (var 3) ⟶ pointCN nameF (data (var 0) (var 1) (var 2) (var 3)) ⋏
        crossEquivalent nameF targetF (data (var 0) (var 1) (var 2) (var 3)) (targetData (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (.andI (regular _ _ _ _ Prf.hyp0) (equivalent _ _ _ _ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBinetWeightedResolvent
