import IPRADerivations.Analysis.GaussianStirlingGammaLogShift
import IPRADerivations.Analysis.GaussianStirlingRationalLogShift
import IPRADerivations.Analysis.GaussianStirlingDifferenceAlgebra
import IPRADerivations.Analysis.GaussianNamedDifference

/-!
# Exact named Stirling difference at every positive rational argument

The two logarithmic increment laws are applied at the actual names.
A uniform dyadic observation budget transports the exact cleared
rational computation to their independent clocks.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianStirlingRecurrence

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData multiplyModulus sum_distance)
open GaussianNameBounds (U sample_bound)
open GaussianNameEquivalence (crossEquivalent cross_to_diagonal diagonal_at)
open GaussianNameRingLaws (add_sample_error multiply_sample_error product_right_error through_identity)
open GaussianNamedDifference (difference_distance)
open GaussianRationalDistanceOrder (distance_congr distance_triangle_same)
open GaussianRationalHorner (qadd qmul)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalPowerDifference (distance_refl_zero)
open GaussianRationalSyntheticDivision (qone qadd_congr qmul_congr)
open GaussianStirlingDifferenceAlgebra (rawA rawDifference difference_value)
open GaussianStirlingNames (source source_shift logGammaF logGammaData log_gamma_regular logXF logXData log_x_regular
  offset point productF productData product_regular nameF nameData name_regular)
open Syn
open scoped Fm
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "three" => GaussianNameRingLaws.three
local notation "dF" => GaussianStirlingDifference.nameF
local notation "dData" => GaussianStirlingDifference.data

def scaleBudget (f : PR 2) (c x C : PTm n) : PTm n :=
  multiplyModulus constantF f c x+one+U constantF c*C

private theorem constant_mul_error (f : PR 2) (c x r p C : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hr : Γ ⊢[PRAAx] distanceBounded (ap2 f p x) r C (unit p)) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (multiplyF constantF f) p (multiplyData constantF f c x))
      (qmul c r) (scaleBudget f c x C) (unit p) := by
  have hC := constant_regular (Γ := Γ) c
  have ep := multiply_sample_error constantF f c x p hC hf
  have aq := qmul_congr (constant_at (Γ := Γ) p c) (.eqRefl (ap2 f p x))
  have hp := unit_positive (Γ := Γ) p
  have bv := GaussianRationalReciprocal.bound_congr (constant_at (Γ := Γ) p c) (.eqRefl _) (.eqRefl _)
    (sample_bound constantF c p hC)
  have last := product_right_error c _ r C (unit p) (U f x) (U constantF c) hp hr (sample_bound f x p hf) bv
  exact distance_triangle_same _ _ _ _ _ _ hp (distance_congr (.eqRefl _) aq (.eqRefl _) (.eqRefl _) ep) last

def aBudget (a b G L : PTm n) : PTm n :=
  three+((num 6+(G+scaleBudget logXF (offset a b) (logXData a b) L))+LeanProofs.ConciseIPRA.PTm.zero)

theorem a_error (p a b g l G L : PTm n) (ha : Γ ⊢[PRAAx] source a b)
    (hg : Γ ⊢[PRAAx] distanceBounded (ap2 logGammaF p (logGammaData a b)) g G (unit p))
    (hl : Γ ⊢[PRAAx] distanceBounded (ap2 logXF p (logXData a b)) l L (unit p)) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (nameData a b)) (rawA a b g l) (aBudget a b G L) (unit p) := by
  let D := GaussianNamedDifference.nameF logGammaF productF
  let dX := GaussianNamedDifference.data (logGammaData a b) (productData a b)
  let c := point a b
  have hp := unit_positive (Γ := Γ) p
  have hG := log_gamma_regular a b ha
  have hL := log_x_regular a b ha
  have hP := product_regular a b ha
  have hc := constant_regular (Γ := Γ) c
  have hD := GaussianNamedDifference.name_regular logGammaF productF (logGammaData a b) (productData a b) hG hP
  have w := constant_mul_error logXF (offset a b) (logXData a b) l p L hL hl
  have d := GaussianNamedDifference.sample_error logGammaF productF (logGammaData a b) (productData a b) p hG hP
  have d' := distance_triangle_same _ _ _ _ _ _ hp d
    (difference_distance _ _ _ _ _ _ _ hp hg w)
  have c' := distance_congr (constant_at (Γ := Γ) p c).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (distance_refl_zero c (unit p) hp)
  have final := sum_distance _ _ _ _ _ _ _ hp d' c'
  exact distance_triangle_same _ _ _ _ _ _ hp (add_sample_error D constantF dX c p hD hc) final

def dBudget (a b : PTm n) : PTm n :=
  three+(scaleBudget GaussianPositiveRationalLogarithm.logF (GaussianStirlingDifference.coefficient a b)
    (GaussianStirlingDifference.logData a b) LeanProofs.ConciseIPRA.PTm.zero+LeanProofs.ConciseIPRA.PTm.zero)

private theorem d_error (p a b : PTm n) (ha : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] distanceBounded (ap2 dF p (dData a b))
      (rawDifference a b (ap2 GaussianPositiveRationalLogarithm.logF p (GaussianStirlingDifference.logData a b)))
      (dBudget a b) (unit p) := by
  let L := GaussianPositiveRationalLogarithm.logF
  let x := GaussianStirlingDifference.logData a b
  let c := GaussianStirlingDifference.coefficient a b
  let m : PTm n := GaussianStirlingDifference.minusOne
  have hp := unit_positive (Γ := Γ) p
  have hL := GaussianStirlingDifference.log_regular a b ha.andE₁
  have hm := constant_regular (Γ := Γ) m
  have first := add_sample_error GaussianStirlingDifference.productF constantF (GaussianStirlingDifference.productData a b)
    m p (GaussianStirlingDifference.product_regular a b ha.andE₁) hm
  have leg := constant_mul_error L c x (ap2 L p x) p _ hL (distance_refl_zero _ _ hp)
  have one := distance_congr (constant_at (Γ := Γ) p m).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (distance_refl_zero m (unit p) hp)
  exact distance_triangle_same _ _ _ _ _ _ hp first (sum_distance _ _ _ _ _ _ _ hp leg one)

abbrev differenceF : PR 2 := GaussianNamedDifference.nameF nameF nameF
def differenceInput (a b : PTm n) : PTm n := GaussianNamedDifference.data (nameData a b) (nameData (a+b) b)
def incrementBudget : PTm n := two+three

private theorem sum_error (f g h : PR 2) (p x y z : PTm n) (hg : Γ ⊢[PRAAx] pointCN g y)
    (hh : Γ ⊢[PRAAx] pointCN h z) (he : Γ ⊢[PRAAx] crossEquivalent f (addF g h) x (addData y z)) :
    Γ ⊢[PRAAx] distanceBounded (ap2 f p x) (qadd (ap2 g p y) (ap2 h p z)) incrementBudget (unit p) :=
  distance_triangle_same _ _ _ _ _ _ (unit_positive p)
    (diagonal_at _ _ _ _ p (cross_to_diagonal _ _ _ _ he))
    (add_sample_error g h y z p hg hh)

def recurrenceBudget (a b : PTm n) : PTm n :=
  (num 6+(aBudget a b LeanProofs.ConciseIPRA.PTm.zero LeanProofs.ConciseIPRA.PTm.zero+
    aBudget (a+b) b incrementBudget incrementBudget))+dBudget a b

private theorem subst_budget {m : ℕ} (σ : Fin n → PTm m) (a b : PTm n) :
    Syn.subst σ (recurrenceBudget a b) = recurrenceBudget (Syn.subst σ a) (Syn.subst σ b) := by
  simp [recurrenceBudget,aBudget,dBudget,scaleBudget,incrementBudget,GaussianNameRingLaws.three,one,two]

@[simp] theorem subst_differenceInput {m : ℕ} (σ : Fin n → PTm m) (a b : PTm n) :
    Syn.subst σ (differenceInput a b) = differenceInput (Syn.subst σ a) (Syn.subst σ b) := by
  simp [differenceInput]

set_option maxHeartbeats 1800000 in
theorem recurrence_error (p a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] distanceBounded (ap2 differenceF p (differenceInput a b)) (ap2 dF p (dData a b))
      (recurrenceBudget a b) (unit p) := by
  let A := nameData a b
  let B := nameData (a+b) b
  let g := ap2 logGammaF p (logGammaData a b)
  let l := ap2 logXF p (logXData a b)
  let F := GaussianPositiveRationalLogarithm.logF
  let T := GaussianStirlingDifference.logData a b
  let t := ap2 F p T
  have hShift := source_shift a b hs
  have hp := unit_positive (Γ := Γ) p
  have gReg := log_gamma_regular a b hs
  have lReg := log_x_regular a b hs
  have tReg := GaussianStirlingDifference.log_regular a b hs.andE₁
  have gInc : Γ ⊢[PRAAx] distanceBounded (ap2 logGammaF p (logGammaData (a+b) b)) (qadd l g)
      incrementBudget (unit p) := sum_error logGammaF logXF logGammaF p (logGammaData (a+b) b)
    (logXData a b) (logGammaData a b) lReg gReg (GaussianStirlingGammaLogShift.log_gamma_increment a b hs)
  have lInc : Γ ⊢[PRAAx] distanceBounded (ap2 logXF p (logXData (a+b) b)) (qadd l t)
      incrementBudget (unit p) := sum_error logXF logXF F p (logXData (a+b) b)
    (logXData a b) T lReg tReg (GaussianStirlingRationalLogShift.increment a b hs)
  have a0 := a_error p a b g l _ _ hs (distance_refl_zero g _ hp) (distance_refl_zero l _ hp)
  have a1 := a_error p (a+b) b (qadd l g) (qadd l t) _ _ hShift gInc lInc
  have exactDifference := GaussianNamedDifference.sample_error nameF nameF A B p (name_regular a b hs)
    (name_regular (a+b) b hShift)
  have v := distance_triangle_same _ _ _ _ _ _ hp exactDifference (difference_distance _ _ _ _ _ _ _ hp a0 a1)
  exact through_identity _ _ _ _ _ _ _ hp v (d_error p a b hs) (difference_value a b g l t hs.andE₂)

set_option maxHeartbeats 1800000 in
theorem recurrence (a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] crossEquivalent differenceF dF (differenceInput a b) (dData a b) := by
  have hShift := source_shift a b hs
  refine GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ (recurrenceBudget a b)
    (GaussianNamedDifference.name_regular nameF nameF (nameData a b) (nameData (a+b) b) (name_regular a b hs)
      (name_regular (a+b) b hShift))
    (GaussianStirlingDifference.name_regular a b hs.andE₁ hs.andE₂) (.allI ?_)
  have h : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift a) (Syn.shift b) := by
    simpa only [Fm.shift,Syn.shift,GaussianStirlingGammaLogarithm.subst_source] using hs.shift
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal,Syn.shift,subst_budget,subst_differenceInput,
    GaussianStirlingDifference.subst_data] using recurrence_error (var 0) (Syn.shift a) (Syn.shift b) h

set_option maxHeartbeats 1800000 in
theorem actual_positive_rational_Stirling_recurrence_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (source (var 0) (var 1) ⟶ crossEquivalent differenceF dF (differenceInput (var 0) (var 1))
      (dData (var 0) (var 1))) :=
  closeUniv 2 (.impI (recurrence _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianStirlingRecurrence
