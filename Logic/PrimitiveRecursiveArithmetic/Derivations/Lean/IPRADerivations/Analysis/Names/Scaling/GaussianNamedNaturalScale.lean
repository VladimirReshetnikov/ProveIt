import IPRADerivations.Analysis.RationalArithmetic.Scaling.GaussianRationalNaturalScale
import IPRADerivations.Analysis.Names.Arithmetic.GaussianNameRingLaws
import IPRADerivations.Analysis.Exponential.Names.Evaluators.GaussianRadiusExponentialName
import IPRADerivations.Analysis.RationalArithmetic.OrderBounds.RationalClosure
import IPRADerivations.Analysis.Exponential.Names.Evaluators.GaussianExponentialReference

/-!
# Actual capped natural multiples of Gaussian names

One numerical cap E fixes the SAME original observation clock at every
stage i. Actual native numerator scaling and the existing normalized
addition program therefore give a literal successor observation rule.
All stages remain actual fixed-arity programs; no name induction or
recursively generated family of host functions is introduced.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianNamedNaturalScale

open_ipra
open GaussianRationalNaturalScale (natScale naturalPoint)
open GaussianRationalHorner (canonical qadd qmul ofGaussian positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameEquivalence (crossEquivalent point_at)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def clock (p E : PTm n) : PTm n := p+E+two
def amplification (E : PTm n) : PTm n := pw two (E+two)
def value (f : PR 2) (p E i x : PTm n) : PTm n := natScale i (ap2 f (clock p E) x)
def data (E i x : PTm n) : PTm n := pairT E (pairT i x)
def nameF (f : PR 2) : PR 2 := PTm.toPR
  (value f (var 0) (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1))))
def sample (f : PR 2) (p E i x : PTm n) : PTm n := ap2 (nameF f) p (data E i x)

ipra_subst clock
ipra_subst amplification
ipra_subst value
ipra_subst data
ipra_subst sample

theorem value_congr (f : PR 2) {p E i x q D j y : PTm n} (hp : Γ ⊢[PRAAx] p ≐ q) (hE : Γ ⊢[PRAAx] E ≐ D)
    (hi : Γ ⊢[PRAAx] i ≐ j) (hx : Γ ⊢[PRAAx] x ≐ y) : Γ ⊢[PRAAx] value f p E i x ≐ value f q D j y := by
  ipra_congr (value f (var 0) (var 1) (var 2) (var 3) : PTm 4) with [hp, hE, hi, hx]
theorem sample_at (f : PR 2) (p E i x : PTm n) : Γ ⊢[PRAAx] sample f p E i x ≐ value f p E i x := by
  have raw : Γ ⊢[PRAAx] sample f p E i x ≐ value f p (fstT (data E i x)) (fstT (sndT (data E i x))) (sndT (sndT (data E i x))) := by
    simpa only [sample,nameF,ap2,subst_value,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons] using
      toPR_eq (Γ := Γ) (value f (var 0) (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1))) : PTm 2) ![p,data E i x]
  exact raw.eqTrans (value_congr f (.eqRefl _) (fst_pair _ _) (snd_pair _ _).fstE
    (snd_pair _ _).sndE)

theorem clock_later (p E : PTm n) : Γ ⊢[PRAAx] le p (clock p E) := le_trans (le_add_right p E) (le_add_right _ two)
theorem clock_unit (p E : PTm n) : Γ ⊢[PRAAx] unit (clock p E) ≐ unit p*amplification E :=
  (congrAp2 powF (by unfold clock; ipra_ring) (.eqRefl _)).eqTrans (pw_add two p (E+two))
theorem cap_budget (E i : PTm n) (hi : Γ ⊢[PRAAx] le i E) : Γ ⊢[PRAAx] le i (amplification E) :=
  le_trans hi (le_trans (le_trans (le_succ_self E) (RationalClosure.succ_le_two_pow E))
    (GaussianFactorBudget.power_monotone_length two E (E+two) (le_succ_self one) (le_add_right E two)))

theorem natural_point_bound (i : PTm n) : Γ ⊢[PRAAx] bounded (naturalPoint i) i one := by
  apply GaussianRationalMetric.bounded_of_cleared _ _ _ _ _ (le_refl one) (le_refl one)
    (GaussianRationalNaturalScale.natural_point_represents i)
  exact le_congr ((congrMul (.eqRefl _) (ComplexLogarithmRemainder.normSq_scale i ComplexLogarithmRemainder.oneCode)).eqTrans
    (by have e := natEq (ComplexLogarithmRemainder.normSq_one (Γ := Γ)); apply deriveNat; ipra_simps; rw [e]; ring)).eqSymm
    (by ipra_ring) (le_refl (i*i))

theorem scaled_bound (i q R : PTm n) (hq : Γ ⊢[PRAAx] bounded q R one) : Γ ⊢[PRAAx] bounded (natScale i q) (i*R) one :=
  GaussianRationalReciprocal.bound_congr (GaussianRationalNaturalScale.natScale_as_product i q).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianRationalReciprocal.bounded_product_one (natural_point_bound i) hq)

theorem scaled_distance (i q r A B R : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hqr : Γ ⊢[PRAAx] distanceBounded q r A B) (hr : Γ ⊢[PRAAx] bounded r R one) : Γ ⊢[PRAAx]
    distanceBounded (natScale i q) (natScale i r) (i*A) B := by
  have h := GaussianNameRingLaws.product_left_error q r (naturalPoint i) A B i R hB hqr (natural_point_bound i) hr
  exact distance_congr
    ((GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans (GaussianRationalNaturalScale.natScale_as_product i q).eqSymm)
    ((GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans (GaussianRationalNaturalScale.natScale_as_product i r).eqSymm)
    (mul_comm _ _) (.eqRefl _) h

theorem value_regularity (f : PR 2) (p q E i R x : PTm n) (hf : Γ ⊢[PRAAx] GaussianRadiusExponentialName.input f R x)
    (hi : Γ ⊢[PRAAx] le i E) : Γ ⊢[PRAAx]
    distanceBounded (value f p E i x) (value f q E i x) (unit p+unit q) (unit p*unit q) := by
  have native := scaled_distance i _ _ _ _ R
    (positive_product _ _ (unit_positive (clock p E)) (unit_positive (clock q E)))
    (point_at f x (clock p E) (clock q E) hf.andE₁)
    (GaussianRadiusExponentialName.bounded_samples_at f R x (clock q E) hf.andE₂)
  have a := natEq (clock_unit (Γ := Γ) p E)
  have b := natEq (clock_unit (Γ := Γ) q E)
  have budget := cap_budget (Γ := Γ) E i hi
  apply distance_radius_mono _ _ _ _ _ _
    (positive_product _ _ (unit_positive (clock p E)) (unit_positive (clock q E)))
    (positive_product _ _ (unit_positive p) (unit_positive q)) _ native
  ipra_le (𝔞(unit p)+𝔞(unit q))*𝔞(unit p)*𝔞(unit q)*𝔞(amplification E)*sl budget using
    rw [a,b]
    ring


def radius (E R : PTm n) : PTm n := E*R+one
ipra_subst radius
theorem sample_canonical (f : PR 2) (p E i x : PTm n) : Γ ⊢[PRAAx] canonical (sample f p E i x) :=
  GaussianRationalHorner.canonical_congr (sample_at f p E i x) (GaussianRationalNaturalScale.natScale_canonical _ _)
theorem sample_regularity (f : PR 2) (p q E i R x : PTm n) (hf : Γ ⊢[PRAAx] GaussianRadiusExponentialName.input f R x)
    (hi : Γ ⊢[PRAAx] le i E) : Γ ⊢[PRAAx]
    distanceBounded (sample f p E i x) (sample f q E i x) (unit p+unit q) (unit p*unit q) :=
  distance_congr (sample_at f p E i x).eqSymm (sample_at f q E i x).eqSymm (.eqRefl _) (.eqRefl _) (value_regularity f p q E i R x hf hi)
theorem name_regular (f : PR 2) (E i R x : PTm n) (hf : Γ ⊢[PRAAx] GaussianRadiusExponentialName.input f R x)
    (hi : Γ ⊢[PRAAx] le i E) : Γ ⊢[PRAAx] pointCN (nameF f) (data E i x) := by
  refine .allI (.allI ?_)
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] GaussianRadiusExponentialName.input f (Syn.shift (Syn.shift R)) (Syn.shift (Syn.shift x)) := by
    simpa [Fm.shift,Syn.shift] using hf.shift.shift
  have is : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] le (Syn.shift (Syn.shift i)) (Syn.shift (Syn.shift E)) := by
    simpa [Fm.shift,Syn.shift] using hi.shift.shift
  simpa only [pointCN,sample,subst_data,Syn.shift,unit,GaussianEuclideanPointDistance.unit] using
    sample_regularity f (var 1) (var 0) (Syn.shift (Syn.shift E)) (Syn.shift (Syn.shift i))
      (Syn.shift (Syn.shift R)) (Syn.shift (Syn.shift x)) hs is

theorem sample_bound (f : PR 2) (p E i R x : PTm n) (hf : Γ ⊢[PRAAx] GaussianRadiusExponentialName.input f R x)
    (hi : Γ ⊢[PRAAx] le i E) : Γ ⊢[PRAAx] bounded (sample f p E i x) (radius E R) one := by
  have bound := scaled_bound i _ R (GaussianRadiusExponentialName.bounded_samples_at f R x (clock p E) hf.andE₂)
  have grown : Γ ⊢[PRAAx] le (i*R) (radius E R) :=
    le_trans (AnalyticNumberTheory.PhiLower.le_mul_mono hi (le_refl R)) (le_add_right (E*R) one)
  exact GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ (le_refl one) (le_refl one)
    (le_congr (by ipra_ring) (by ipra_ring) grown)
    (GaussianRationalReciprocal.bound_congr (sample_at f p E i x).eqSymm (.eqRefl _) (.eqRefl _) bound)

theorem exponential_input (f : PR 2) (E i R x : PTm n) (hf : Γ ⊢[PRAAx] GaussianRadiusExponentialName.input f R x)
    (hi : Γ ⊢[PRAAx] le i E) : Γ ⊢[PRAAx] GaussianRadiusExponentialName.input (nameF f) (radius E R) (data E i x) := by
  refine .andI (name_regular f E i R x hf hi) (.allI ?_)
  have hs : Γ.map Fm.shift ⊢[PRAAx] GaussianRadiusExponentialName.input f (Syn.shift R) (Syn.shift x) := by
    simpa [Fm.shift,Syn.shift] using hf.shift
  have is : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift i) (Syn.shift E) := by simpa [Fm.shift,Syn.shift] using hi.shift
  simpa only [GaussianRadiusExponentialName.boundedSamples,sample,subst_data,subst_radius,Syn.shift] using
    sample_bound f (var 0) (Syn.shift E) (Syn.shift i) (Syn.shift R) (Syn.shift x) hs is

theorem sample_zero (f : PR 2) (p E x : PTm n) : Γ ⊢[PRAAx] sample f p E zero x ≐ GaussianRationalHorner.qzero :=
  (sample_at f p E zero x).eqTrans (GaussianRationalNaturalScale.natScale_zero _)
theorem sample_one (f : PR 2) (p E x : PTm n) : Γ ⊢[PRAAx]
    sample f p E one x ≐ GaussianFastValueCut.recode (ap2 f (clock p E) x) :=
  (sample_at f p E one x).eqTrans ((GaussianRationalNaturalScale.natScale_one _).eqTrans
    ((GaussianReciprocalHorner.qadd_commutative _ _).eqTrans (GaussianNameRingLaws.add_zero_recode _)))

theorem one_observation (f : PR 2) (p q E R x : PTm n) (hf : Γ ⊢[PRAAx] GaussianRadiusExponentialName.input f R x) : Γ ⊢[PRAAx]
    distanceBounded (sample f p E one x) (ap2 f q x) (unit p+unit q) (unit p*unit q) := by
  have grow : Γ ⊢[PRAAx] le (unit p) (unit (clock p E)) :=
    GaussianFactorBudget.power_monotone_length two _ _ (le_succ_self one) (clock_later p E)
  have old := GaussianNameRingLaws.recode_left_distance _ _ _ _
    (positive_product _ _ (unit_positive (clock p E)) (unit_positive q))
    (point_at f x (clock p E) q hf.andE₁)
  apply distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (unit_positive (clock p E)) (unit_positive q))
    (positive_product _ _ (unit_positive p) (unit_positive q)) _
    (distance_congr (sample_one f p E x).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) old)
  ipra_le 𝔞(unit q)*𝔞(unit q)*sl grow

theorem one_cross (f : PR 2) (E R x : PTm n) (hf : Γ ⊢[PRAAx] GaussianRadiusExponentialName.input f R x) : Γ ⊢[PRAAx]
    crossEquivalent (nameF f) f (data E one x) x := by
  refine .allI (.allI ?_)
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] GaussianRadiusExponentialName.input f (Syn.shift (Syn.shift R)) (Syn.shift (Syn.shift x)) := by
    simpa [Fm.shift,Syn.shift] using hf.shift.shift
  simpa only [crossEquivalent,sample,subst_data,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift,unit,GaussianEuclideanPointDistance.unit] using
    one_observation f (var 1) (var 0) (Syn.shift (Syn.shift E)) (Syn.shift (Syn.shift R)) (Syn.shift (Syn.shift x)) hs

def addData (E i x : PTm n) : PTm n := GaussianNameArithmetic.addData (data E i x) (data E one x)
ipra_subst addData

/-- Literal actual addition uses its own normalizer query, but all stage
inputs share their fixed-cap original observation clock at that query. -/
theorem add_step_at (f : PR 2) (p E i x : PTm n) : Γ ⊢[PRAAx]
    ap2 (GaussianNameArithmetic.addF (nameF f) (nameF f)) p (addData E i x) ≐
      sample f (GaussianFastValueCut.exponent two p) E (succ i) x := by
  let s := GaussianFastValueCut.exponent two p
  have native : Γ ⊢[PRAAx] qadd (sample f s E i x) (sample f s E one x) ≐ sample f s E (succ i) x :=
    (GaussianRationalSyntheticDivision.qadd_congr (sample_at f s E i x) (sample_at f s E one x)).eqTrans
      ((GaussianRationalNaturalScale.natScale_add i one _).eqSymm.eqTrans
        ((GaussianRationalNaturalScale.natScale_congr (succ_eq_add_one i).eqSymm (.eqRefl _)).eqTrans (sample_at f s E (succ i) x).eqSymm))
  exact (GaussianNameArithmetic.add_at (nameF f) (nameF f) _ _ p).eqTrans
    ((GaussianNameArithmetic.recode_congr native).eqTrans
      (GaussianExponentialReference.recode_fixed _ (sample_canonical f s E (succ i) x)))

theorem add_step_cross (f : PR 2) (E i R x : PTm n) (hf : Γ ⊢[PRAAx] GaussianRadiusExponentialName.input f R x)
    (hi : Γ ⊢[PRAAx] le (succ i) E) : Γ ⊢[PRAAx]
    crossEquivalent (GaussianNameArithmetic.addF (nameF f) (nameF f)) (nameF f) (addData E i x) (data E (succ i) x) := by
  refine .allI (.allI ?_)
  let D := (Γ.map Fm.shift).map Fm.shift
  let Es := Syn.shift (Syn.shift E)
  let is := Syn.shift (Syn.shift i)
  let Rs := Syn.shift (Syn.shift R)
  let xs := Syn.shift (Syn.shift x)
  let p : PTm (n+2) := var 1
  let q : PTm (n+2) := var 0
  let s := GaussianFastValueCut.exponent two p
  have hs : D ⊢[PRAAx] GaussianRadiusExponentialName.input f Rs xs := by simpa [D,Rs,xs,Fm.shift,Syn.shift] using hf.shift.shift
  have ih : D ⊢[PRAAx] le (succ is) Es := by simpa [D,is,Es,Fm.shift,Syn.shift] using hi.shift.shift
  have grow : D ⊢[PRAAx] le (unit p) (unit s) :=
    GaussianFactorBudget.power_monotone_length two p s (le_succ_self one) (le_add_right _ _)
  have old := point_at (nameF f) (data Es (succ is) xs) s q (name_regular f Es (succ is) Rs xs hs ih)
  have compared : D ⊢[PRAAx] distanceBounded (sample f s Es (succ is) xs) (sample f q Es (succ is) xs)
      (unit p+unit q) (unit p*unit q) := by
    apply distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (unit_positive s) (unit_positive q))
      (positive_product _ _ (unit_positive p) (unit_positive q)) _ old
    ipra_le Groth.ι (IPRA.Q.mk D (unit q))*Groth.ι (IPRA.Q.mk D (unit q))*sl grow
  have result := distance_congr (add_step_at f p Es is xs).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) compared
  simpa only [crossEquivalent,sample,subst_addData,subst_data,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift,unit,GaussianEuclideanPointDistance.unit,
    D,Es,is,Rs,xs,p,q] using result


theorem radius_positive (E R : PTm n) : Γ ⊢[PRAAx] le one (radius E R) :=
  le_congr (.eqRefl _) (by unfold radius; ipra_ring) (le_add_right one (E*R))

theorem actual_scaled_sample_program_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (sample f (var 0) (var 1) (var 2) (var 3) ≐
      natScale (var 2) (ap2 f (clock (var 0) (var 1)) (var 3)) ⋏
        canonical (sample f (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.andI (sample_at f _ _ _ _) (sample_canonical f _ _ _ _))

theorem original_capped_scale_input_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (GaussianRadiusExponentialName.input f (var 2) (var 3) ⟶ le (var 1) (var 0) ⟶
      GaussianRadiusExponentialName.input (nameF f) (radius (var 0) (var 2)) (data (var 0) (var 1) (var 3))) :=
  closeUniv 4 (.impI (.impI (exponential_input f _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem actual_scaled_zero_sample_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (sample f (var 0) (var 1) zero (var 2) ≐ GaussianRationalHorner.qzero) :=
  closeUniv 3 (sample_zero f _ _ _)

theorem original_scaled_one_equivalence_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (GaussianRadiusExponentialName.input f (var 1) (var 2) ⟶
      crossEquivalent (nameF f) f (data (var 0) one (var 2)) (var 2)) :=
  closeUniv 3 (.impI (one_cross f _ _ _ Prf.hyp0))

theorem actual_scaled_addition_successor_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (ap2 (GaussianNameArithmetic.addF (nameF f) (nameF f)) (var 0) (addData (var 1) (var 2) (var 3)) ≐
      sample f (GaussianFastValueCut.exponent two (var 0)) (var 1) (succ (var 2)) (var 3)) :=
  closeUniv 4 (add_step_at f _ _ _ _)

theorem original_scaled_addition_successor_equivalence_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (GaussianRadiusExponentialName.input f (var 2) (var 3) ⟶ le (succ (var 1)) (var 0) ⟶
      crossEquivalent (GaussianNameArithmetic.addF (nameF f) (nameF f)) (nameF f)
        (addData (var 0) (var 1) (var 3)) (data (var 0) (succ (var 1)) (var 3))) :=
  closeUniv 4 (.impI (.impI (add_step_cross f _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianNamedNaturalScale
