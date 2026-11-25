import IPRADerivations.Analysis.GaussianNamedPositiveLogarithm
import IPRADerivations.Analysis.GaussianEulerCompactExhaustionNormalization

/-!
# Reciprocal of a positive real name with a supplied compact margin

Every selected source observation has a positive decoded numerator and
denominator. The reciprocal program swaps those integers and normalizes
at the clock paid for by the squared inverse margin.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedPositiveReciprocal

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianNamedPositiveLogarithm (source numerator denominator decoded_domain decoded_value)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianApproximateInverseDistance (central_distance)
open GaussianRationalHorner (canonical qmul positive_product)
open GaussianRationalReciprocal (qone)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameEquivalence (point_at)
open GaussianFastValueCut (exponent query_budget)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def clock (p E : PTm n) : PTm n := exponent (E*E) p
def observation (f : PR 2) (p x E : PTm n) : PTm n :=
  fraction (denominator f (clock p E) x) (numerator f (clock p E) x)
def data (x E : PTm n) : PTm n := pairT x E
def nameF (f : PR 2) : PR 2 := PTm.toPR (observation f (var 0) (fstT (var 1)) (sndT (var 1)))

@[simp] theorem subst_observation {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (p x E : PTm n) :
    Syn.subst σ (observation f p x E) = observation f (Syn.subst σ p) (Syn.subst σ x) (Syn.subst σ E) := by
  simp [observation,clock,numerator,denominator]

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (x E : PTm n) :
    Syn.subst σ (data x E) = data (Syn.subst σ x) (Syn.subst σ E) := by simp [data]

theorem name_at (f : PR 2) (p x E : PTm n) :
    Γ ⊢[PRAAx] ap2 (nameF f) p (data x E) ≐ observation f p x E := by
  have raw : Γ ⊢[PRAAx] ap2 (nameF f) p (data x E) ≐ observation f p (fstT (data x E)) (sndT (data x E)) := by
    simpa [nameF,ap2] using toPR_eq (Γ := Γ)
      (observation f (var 0) (fstT (var 1)) (sndT (var 1)) : PTm 2) ![p,data x E]
  have fields := Prf.eqCongr (Ax := PRAAx) (Γ := Γ) (observation f (var 0) (var 1) (var 2) : PTm 3)
    (σ := ![p,fstT (data x E),sndT (data x E)]) (σ' := ![p,x,E]) (fun i => by
      fin_cases i
      exact .eqRefl _
      exact fst_pair _ _
      exact snd_pair _ _)
  exact raw.eqTrans (by simpa using fields)

theorem observation_canonical (f : PR 2) (p x E T : PTm n) (hs : Γ ⊢[PRAAx] source f x E T) :
    Γ ⊢[PRAAx] canonical (observation f p x E) :=
  GaussianRationalHorner.ofGaussian_canonical _ _ (decoded_domain f (clock p E) x E T hs).andE₁.andE₁

theorem observation_bound (f : PR 2) (p x E T : PTm n) (hs : Γ ⊢[PRAAx] source f x E T) :
    Γ ⊢[PRAAx] bounded (observation f p x E) E one := by
  let a := numerator f (clock p E) x
  let b := denominator f (clock p E) x
  have h := decoded_domain f (clock p E) x E T hs
  have radius := GaussianDominantPairAlgebra.radius_bounded b a h.andE₁.andE₁
  have original := GaussianRationalReciprocal.bound_congr
    (GaussianEulerDecayFactorBounds.fraction_is_radius_point b a h.andE₁.andE₁).eqSymm (.eqRefl _) (.eqRefl _) radius
  exact GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ h.andE₁.andE₁ (le_refl one)
    (le_congr (by ipra_ring) (.eqRefl _) h.andE₂.andE₁) original

theorem swapped_domain (f : PR 2) (p x E T : PTm n) (hs : Γ ⊢[PRAAx] source f x E T) :
    Γ ⊢[PRAAx] GaussianCompactLogarithmBounds.domain (denominator f (clock p E) x)
      (numerator f (clock p E) x) T E := by
  have h := decoded_domain f (clock p E) x E T hs
  exact .andI (.andI h.andE₁.andE₂ h.andE₁.andE₁) (.andI h.andE₂.andE₂ h.andE₂.andE₁)

theorem observation_inverse (f : PR 2) (p x E T : PTm n) (hs : Γ ⊢[PRAAx] source f x E T) :
    Γ ⊢[PRAAx] qmul (observation f p x E) (ap2 f (clock p E) x) ≐ qone := by
  have h := decoded_domain f (clock p E) x E T hs
  exact (GaussianRationalSyntheticDivision.qmul_congr (.eqRefl _) (decoded_value f (clock p E) x E T hs).eqSymm).eqTrans
    (GaussianEulerCompactExhaustionNormalization.exact_inverse_product _ _ h.andE₁.andE₁ h.andE₁.andE₂)

theorem observation_rate (f : PR 2) (p q x E T : PTm n) (hs : Γ ⊢[PRAAx] source f x E T) :
    Γ ⊢[PRAAx] distanceBounded (observation f p x E) (observation f q x E)
      (unit p+unit q) (unit p*unit q) := by
  let s := clock p E
  let t := clock q E
  let i := observation f p x E
  let j := observation f q x E
  let a := ap2 f s x
  let b := ap2 f t x
  let U := unit s
  let V := unit t
  let P := unit p
  let Q' := unit q
  have d : Γ ⊢[PRAAx] le one (U*V) := positive_product _ _ (unit_positive _) (unit_positive _)
  have left := observation_inverse f p x E T hs
  have right := observation_inverse f q x E T hs
  have comp := central_distance a b i j E one (U+V) (U*V) (le_refl one) d
    (observation_bound f p x E T hs) (observation_bound f q x E T hs) (point_at f x s t hs.andE₁)
  have l : Γ ⊢[PRAAx] qmul i (qmul b j) ≐ i :=
    (GaussianRationalSyntheticDivision.qmul_congr (.eqRefl _) ((GaussianRationalPowerAlgebra.qmul_commutative b j).eqTrans right)).eqTrans
      (GaussianReciprocalHorner.qmul_one_right i (observation_canonical f p x E T hs))
  have r : Γ ⊢[PRAAx] qmul j (qmul a i) ≐ j :=
    (GaussianRationalSyntheticDivision.qmul_congr (.eqRefl _) ((GaussianRationalPowerAlgebra.qmul_commutative a i).eqTrans left)).eqTrans
      (GaussianReciprocalHorner.qmul_one_right j (observation_canonical f q x E T hs))
  have payP : Γ ⊢[PRAAx] le ((E*E)*P) U := query_budget (E*E) p
  have payQ : Γ ⊢[PRAAx] le ((E*E)*Q') V := query_budget (E*E) q
  have budget : Γ ⊢[PRAAx] le ((E*E*(U+V))*(P*Q')) ((P+Q')*(U*V)) := by
    ipra_le 𝔞(V*Q')*sl payP+𝔞(U*P)*sl payQ
  exact distance_radius_mono i j _ _ _ _ d (positive_product _ _ (unit_positive _) (unit_positive _)) budget
    (distance_congr l r (.eqRefl _) (by ipra_ring) comp)

theorem name_regular (f : PR 2) (x E T : PTm n) (hs : Γ ⊢[PRAAx] source f x E T) :
    Γ ⊢[PRAAx] pointCN (nameF f) (data x E) := by
  let sh (a : PTm n) := Syn.shift (Syn.shift a)
  have moved : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] source f (sh x) (sh E) (sh T) := by
    simpa only [Fm.shift,Syn.shift,GaussianNamedPositiveLogarithm.subst_source,sh] using hs.shift.shift
  refine .allI (.allI ?_)
  have comparison := observation_rate f (var 1) (var 0) (sh x) (sh E) (sh T) moved
  simpa only [pointCN,GaussianEuclideanPointDistance.unit,GaussianCoefficientNameBounds.unit,Syn.shift,subst_data,sh] using
    distance_congr (name_at f (var 1) (sh x) (sh E)).eqSymm (name_at f (var 0) (sh x) (sh E)).eqSymm
      (.eqRefl _) (.eqRefl _) comparison

private theorem scalar_represents (a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] RationalArithmetic.represents (fstT (fraction a b)) (ZT.ofNat a) b := by
  apply GaussianRationalHorner.scalar_congr (.eqRefl _) ?_ (.eqRefl _)
    (GaussianRationalHorner.ofGaussian_represents (ComplexLogarithmRemainder.scale a ComplexLogarithmRemainder.oneCode) b hb).andE₁
  apply ZT.derive
  simp only [GaussianRootAlgebra.re_scale,GaussianRootAlgebra.re_one,ZT.toZ_ofNat]
  ring

theorem observation_positive_source (f : PR 2) (p x E T : PTm n)
    (hT : Γ ⊢[PRAAx] le one T) (hs : Γ ⊢[PRAAx] source f x E T) :
    Γ ⊢[PRAAx] GaussianPositiveCompactInputDecoding.source (observation f p x E) T E := by
  let a := denominator f (clock p E) x
  let b := numerator f (clock p E) x
  let v := observation f p x E
  have swapped := swapped_domain f p x E T hs
  have order : Γ ⊢[PRAAx] RationalArgmin.rationalLE (GaussianEuclideanDistanceName.fraction one T) (fstT v) :=
    GaussianRationalMetric.comparison_of_cleared _ _ one a T b hT swapped.andE₁.andE₂
      (GaussianEuclideanDistanceName.fraction_represents one T hT) (scalar_represents a b swapped.andE₁.andE₂)
      (le_congr (by ipra_ring : Γ ⊢[PRAAx] b ≐ b*one) (mul_comm T a) swapped.andE₂.andE₁)
  have lower : Γ ⊢[PRAAx] RationalValueBounds.upper (GaussianEuclideanDistanceName.fraction one T) (fstT v) zero one :=
    RationalValueBounds.upper_of_order _ _ zero one order
  exact .andI (GaussianEulerPositivePowerChartOrder.fraction_positive a b swapped.andE₁.andE₂).andE₁
    (.andI hT (.andI lower (observation_bound f p x E T hs)))

theorem name_positive_source (f : PR 2) (x E T : PTm n)
    (hT : Γ ⊢[PRAAx] le one T) (hs : Γ ⊢[PRAAx] source f x E T) :
    Γ ⊢[PRAAx] source (nameF f) (data x E) T E := by
  refine .andI (name_regular f x E T hs) (.andI hT (.allI ?_))
  have moved : Γ.map Fm.shift ⊢[PRAAx] source f (Syn.shift x) (Syn.shift E) (Syn.shift T) := by
    simpa only [Fm.shift,Syn.shift,GaussianNamedPositiveLogarithm.subst_source] using hs.shift
  have shiftedT : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift T) := by
    simpa [Fm.shift,Syn.shift,one] using hT.shift
  let p : PTm (n+1) := var 0
  let value := ap2 (nameF f) p (data (Syn.shift x) (Syn.shift E))
  let raw := observation f p (Syn.shift x) (Syn.shift E)
  have code : Γ.map Fm.shift ⊢[PRAAx] value ≐ raw := name_at f p (Syn.shift x) (Syn.shift E)
  have body : Γ.map Fm.shift ⊢[PRAAx] canonical raw ⋏
      GaussianPositiveCompactInputDecoding.source raw (Syn.shift T) (Syn.shift E) :=
    .andI (observation_canonical f p (Syn.shift x) (Syn.shift E) (Syn.shift T) moved)
      (observation_positive_source f p (Syn.shift x) (Syn.shift E) (Syn.shift T) shiftedT moved)
  have transported := Prf.eqSubst
    (canonical (var 0) ⋏ GaussianPositiveCompactInputDecoding.source (var 0) (var 1) (var 2) : Fm PTm 3)
    (σ := ![raw,Syn.shift T,Syn.shift E]) (σ' := ![value,Syn.shift T,Syn.shift E])
    (fun i => by fin_cases i; exact code.eqSymm; exact .eqRefl _; exact .eqRefl _) (by simpa using body)
  simpa [GaussianNamedPositiveLogarithm.admissible,Syn.shift,p,value] using transported

theorem actual_positive_named_reciprocal_regular_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (source f (var 0) (var 1) (var 2) ⟶ pointCN (nameF f) (data (var 0) (var 1))) :=
  closeUniv 3 (.impI (name_regular f _ _ _ Prf.hyp0))

theorem actual_positive_named_reciprocal_inverts_selected_observation_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (source f (var 1) (var 2) (var 3) ⟶
        qmul (ap2 (nameF f) (var 0) (data (var 1) (var 2))) (ap2 f (clock (var 0) (var 2)) (var 1)) ≐ qone) :=
  closeUniv 4 (.impI ((GaussianRationalSyntheticDivision.qmul_congr (name_at f _ _ _) (.eqRefl _)).eqTrans
    (observation_inverse f _ _ _ _ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianNamedPositiveReciprocal
