import IPRADerivations.Analysis.Trigonometry.Arctangent.Extension.GaussianArctangentNamedExtension
import IPRADerivations.Analysis.Trigonometry.Arctangent.PartialSums.GaussianArctangentPartialExponential

/-!
# The actual Cayley formula on names

At the original exponential query, the extension returns the partial
arctangent of its literal clipped fraction. A finite exponential
comparison identifies the exponential with the Cayley value of that
fraction. The resulting Cayley program is regular after a fixed
normalization, whose samples still compute the original formula exactly.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianArctangentNamedCayley

open_ipra
open GaussianArctangentCayleyValues (value)
open GaussianArctangentNamedExtension (clock numerator denominator denominator_positive numerator_le)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constant_at)
open GaussianNameEquivalence (crossEquivalent cross_to_diagonal diagonal_at point_at)
open GaussianNamedDiagonalRate (diagonalRate cross_of_diagonal_rate)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (canonical ofGaussian_canonical positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalPolynomialExponential (scalarSum)
open GaussianRationalReciprocal (bound_congr)
open GaussianRadiusExponentialName (input inputPrecision index)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

def exponentialF (f : PR 2) : PR 2 :=
  GaussianRadiusExponentialName.nameF (GaussianArctangentNamedExtension.nameF f)
def exponentialData (x : PTm n) : PTm n := GaussianRadiusExponentialName.data two x
def queryPrecision (p : PTm n) : PTm n := inputPrecision two p
def raw (f : PR 2) (p x : PTm n) : PTm n :=
  value (denominator f (queryPrecision p) x) (numerator f (queryPrecision p) x)
def rawF (f : PR 2) : PR 2 := PTm.toPR (raw f (var 0) (var 1) : PTm 2)
def modulus : PTm n := num 4
def nameF (f : PR 2) : PR 2 := GaussianFastValueCut.nameF (rawF f)
def data (x : PTm n) : PTm n := GaussianFastValueCut.nameData modulus x

ipra_subst exponentialData
ipra_subst queryPrecision
ipra_subst raw [value, GaussianArctangentCayleyValues.numerator, GaussianArctangentCayleyValues.denominator]
ipra_subst data [modulus]

theorem argument_bound (f : PR 2) (p x : PTm n) :
    Γ ⊢[PRAAx] bounded (ap2 (GaussianArctangentNamedExtension.nameF f) p x) two one :=
  bound_congr (GaussianArctangentNamedExtension.sample_at f p x).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianArctangentPartialExponential.argument_bound (clock p) _ _
      (denominator_positive f p x) (numerator_le f p x))

theorem exp_input (f : PR 2) (x : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) :
    Γ ⊢[PRAAx] input (GaussianArctangentNamedExtension.nameF f) two x := by
  refine .andI (GaussianArctangentNamedExtension.name_regular f x hf) (.allI ?_)
  simpa only [GaussianRadiusExponentialName.boundedSamples,Syn.shift,PTm.subst_succ,PTm.subst_zero] using
    argument_bound f (var 0) (Syn.shift x)

theorem exp_regular (f : PR 2) (x : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) :
    Γ ⊢[PRAAx] pointCN (exponentialF f) (exponentialData x) :=
  GaussianRadiusExponentialName.name_regular _ _ _ (exp_input f x hf)

theorem raw_at (f : PR 2) (p x : PTm n) : Γ ⊢[PRAAx] ap2 (rawF f) p x ≐ raw f p x := by
  simpa [rawF,ap2] using toPR_eq (Γ := Γ) (raw f (var 0) (var 1) : PTm 2) ![p,x]

theorem raw_canonical (f : PR 2) (p x : PTm n) : Γ ⊢[PRAAx] canonical (raw f p x) :=
  ofGaussian_canonical _ _ (GaussianArctangentCayleyValues.denominator_positive _ _
    (denominator_positive f (queryPrecision p) x))

theorem raw_bound (f : PR 2) (p x : PTm n) : Γ ⊢[PRAAx] bounded (raw f p x) one one :=
  GaussianArctangentCayleyValues.unit_bound _ _ (denominator_positive f (queryPrecision p) x)

theorem raw_distance (f : PR 2) (p x : PTm n) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (exponentialF f) p (exponentialData x)) (raw f p x) (num 3) (unit p) := by
  let j := queryPrecision p
  let A := numerator f j x
  let B := denominator f j x
  let t := clock j
  let K := index two p
  let F := GaussianArctangentPartialQuadrature.nameF
  let u := GaussianArctangentPartialQuadrature.data A B
  let E := GaussianArctangentPartialExponential.exponentialF
  let y := GaussianArctangentPartialExponential.exponentialData A B
  have hb := denominator_positive (Γ := Γ) f j x
  have ha := numerator_le (Γ := Γ) f j x
  have h := GaussianArctangentPartialExponential.exponential_input A B hb ha
  have hr := GaussianExponentialReference.finite_reference F two u p t K h (le_add_right _ _) (le_refl _)
  have read : Γ ⊢[PRAAx] ap2 (exponentialF f) p (exponentialData x) ≐ scalarSum (ap2 F t u) K :=
    (GaussianRadiusExponentialName.sample_at (GaussianArctangentNamedExtension.nameF f) two p x).eqTrans
      (GaussianNameConjugation.scalar_sum_congr K (GaussianArctangentNamedExtension.sample_at f j x))
  have first := distance_congr read.eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) hr
  have cross := GaussianArctangentPartialExponential.exponential_cross A B hb ha
  have last := distance_congr (.eqRefl _) (constant_at p (raw f p x)) (.eqRefl _) (.eqRefl _)
    (diagonal_at E _ y (raw f p x) p (cross_to_diagonal _ _ _ _ cross))
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ (unit_positive p) first last)

private theorem raw_regularity_at (f : PR 2) (p q x : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (rawF f) p x) (ap2 (rawF f) q x)
      (modulus*(unit p+unit q)) (unit p*unit q) := by
  let P := unit p
  let Q := unit q
  have hp := unit_positive (Γ := Γ) p
  have hq := unit_positive (Γ := Γ) q
  have hPQ := positive_product P Q hp hq
  have first := distance_radius_mono _ _ (num 3) P (num 3*Q) (P*Q) hp hPQ
    (le_of_eq_add (d := zero) (by ipra_ring))
    (distance_symmetric _ _ _ _ hp (raw_distance f p x))
  have middle := point_at _ _ p q (exp_regular f x hf)
  have last := distance_radius_mono _ _ (num 3) Q (num 3*P) (P*Q) hq hPQ
    (le_of_eq_add (d := zero) (by ipra_ring)) (raw_distance f q x)
  exact distance_congr (raw_at f p x).eqSymm (raw_at f q x).eqSymm
    (by dsimp only [P,Q]; unfold modulus; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hPQ (distance_triangle_same _ _ _ _ _ _ hPQ first middle) last)

theorem raw_regularity (f : PR 2) (x : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) :
    Γ ⊢[PRAAx] GaussianFastValueCut.regular (rawF f) modulus x := by
  let u := Syn.shift (Syn.shift x)
  let p : PTm (n+2) := var 1
  let q : PTm (n+2) := var 0
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] pointCN f u := by
    simpa only [Fm.shift,GaussianEuclideanDistanceName.subst_pointCN,Syn.shift,u] using hf.shift.shift
  refine .allI (.allI ?_)
  simpa only [GaussianFastValueCut.regular,modulus,PTm.subst_num,Syn.shift,u,p,q] using
    raw_regularity_at f p q u hs

theorem name_regular (f : PR 2) (x : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) :
    Γ ⊢[PRAAx] pointCN (nameF f) (data x) :=
  GaussianFastValueCut.name_fast _ _ _ (raw_regularity f x hf)

theorem sample_at (f : PR 2) (p x : PTm n) :
    Γ ⊢[PRAAx] ap2 (nameF f) p (data x) ≐ raw f (GaussianFastValueCut.exponent modulus p) x := by
  let t := GaussianFastValueCut.exponent modulus p
  have lift : Γ ⊢[PRAAx] GaussianFastValueCut.recode (ap2 (rawF f) t x) ≐ GaussianFastValueCut.recode (raw f t x) := by
    simpa only [GaussianFastValueCut.subst_recode,Syn.subst_var,Matrix.cons_val_zero] using
      (Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (GaussianFastValueCut.recode (var 0) : PTm 1)
        (σ := ![ap2 (rawF f) t x]) (σ' := ![raw f t x])
        (fun i => by fin_cases i; exact raw_at f t x))
  exact (GaussianFastValueCut.name_at (rawF f) modulus x p).eqTrans
    (lift.eqTrans (GaussianExponentialReference.recode_fixed _ (raw_canonical f t x)))

theorem sample_bound (f : PR 2) (p x : PTm n) :
    Γ ⊢[PRAAx] bounded (ap2 (nameF f) p (data x)) one one :=
  bound_congr (sample_at f p x).eqSymm (.eqRefl _) (.eqRefl _) (raw_bound f _ x)

private theorem normalized_distance (f : PR 2) (p x : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (exponentialF f) p (exponentialData x)) (ap2 (nameF f) p (data x))
      (two+num 3) (unit p) := by
  let t := GaussianFastValueCut.exponent (modulus : PTm n) p
  let P := unit p
  let T := unit t
  have ht : Γ ⊢[PRAAx] le p t := le_add_right _ _
  have grow := GaussianExponentialReference.unit_monotone ht
  have reg := point_at _ _ p t (exp_regular f x hf)
  have first := distance_radius_mono _ _ _ _ two P (positive_product _ _ (unit_positive p) (unit_positive t))
    (unit_positive p) (by change Γ ⊢[PRAAx] le ((P+T)*P) (two*(P*T)); ipra_le 𝔟 P*sl grow) reg
  have last := GaussianExponentialReference.dyadic_weaken _ _ _ p t ht (raw_distance f t x)
  exact distance_congr (.eqRefl _) (sample_at f p x).eqSymm (.eqRefl _) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ (unit_positive p) first last)

theorem exponential_cross (f : PR 2) (x : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) :
    Γ ⊢[PRAAx] crossEquivalent (exponentialF f) (nameF f) (exponentialData x) (data x) := by
  apply cross_of_diagonal_rate _ _ _ _ (two+num 3) (exp_regular f x hf) (name_regular f x hf)
  let u := Syn.shift x
  have hs : Γ.map Fm.shift ⊢[PRAAx] pointCN f u := by
    simpa only [Fm.shift,GaussianEuclideanDistanceName.subst_pointCN,Syn.shift,u] using hf.shift
  refine .allI ?_
  simpa only [diagonalRate,subst_exponentialData,subst_data,PTm.subst_add,PTm.subst_succ,PTm.subst_zero,
    PTm.subst_num,Syn.shift,u] using normalized_distance f (var 0) u hs

theorem actual_named_arctangent_Cayley_literal_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (ap2 (nameF f) (var 0) (data (var 1)) ≐ raw f (GaussianFastValueCut.exponent modulus (var 0)) (var 1)) :=
  closeUniv 2 (sample_at f _ _)

theorem actual_named_arctangent_Cayley_distance_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (distanceBounded (ap2 (exponentialF f) (var 0) (exponentialData (var 1))) (raw f (var 0) (var 1))
      (num 3) (unit (var 0))) :=
  closeUniv 2 (raw_distance f _ _)

theorem actual_named_arctangent_Cayley_exponential_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (pointCN f (var 0) ⟶ crossEquivalent (exponentialF f) (nameF f) (exponentialData (var 0)) (data (var 0))) :=
  closeUniv 1 (.impI (exponential_cross f _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianArctangentNamedCayley
