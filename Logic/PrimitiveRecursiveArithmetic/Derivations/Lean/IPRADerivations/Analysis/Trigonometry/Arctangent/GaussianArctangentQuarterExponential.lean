import IPRADerivations.Analysis.Trigonometry.Arctangent.PartialSums.GaussianArctangentExponentialPrefix
import IPRADerivations.Analysis.Exponential.Names.GaussianExponentialReference
import IPRADerivations.Analysis.Gamma.EulerProducts.CanonicalProducts.GaussianGammaCanonicalExponent
import IPRADerivations.Analysis.Gamma.HalfInteger.GaussianGammaHalfPiName
import IPRADerivations.Analysis.Names.Rates.GaussianNamedDiagonalRate
import IPRADerivations.Analysis.Exponential.Estimates.GaussianRationalUniformExponentialLipschitz

/-!
# The exponential at the named arctangent quarter turn

The named input uses the native π observation at each precision. Uniform
finite exponential stability compares that input with the exponential's
scheduled query, while its factorial tail covers the Cayley rectangle cutoff.
-/

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianArctangentQuarterExponential

open_ipra
open ComplexLogarithmRemainder (normSq normSq_eval eval_re_code eval_im_code)
open GaussianArctangentCayleyValues (imaginaryCode imaginaryPoint)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNameEquivalence (crossEquivalent point_at)
open GaussianNamedDiagonalRate (diagonalRate)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (ofGaussian ofGaussian_represents qmul positive_product)
open GaussianRationalMetric (bounded bounded_of_cleared distanceBounded)
open GaussianRationalPolynomialExponential (scalarSum)
open GaussianRationalReciprocal (bound_congr)
open GaussianScalarExponentialProductTail (rectangleCutoff)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

def radius : PTm n := two
def halfImaginary : PTm n := ofGaussian imaginaryCode two
def argument (p z : PTm n) : PTm n :=
  qmul halfImaginary (ap2 GaussianGammaHalfPiName.nameF p z)
def stage (p : PTm n) : PTm n := p+two*GaussianGammaHalfPiName.meshAt p
def finiteValue (p z : PTm n) : PTm n := scalarSum (argument p z) (rectangleCutoff radius (stage p))
def finiteEstimate (z C : PTm n) : Fm PTm n := .all
  (distanceBounded (finiteValue (var 0) (Syn.shift z)) imaginaryPoint (Syn.shift C) (unit (var 0)))
def boundedArguments (z : PTm n) : Fm PTm n := .all
  (bounded (argument (var 0) (Syn.shift z)) radius one)

def quarterF : PR 2 := PTm.toPR (argument (var 0) (var 1) : PTm 2)
def exponentialF : PR 2 := GaussianRadiusExponentialName.nameF quarterF
def exponentialData (z : PTm n) : PTm n := GaussianRadiusExponentialName.data radius z

ipra_subst argument [halfImaginary, imaginaryCode]
ipra_subst stage [GaussianGammaHalfPiName.meshAt, GaussianGammaHalfPiName.meshIndex, GaussianGammaHalfPiName.orderAt, GaussianGammaHalfPiName.orderIndex]
ipra_subst finiteValue [radius, rectangleCutoff, GaussianScalarExponentialProductTail.reserve, GaussianScalarExponentialProductTail.growthExponent]
ipra_subst finiteEstimate [imaginaryPoint, imaginaryCode, Syn.subst_shift, Syn.shift_subst]
ipra_subst boundedArguments [radius, Syn.subst_shift, Syn.shift_subst]

theorem sample_at (p z : PTm n) : Γ ⊢[PRAAx] ap2 quarterF p z ≐ argument p z := by
  simpa [quarterF,ap2] using toPR_eq (Γ := Γ) (argument (var 0) (var 1) : PTm 2) ![p,z]

theorem half_imaginary_bound : Γ ⊢[PRAAx] bounded (halfImaginary : PTm n) one one := by
  have hd : Γ ⊢[PRAAx] le one two := le_succ_self one
  have hn : Γ ⊢[PRAAx] normSq (imaginaryCode : PTm n) ≐ one := by
    apply deriveNat
    rw [normSq_eval]
    simp only [imaginaryCode,eval_re_code,eval_im_code,ZT.toZ_ofNat]
    ipra_simps
    ring
  apply bounded_of_cleared _ _ two one one hd (le_refl _) (ofGaussian_represents _ _ hd)
  have budget : Γ ⊢[PRAAx] le (normSq (imaginaryCode : PTm n)) (two*two) :=
    le_congr hn.eqSymm (.eqRefl _) (le_of_eq_add (d := num 3) (by ipra_ring))
  exact le_congr (by ipra_ring) (by ipra_ring) budget

theorem argument_distance (p q z : PTm n) :
    Γ ⊢[PRAAx] distanceBounded (argument p z) (argument q z) (unit p+unit q) (unit p*unit q) := by
  have raw := GaussianApproximateInverseDistance.multiply_distance (Γ := Γ) halfImaginary _ _ one _ _
    (positive_product _ _ (unit_positive p) (unit_positive q)) half_imaginary_bound
    (point_at GaussianGammaHalfPiName.nameF z p q (GaussianGammaHalfPiName.name_regular z))
  exact distance_congr (.eqRefl _) (.eqRefl _) (one_mul _) (.eqRefl _) raw

theorem quarter_regular (z : PTm n) : Γ ⊢[PRAAx] pointCN quarterF z :=
  .allI (.allI (distance_congr (sample_at _ _).eqSymm (sample_at _ _).eqSymm
    (.eqRefl _) (.eqRefl _) (argument_distance _ _ _)))

theorem bounded_argument_at (p z : PTm n) (h : Γ ⊢[PRAAx] boundedArguments z) :
    Γ ⊢[PRAAx] bounded (argument p z) radius one := by
  simpa only [boundedArguments,GaussianRationalMetric.subst_bounded,subst_argument,
    Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift,radius,PTm.subst_zero,PTm.subst_succ] using h.allE p

theorem quarter_input (z : PTm n) (h : Γ ⊢[PRAAx] boundedArguments z) :
    Γ ⊢[PRAAx] GaussianRadiusExponentialName.input quarterF radius z := by
  refine .andI (quarter_regular z) (.allI ?_)
  have hs : Γ.map Fm.shift ⊢[PRAAx] boundedArguments (Syn.shift z) := by
    simpa only [Fm.shift,subst_boundedArguments,Syn.shift] using h.shift
  have hp : Γ.map Fm.shift ⊢[PRAAx] bounded (ap2 quarterF (var 0) (Syn.shift z)) radius one :=
    bound_congr (sample_at _ _).eqSymm (.eqRefl _) (.eqRefl _)
      (bounded_argument_at (var 0) (Syn.shift z) hs)
  simpa only [GaussianRadiusExponentialName.boundedSamples,radius,Syn.shift,PTm.subst_zero,PTm.subst_succ] using hp

theorem original_argument_bound (p z : PTm n) : Γ ⊢[PRAAx] bounded (argument p z) radius one := by
  let M := GaussianGammaHalfPiName.meshAt p
  let L := GaussianGammaHalfPiName.clearing p
  exact bound_congr (GaussianArctangentExponentialPrefix.at_pi_observation p z) (.eqRefl _) (.eqRefl _)
    (GaussianArctangentExponentialPrefix.prefix_bound M M L
      (GaussianArctangentExponentialPrefix.original_mesh_source p) (le_refl _))

theorem original_bounded_arguments (z : PTm n) : Γ ⊢[PRAAx] boundedArguments z :=
  .allI (original_argument_bound (var 0) (Syn.shift z))

theorem finite_estimate_at (z C p : PTm n) (h : Γ ⊢[PRAAx] finiteEstimate z C) :
    Γ ⊢[PRAAx] distanceBounded (finiteValue p z) imaginaryPoint C (unit p) := by
  simpa [finiteEstimate,imaginaryPoint,imaginaryCode] using h.allE p

/-- The finite endpoint at the literal π observation and the actual named
exponential observation admit a common dyadic error bound. -/
theorem scheduled_comparison (p z : PTm n) (h : Γ ⊢[PRAAx] boundedArguments z) :
    Γ ⊢[PRAAx] distanceBounded (ap2 exponentialF p (exponentialData z)) (finiteValue p z)
      (pw (num 3) radius*two+one) (unit p) := by
  let j := GaussianRadiusExponentialName.inputPrecision radius p
  let K := GaussianRadiusExponentialName.index radius p
  let q := GaussianRadiusExponentialName.query quarterF radius p z
  let a := argument p z
  let T := rectangleCutoff radius (stage p)
  have hr := quarter_input z h
  have ha : Γ ⊢[PRAAx] bounded a radius one := bounded_argument_at p z h
  have hj : Γ ⊢[PRAAx] le p j := by
    unfold j GaussianRadiusExponentialName.inputPrecision
    exact le_trans (le_add_right _ _) (le_add_right _ _)
  have raw := distance_congr (Γ := Γ) (sample_at j z).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (argument_distance j p z)
  have hd : Γ ⊢[PRAAx] distanceBounded q a two (unit p) :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (unit_positive j) (unit_positive p))
      (unit_positive p) (by
        have order := GaussianExponentialReference.unit_monotone hj
        ipra_le 𝔟 (unit p)*sl order) raw
  have hlip := GaussianRationalUniformExponentialLipschitz.scalar_sum_lipschitz q a radius two
    (unit p) K (unit_positive p) (GaussianRadiusExponentialName.query_bound _ _ _ _ hr) ha hd
  have hK : Γ ⊢[PRAAx] le K T :=
    GaussianExponentialReference.index_below_rectangle radius radius p (stage p)
      (le_add_right _ _) (le_add_right _ _)
  have htail := GaussianExponentialReference.later_cutoff a radius p T ha hK
  have htail' := GaussianExponentialReference.dyadic_weaken _ _ _ p (ConciseIPRA.PTm.succ p)
    (le_succ_self p) htail
  have combined := distance_triangle_same _ _ _ _ _ _ (unit_positive p) hlip
    (distance_symmetric _ _ _ _ (unit_positive p) htail')
  exact distance_congr (GaussianRadiusExponentialName.sample_at quarterF radius p z).eqSymm
    (.eqRefl _) (.eqRefl _) (.eqRefl _) combined

theorem quarter_cross (z C : PTm n) (h : Γ ⊢[PRAAx] boundedArguments z)
    (hf : Γ ⊢[PRAAx] finiteEstimate z C) :
    Γ ⊢[PRAAx] crossEquivalent exponentialF constantF (exponentialData z) imaginaryPoint := by
  apply GaussianNamedDiagonalRate.cross_of_diagonal_rate _ _ _ _ (pw (num 3) radius*two+one+C)
    (GaussianRadiusExponentialName.name_regular _ _ _ (quarter_input z h)) (constant_regular _)
  refine .allI ?_
  let x := Syn.shift z
  let E := Syn.shift C
  let p : PTm (n+1) := var 0
  have hb : Γ.map Fm.shift ⊢[PRAAx] boundedArguments x := by
    simpa [Fm.shift,x,Syn.shift] using h.shift
  have he : Γ.map Fm.shift ⊢[PRAAx] finiteEstimate x E := by
    simpa [Fm.shift,x,E,Syn.shift] using hf.shift
  have comparison := distance_triangle_same _ _ _ _ _ _ (unit_positive p)
    (scheduled_comparison p x hb) (finite_estimate_at x E p he)
  simpa only [diagonalRate,exponentialF,exponentialData,radius,imaginaryPoint,imaginaryCode,x,E,p,Syn.shift,
    GaussianRadiusExponentialName.subst_data,PTm.subst_num,PTm.subst_add,PTm.subst_mul,pw,subst_ap2,
    PTm.subst_succ,PTm.subst_zero,ComplexLogarithmRemainder.subst_code,GaussianRationalHorner.subst_ofGaussian,
    ZT.subst_ofNat] using
    distance_congr (.eqRefl _) (constant_at p imaginaryPoint).eqSymm (.eqRefl _) (.eqRefl _) comparison

theorem original_quarter_cross (z C : PTm n) (hf : Γ ⊢[PRAAx] finiteEstimate z C) :
    Γ ⊢[PRAAx] crossEquivalent exponentialF constantF (exponentialData z) imaginaryPoint :=
  quarter_cross z C (original_bounded_arguments z) hf

end LeanProofs.IPRA.Analysis.GaussianArctangentQuarterExponential
