import IPRADerivations.Analysis.GaussianStirlingAllOrderImproperName
import IPRADerivations.Analysis.GaussianStirlingAllOrderOuterCovarianceStrict
import IPRADerivations.Analysis.GaussianStirlingMultiplicativeBoundsOrder

/-!
# A positive rational floor for the named Stirling upper gap

Choose the common mesh fine enough for both the certified improper
approximation and the finite strict covariance estimate. The finite
gap is then separated from zero by the same rational fraction at
every clock. The mass converges to the exact reciprocal primitive.
-/

set_option autoImplicit false
set_option maxHeartbeats 1050000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderNamedUpperGap

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num monus)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (fraction fraction_represents)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNamedPositiveExponentialOrder (realOrder scalar_coordinate_distance)
open GaussianNamedRealOrderEnvelope (envelope order_from_envelope)
open GaussianRationalDistanceOrder (distance_congr distance_triangle_same distance_symmetric)
open GaussianRationalHorner (positive_product)
open GaussianRationalL1 (nonnegative_of_representation)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianStirlingAllOrderDiscreteParts (sub)
open GaussianStirlingAllOrderOuterCovarianceRate (gap)
open GaussianStirlingAllOrderOuterCovarianceStrict (marginDenominator margin_den_positive positive_gap refinement)
open GaussianStirlingAllOrderPanelDerivative (signedMean)
open GaussianStirlingAllOrderPanelPartsBinding (requiredMesh prefixAt radius actual_prefix_distance meanPoint)
open GaussianStirlingAllOrderPanelPartsNames
  (constantCap difference_error fixed_product_distance nameF nameData name_regular weightedPrimitive)
open GaussianStirlingAllOrderPanelPartsOuterFold (massPrefix panelPrefix)
open GaussianStirlingAllOrderPanelPartsSolve (embed_sub)
open GaussianStirlingAllOrderPowerIntegralCofinal (cofinal_mass_distance)
open GaussianStirlingAllOrderPowerIntegralMeshCells (primitive)
open GaussianStirlingAllOrderReciprocalWeightError (power)
open GaussianStirlingGlobalBounds (steps)
open GaussianStirlingNames (source)
open RationalAlgebra (multiply_associative multiply_commutative multiply_congr)
open RationalArgmin (eq_le rationalLE rationalLE_congr transitive)
open RationalArithmetic (add_guard multiply multiply_monotone)
open RationalFiniteSum (canonical_equal)
open RationalGaussianEmbedding (embed embed_multiply)
open RationalNonnegativePowers (fraction_congr fraction_multiply)
open RationalNormalForm (normalize_well_formed)
open RationalSumConstants (multiply_one_right)
open RationalValueBounds (upper upper_congr upper_of_radius upper_order_left)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "gfraction" => GaussianPositiveRationalLogarithm.fraction
local notation "subF" => GaussianNamedDifference.nameF
local notation "subData" => GaussianNamedDifference.data

def floorDenominator (m : ℕ) (A B : PTm n) : PTm n := num 4*marginDenominator m (2*m+2) A B

def floorPoint (m : ℕ) (A B : PTm n) : PTm n := gfraction one (floorDenominator m A B)

def gapF (m : ℕ) : PR 2 := subF constantF (nameF m)

def gapData (m : ℕ) (A B x : PTm n) : PTm n := subData (weightedPrimitive m A B) (nameData m A B x)

def gapRadius (m : ℕ) (B : PTm n) : PTm n :=
  constantCap (meanPoint m)*(power (2*m+2) B+one)+radius m B+num 6

theorem floor_denominator_positive (m : ℕ) (A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) :
    Γ ⊢[PRAAx] le one (floorDenominator m A B) :=
  positive_product _ _ (by ipra_le 3) (margin_den_positive m (2*m+2) A B hA)

private def meshBase (m : ℕ) (A B p : PTm n) : PTm n :=
  requiredMesh m A B p+refinement m (2*m+2) A B+unit p

private def meshWidth (m : ℕ) (A B p : PTm n) : PTm n := meshBase m A B p*num 8

private theorem half_double (c : PTm n) (hc : Γ ⊢[PRAAx] RationalNormalForm.wellFormed c) :
    Γ ⊢[PRAAx] multiply (fraction one two) (multiply (fraction two one) c) ≐ c := by
  have ht : Γ ⊢[PRAAx] le one (two : PTm n) := by ipra_le 1
  have hd := positive_product _ _ ht (le_refl one)
  have e : Γ ⊢[PRAAx] fraction (one*two) (two*one) ≐ fraction one one := by
    apply canonical_equal _ _ _ _ _ _
      (normalize_well_formed _ _ hd) (normalize_well_formed _ _ (le_refl one))
      (fraction_represents _ _ hd) (fraction_represents _ _ (le_refl one)) hd (le_refl one)
    apply ZT.derive
    simp only [ZT.toZ_mul,ZT.toZ_ofNat,IPRA.Q.mk_mul,map_mul]
    ring
  have value := (fraction_multiply (Γ := Γ) one two two one ht (le_refl one)).eqTrans e
  exact (multiply_associative _ _ c).eqSymm.eqTrans ((multiply_congr value (.eqRefl c)).eqTrans
    ((multiply_commutative _ _).eqTrans (multiply_one_right c hc)))

private theorem finite_floor (m : ℕ) (A B S p : PTm n)
    (hs : Γ ⊢[PRAAx] source A B) (hS : Γ ⊢[PRAAx] le (refinement m (2*m+2) A B) S) :
    Γ ⊢[PRAAx] rationalLE (fraction one (floorDenominator m A B)) (gap m (2*m+2) A B S (steps p)) := by
  let e := 2*m+2
  let D := marginDenominator m e A B
  let L := GaussianStirlingIntegerLimit.index p
  let t := monus L one
  let half := fraction (one : PTm n) two
  have ht : Γ ⊢[PRAAx] L ≐ succ t :=
    (eq_add_of_le (GaussianStirlingIntegerLimit.index_positive (Γ := Γ) p)).eqTrans
      ((add_comm _ _).eqTrans (succ_eq_add_one _).eqSymm)
  have len : Γ ⊢[PRAAx] steps p ≐ succ (succ t) := congrSucc ht
  have mean {k : ℕ} (σ : Fin (n+1) → PTm k) :
      Syn.subst σ (signedMean (m+1) : PTm (n+1)) = (signedMean (m+1) : PTm k) := by
    simp [signedMean,GaussianStirlingAllOrderPanelDerivative.meanNumerator,BernoulliBounds.zint]
  have ve : Γ ⊢[PRAAx] gap m e A B S (succ (succ t)) ≐ gap m e A B S (steps p) := by
    simpa only [gap,sub,GaussianStirlingAllOrderPanelPartsOuterFold.subst_massPrefix,
      GaussianStirlingAllOrderPanelPartsOuterFold.subst_panelPrefix,RationalArithmetic.subst_multiply,
      RationalArithmetic.subst_add,RationalArithmetic.subst_negative,Syn.subst_var,
      Syn.inst_zero,Syn.subst_inst_shift,PTm.subst_mul,PTm.subst_num,mean] using
      Prf.eqCongr (Γ := Γ) (gap m e (Syn.shift A) (Syn.shift B) (Syn.shift S) (var 0))
        (σ := Syn.inst (succ (succ t))) (σ' := Syn.inst (steps p))
        (fun i => Fin.cases len.eqSymm (fun j => .eqRefl (var j)) i)
  have hD := margin_den_positive m e A B hs.andE₁
  have h2 : Γ ⊢[PRAAx] le one (two : PTm n) := by ipra_le 1
  have hs2 := positive_product _ _ h2 hD
  have pos := nonnegative_of_representation half one two h2 (fraction_represents _ _ h2)
  have f := positive_gap m e (by unfold e; omega) A B S t hs.andE₁ hs.andE₂ hS
  have scaled := multiply_monotone half _ _ pos f
  have i : Γ ⊢[PRAAx] multiply half (fraction one (two*D)) ≐ fraction one (floorDenominator m A B) :=
    (fraction_multiply one two one (two*D) h2 hs2).eqTrans
      (fraction_congr (one_mul one) (by unfold D e floorDenominator; ipra_ring))
  have v := half_double (Γ := Γ) (gap m e A B S (succ (succ t))) (add_guard _ _)
  exact rationalLE_congr i (v.eqTrans ve) scaled

private theorem raw_floor (m : ℕ) (p A B : PTm n) (hs : Γ ⊢[PRAAx] source A B) :
    Γ ⊢[PRAAx] rationalLE (fstT (floorPoint m A B))
      (fstT (embed (gap m (2*m+2) A B (B*meshBase m A B p) (steps p)))) := by
  let e := 2*m+2
  let base := meshBase m A B p
  let S := B*base
  let v := gap m e A B S (steps p)
  have hb : Γ ⊢[PRAAx] le (refinement m e A B) S := by
    dsimp [S,base,meshBase,e]
    ipra_le
      𝔞 B*(𝔞 (requiredMesh m A B p)+𝔞 (unit p)) + sl hs.andE₂*𝔞 (refinement m (2*m+2) A B)
  have lo := finite_floor m A B S p hs hb
  have first := GaussianStirlingMultiplicativeBoundsOrder.fraction_real_part one _ (floor_denominator_positive m A B hs.andE₁)
  have last : Γ ⊢[PRAAx] fstT (embed v) ≐ RationalArithmetic.recode v := fst_pair _ _
  exact rationalLE_congr first.eqSymm last.eqSymm
    (transitive lo (eq_le (RationalArithmetic.recode_equal v).eqSymm))

private theorem aligned_gap (m : ℕ) (A B p : PTm n) :
    Γ ⊢[PRAAx] embed (gap m (2*m+2) A B (B*meshBase m A B p) (steps p)) ≐
      qsub (GaussianRationalHorner.qmul (meanPoint m)
        (embed (massPrefix (2*m+2) A B (B*meshWidth m A B p) (steps p))))
        (prefixAt m A B (meshWidth m A B p) p) := by
  let e := 2*m+2
  let L := steps p
  let M := (B*meshBase m A B p)*num 8
  let N := B*meshWidth m A B p
  have same : Γ ⊢[PRAAx] M ≐ N := by dsimp only [M,N,meshWidth]; ipra_ring
  have mw : Γ ⊢[PRAAx] massPrefix e A B M L ≐ massPrefix e A B N L := by
    simpa only [GaussianStirlingAllOrderPanelPartsOuterFold.subst_massPrefix,Syn.subst_var,
      Syn.inst_zero,Syn.subst_inst_shift] using
      Prf.eqCongr (Γ := Γ) (massPrefix e (Syn.shift A) (Syn.shift B) (var 0) (Syn.shift L))
        (σ := Syn.inst M) (σ' := Syn.inst N)
        (fun i => Fin.cases same (fun j => .eqRefl (var j)) i)
  have hp : Γ ⊢[PRAAx] panelPrefix m (e-1) A B M L ≐ panelPrefix m (2*m+1) A B N L := by
    have h : e-1=2*m+1 := by unfold e; omega
    rw [h]
    simpa only [GaussianStirlingAllOrderPanelPartsOuterFold.subst_panelPrefix,Syn.subst_var,
      Syn.inst_zero,Syn.subst_inst_shift] using
      Prf.eqCongr (Γ := Γ) (panelPrefix m (2*m+1) (Syn.shift A) (Syn.shift B) (var 0) (Syn.shift L))
        (σ := Syn.inst M) (σ' := Syn.inst N)
        (fun i => Fin.cases same (fun j => .eqRefl (var j)) i)
  exact (embed_sub (multiply (signedMean (m+1)) (massPrefix e A B M L)) (panelPrefix m (e-1) A B M L)).eqTrans
    (GaussianRationalSyntheticDivision.qsub_congr
      ((embed_multiply _ _).eqTrans (GaussianRationalSyntheticDivision.qmul_congr (.eqRefl _)
        (RationalGaussianRealPart.embed_congr mw)))
      (RationalGaussianRealPart.embed_congr hp))

private theorem gap_distance (m : ℕ) (p A B x : PTm n) (hs : Γ ⊢[PRAAx] source A B) :
    Γ ⊢[PRAAx] distanceBounded (embed (gap m (2*m+2) A B (B*meshBase m A B p) (steps p)))
      (ap2 (gapF m) p (gapData m A B x)) (gapRadius m B) (unit p) := by
  let e := 2*m+2
  let Q := meshWidth m A B p
  let M := B*Q
  let L := steps p
  have hp := unit_positive (Γ := Γ) p
  have hQ : Γ ⊢[PRAAx] le (requiredMesh m A B p) Q := by
    dsimp only [Q,meshWidth,meshBase,e]
    ipra_le 7*𝔞 (requiredMesh m A B p)+8*𝔞 (refinement m (2*m+2) A B)+8*𝔞 (unit p)
  have hcut : Γ ⊢[PRAAx] le (unit p) L :=
    le_trans (GaussianStirlingIntegerLimit.index_dominates_unit p) (le_succ_self _)
  have hmesh : Γ ⊢[PRAAx] le (unit p) M := by
    dsimp only [M,Q,meshWidth,meshBase,e]
    ipra_le 𝔞 B*(8*𝔞 (requiredMesh m A B p)+8*𝔞 (refinement m (2*m+2) A B)+7*𝔞 (unit p))
      +sl hs.andE₂*𝔞 (unit p)
  have mass := cofinal_mass_distance e (by unfold e; omega) A B M L (unit p) hs.andE₁ hp hmesh hcut
  have scaled := fixed_product_distance (meanPoint m) _ _ _ _ hp mass
  have ev := embed_multiply (Γ := Γ) (signedMean (m+1)) (primitive e A B)
  have mulDist := distance_congr (.eqRefl _) ev.eqSymm (.eqRefl _) (.eqRefl _) scaled
  have raw := GaussianNamedDifference.difference_distance _ _ _ _ _ _ _ hp mulDist
    (actual_prefix_distance m A B Q p x hs hQ)
  have named := distance_symmetric _ _ _ _ hp (difference_error m A B x p hs)
  exact distance_congr (aligned_gap m A B p).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hp raw named)

theorem gap_regular (m : ℕ) (A B x : PTm n) (hs : Γ ⊢[PRAAx] source A B) :
    Γ ⊢[PRAAx] GaussianEuclideanDistanceName.pointCN (gapF m) (gapData m A B x) :=
  GaussianNamedDifference.name_regular _ _ _ _ (constant_regular _) (name_regular m A B x hs)

theorem approximate_lower (m : ℕ) (p A B x : PTm n) (hs : Γ ⊢[PRAAx] source A B) :
    Γ ⊢[PRAAx] upper (fstT (ap2 constantF p (floorPoint m A B)))
      (fstT (ap2 (gapF m) p (gapData m A B x))) (gapRadius m B) (unit p) := by
  have h := upper_of_radius _ _ _ _ (scalar_coordinate_distance _ _ _ _ (unit_positive p) (gap_distance m p A B x hs))
  exact upper_congr (congrFst (constant_at _ _)).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (upper_order_left _ _ _ _ _ (raw_floor m p A B hs) h)

@[simp] theorem subst_floorPoint {l : ℕ} (σ : Fin n → PTm l) (m : ℕ) (A B : PTm n) :
    Syn.subst σ (floorPoint m A B) = floorPoint m (Syn.subst σ A) (Syn.subst σ B) := by
  simp [floorPoint,floorDenominator,marginDenominator,GaussianStirlingAllOrderBernoulliMeshMargin.coarseDen,
    GaussianStirlingAllOrderCenteredBernoulli.denominator,GaussianStirlingAllOrderBoxProductGap.weightDenominator,pw,one,two]

@[simp] theorem subst_gapData {l : ℕ} (σ : Fin n → PTm l) (m : ℕ) (A B x : PTm n) :
    Syn.subst σ (gapData m A B x) = gapData m (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ x) := by
  simp [gapData]

@[simp] theorem subst_gapRadius {l : ℕ} (σ : Fin n → PTm l) (m : ℕ) (B : PTm n) :
    Syn.subst σ (gapRadius m B) = gapRadius m (Syn.subst σ B) := by
  simp [gapRadius,power,pw,one]

theorem named_gap_lower (m : ℕ) (A B x : PTm n) (hs : Γ ⊢[PRAAx] source A B) :
    Γ ⊢[PRAAx] realOrder constantF (gapF m) (floorPoint m A B) (gapData m A B x) := by
  apply order_from_envelope _ _ _ _ (gapRadius m B) (constant_regular _) (gap_regular m A B x hs)
  refine .allI ?_
  let a := Syn.shift A
  let b := Syn.shift B
  let c := Syn.shift x
  let Δ := Γ.map Fm.shift
  have h : Δ ⊢[PRAAx] source a b := by simpa [Δ,a,b,Fm.shift,Syn.shift] using hs.shift
  simpa [envelope,a,b,c,Δ,Syn.shift] using approximate_lower m (var 0) a b c h

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderNamedUpperGap
