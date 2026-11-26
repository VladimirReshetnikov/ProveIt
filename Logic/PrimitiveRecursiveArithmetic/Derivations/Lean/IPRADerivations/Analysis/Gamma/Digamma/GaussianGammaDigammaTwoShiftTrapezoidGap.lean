import IPRADerivations.Analysis.Gamma.Digamma.GaussianGammaDigammaTwoShiftLogGap

/-!
# Close logarithms with a ratio as large as three

The factorial-mesh trapezoid bound gives
log((c+w)/c) ≤ 2k/(c+w) when w ≤ k and c+w ≤ 3c.
This is the lower outside chord estimate for the two-shift rate.
-/

set_option autoImplicit false
set_option maxHeartbeats 2600000

namespace LeanProofs.IPRA.Analysis.GaussianGammaDigammaTwoShiftTrapezoidGap

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianCoefficientNameBounds (unit_positive)
open GaussianGammaDigammaHarmonicCells (cell halfReciprocal point_fraction_represents trapezoid_exact)
open GaussianHarmonicLogarithmName (sample)
open GaussianHarmonicLogarithmProduct (mesh mesh_later)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (positive_product qadd)
open GaussianRationalMetric (distanceBounded)
open RationalArgmin (rationalLE rationalLE_congr)
open RationalGaussianEmbedding (embed scalarZero scalar_zero_represents)
open RationalHarmonicInterval (interval common common_canonical horizon left_horizon)
open RationalRepresentedUpper (left right from_signed)
open RationalValueBounds (upper upper_of_order upper_order_left radius_of_upper)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

private theorem fraction_order (r s A B : PTm n) (hA : Γ ⊢[PRAAx] le one A)
    (hB : Γ ⊢[PRAAx] le one B) (h : Γ ⊢[PRAAx] le (r*B) (s*A)) :
    Γ ⊢[PRAAx] rationalLE (fstT (fraction r A)) (fstT (fraction s B)) := by
  apply RationalArithmetic.order_of_representations _ _ (ZT.ofNat r) (ZT.ofNat s) A B
    (point_fraction_represents r A hA) (point_fraction_represents s B hB) hA hB
  apply zle_of_toZ (monus (s*A) (r*B))
  have e := natEq (eq_add_of_le h)
  simp only [ZT.toZ_mul,ZT.toZ_ofNat]
  ipra_simps
  exact e.symm

private theorem fraction_nonnegative (r A : PTm n) (hA : Γ ⊢[PRAAx] le one A) :
    Γ ⊢[PRAAx] rationalLE scalarZero (fstT (fraction r A)) := by
  apply RationalArithmetic.order_of_representations _ _ (ZT.ofNat zero) (ZT.ofNat r) one A
    (scalar_zero_represents one) (point_fraction_represents r A hA) (le_refl _) hA
  apply zle_of_toZ r
  simp only [ZT.toZ_mul,ZT.toZ_ofNat]
  ipra_simps
  ring

private theorem fraction_upper (r a : PTm n) (ha : Γ ⊢[PRAAx] le one a) :
    Γ ⊢[PRAAx] upper (fstT (fraction r a)) scalarZero r a := by
  apply from_signed _ _ (ZT.ofNat r) (ZT.ofNat zero) a one r a ha (le_refl _)
    (point_fraction_represents r a ha) (scalar_zero_represents one)
  apply zle_of_toZ zero
  simp only [left,right,ZT.toZ_mul,ZT.toZ_add,ZT.toZ_ofNat]
  ipra_simps
  ring

private theorem interval_projection (a c Q : PTm n) : Γ ⊢[PRAAx] fstT (embed (interval a c Q)) ≐ interval a c Q :=
  (fst_pair _ _).eqTrans (RationalNormalForm.normalize_fixed_point _ (common_canonical a c Q (horizon a c Q)))

theorem trapezoid_gap (p c w b k : PTm n) (hc : Γ ⊢[PRAAx] le one c)
    (hw : Γ ⊢[PRAAx] le w k) (hRatio : Γ ⊢[PRAAx] le (c+w) (num 3*c)) :
    Γ ⊢[PRAAx] distanceBounded (sample p (c+w) b) (sample p c b) (two*k) (c+w) := by
  let a := c+w
  let Q := mesh p
  let L := horizon a c Q
  let V := cell a c Q L
  let T := qadd (halfReciprocal c w) (halfReciprocal a w)
  let R := fraction (two*k) a
  have ha : Γ ⊢[PRAAx] le one a := le_trans hc (le_add_right _ _)
  have hQ := le_trans (unit_positive (Γ := Γ) p) (mesh_later p)
  have hD : Γ ⊢[PRAAx] le one (two*c*a) :=
    positive_product _ _ (positive_product _ _ (le_succ_self one) hc) ha
  have hsum : Γ ⊢[PRAAx] le (two*c+w) (num 4*c) := by
    ipra_le sl hRatio
  have product := le_mul_mono hw hsum
  have clear : Γ ⊢[PRAAx] le ((w*(two*c+w))*a) ((two*k)*(two*c*a)) :=
    le_congr (.eqRefl _) (by ipra_ring) (le_mul_mono product (le_refl a))
  have tr := GaussianGammaDigammaHarmonicCells.trapezoid c w Q L hc hQ
  have tr' : Γ ⊢[PRAAx] rationalLE (fstT T) (fstT R) :=
    rationalLE_congr (congrFst (trapezoid_exact c w hc)).eqSymm (.eqRefl _)
      (fraction_order _ _ _ _ hD ha clear)
  have left := GaussianGammaDigammaHarmonicCells.right_rectangle c w Q L hc hQ (left_horizon a c Q)
  have lower := RationalArgmin.transitive (fraction_nonnegative w a ha) left
  have upper' := RationalArgmin.transitive tr tr'
  have e : Γ ⊢[PRAAx] fstT V ≐ interval a c Q := interval_projection a c Q
  have r := radius_of_upper (interval a c Q) scalarZero (two*k) a
    (upper_order_left _ _ _ _ _ (rationalLE_congr e (.eqRefl _) upper') (fraction_upper (two*k) a ha))
    (upper_of_order _ _ _ _ (rationalLE_congr (.eqRefl _) e lower))
  have d := RationalGaussianNameEmbedding.distance_from_radius _ _ _ _ ha r
  have base := GaussianRationalDistanceOrder.distance_congr (.eqRefl _) RationalGaussianEmbedding.embed_zero
    (.eqRefl _) (.eqRefl _) d
  have eq := (GaussianRationalReconstruction.qsub_zero_right (Γ := Γ) _ (RationalGaussianEmbedding.embed_canonical (interval a c Q))).eqTrans
    (GaussianGammaDigammaTwoShiftLogGap.sample_difference p a c b).eqSymm
  exact GaussianRationalReciprocal.bound_congr eq (.eqRefl _) (.eqRefl _) base

end LeanProofs.IPRA.Analysis.GaussianGammaDigammaTwoShiftTrapezoidGap
