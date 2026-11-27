import IPRADerivations.Analysis.Stirling.AllOrders.PanelParts.FinitePanels.GaussianStirlingAllOrderPanelPartsFold
import IPRADerivations.Analysis.Stirling.AllOrders.PanelParts.FinitePanels.GaussianStirlingAllOrderPanelPartsBoundary

/-!
# Actual finite integration-by-parts recurrence for the Bernoulli panels

This preserves the original complete sampled panels. The omitted left
endpoint of the interior density is the mean times the reciprocal
weight at zero. After restoring that term the normalized recurrence
has a fully explicit O(M^-1) error.
-/

set_option autoImplicit false
set_option maxHeartbeats 950000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderPanelPartsRecurrence

open_ipra
open GaussianStirlingAllOrderPanelPartsFinite (interior weightAt weightBody weight_at interiorDensity)
open GaussianStirlingAllOrderPanelPartsFold
  (weightInput prevInput nextInput mass previous following prev_at next_at fold_identity)
open GaussianStirlingAllOrderPanelPartsBoundary (boundaryCap interior_density_bound)
open GaussianStirlingAllOrderPanelPartsRows (rowRadius weight_bound scalar_order_bound)
open GaussianStirlingAllOrderPanelPartsDensities (lowScalar highScalar previousDensity nextDensity)
open GaussianStirlingAllOrderPanelDerivative (signedMean)
open GaussianStirlingAllOrderPanelTail (panel panelData panelBody)
open GaussianStirlingAllOrderPanelRotation (nextBody rotate)
open GaussianStirlingAllOrderCenteredBernoulli (endpoint_samples_zero)
open GaussianStirlingAllOrderKernel (multiply_zero_right)
open GaussianStirlingAllOrderReciprocalWeightError (power)
open GaussianStirlingAllOrderDiscreteParts (sub)
open GaussianEuclideanDistanceName (fraction fraction_order)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (bounded)
open GaussianRationalPowerDifference (bounded_sum_same)
open GaussianRationalReciprocal (bounded_product bound_congr)
open GaussianRationalSyntheticDivision (qadd_congr)
open GaussianRationalSumAlgebra (qadd_associative)
open RationalArithmetic (add multiply negative)
open RationalAlgebra (add_congr add_associative add_commutative multiply_congr multiply_commutative
  multiply_associative multiply_add multiply_negative negative_congr)
open RationalGaussianEmbedding (embed embed_add embed_multiply)
open RationalGaussianRealPart (embed_congr)
open RationalArgmin (reflexive)
open RationalFiniteSum (term)
open RationalReciprocalPowerTail (add_zero_right)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "rsum" => RationalFiniteSum.sum

def fullMass (e : ℕ) (U B M : PTm n) : PTm n :=
  rsum (weightBody e) M (weightInput U B M)

def panelMass (e : ℕ) (U B M : PTm n) : PTm n :=
  multiply (fraction one M) (fullMass e U B M)

def rawResidual (m e : ℕ) (U B M : PTm n) : PTm n :=
  sub (multiply (lowScalar m) (sub (multiply (signedMean m) (fullMass e U B M))
    (rsum (panelBody (m-1)) M (prevInput e U B M))))
    (multiply (highScalar e) (rsum (panelBody m) M (nextInput e U B M)))

def residual (m e : ℕ) (U B M : PTm n) : PTm n :=
  sub (multiply (lowScalar m) (sub (multiply (signedMean m) (panelMass e U B M))
    (panel (m-1) (num (e-1)) U B M zero)))
    (multiply (highScalar e) (panel m (num (e+1)) U B M zero))

def endpointCap (m : ℕ) : PTm n :=
  GaussianNameBounds.U constantF (embed (multiply (lowScalar m) (signedMean m)))

def errorCoefficient (m e : ℕ) (U B : PTm n) : PTm n :=
  rowRadius m e U B+boundaryCap m e B+endpointCap m*power e B

theorem join_full_prefix (f : PTm 2) (x M : PTm n) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] rsum f M x ≐ add (term f zero x) (rsum (nextBody f) (interior M) x) := by
  let N := interior M
  have hs : Γ ⊢[PRAAx] M ≐ succ N :=
    (eq_add_of_le hM).eqTrans ((add_comm _ _).eqTrans (succ_eq_add_one N).eqSymm)
  have e : Γ ⊢[PRAAx] rsum f M x ≐ rsum f (succ N) x := by
    simpa only [RationalFiniteSum.subst_sum,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using
      Prf.eqCongr (Γ := Γ) (rsum f (var 0) (var 1) : PTm 2)
        (σ := ![M,x]) (σ' := ![succ N,x]) (fun i => by fin_cases i; exact hs; exact .eqRefl _)
  exact e.eqTrans ((RationalFiniteSum.sum_succ f N x).eqTrans (rotate f N x))

private theorem join_zero_prefix (f : PTm 2) (x M : PTm n) (hM : Γ ⊢[PRAAx] le one M)
    (hz : Γ ⊢[PRAAx] term f zero x ≐ fraction zero one) :
    Γ ⊢[PRAAx] rsum f M x ≐ rsum (nextBody f) (interior M) x :=
  (join_full_prefix f x M hM).eqTrans ((add_congr hz (.eqRefl _)).eqTrans
    ((add_commutative _ _).eqTrans (add_zero_right _ (RationalFiniteSum.sum_well_formed _ _ _))))

private theorem shuffle (a b c : PTm n) : Γ ⊢[PRAAx] add (add a b) c ≐ add (add a c) b :=
  (add_associative _ _ _).eqTrans ((add_congr (.eqRefl _) (add_commutative _ _)).eqTrans (add_associative _ _ _).eqSymm)

private theorem restore_endpoint (m e : ℕ) (hm : 0<m) (he : 2≤e) (U B M : PTm n)
    (hU : Γ ⊢[PRAAx] le one U) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] rawResidual m e U B M ≐ add (interiorDensity m e U B M)
      (multiply (multiply (lowScalar m) (signedMean m)) (weightAt e U B M zero)) := by
  let N := interior M
  let a := previous m e N U B M
  let b := following m e N U B M
  let z := weightAt e U B M zero
  let W := mass e N U B M
  let c := signedMean (n := n) m
  let L := lowScalar (n := n) m
  let K := highScalar (n := n) e
  have eW : Γ ⊢[PRAAx] fullMass e U B M ≐ add z W :=
    (join_full_prefix _ _ _ hM).eqTrans (add_congr (weight_at e U B M zero) (.eqRefl _))
  have ha : Γ ⊢[PRAAx] term (panelBody (m-1)) zero (prevInput e U B M) ≐ fraction zero one :=
    (prev_at m e hm he U B M zero).eqTrans
      ((multiply_congr (endpoint_samples_zero m M hM).1 (.eqRefl _)).eqTrans
        ((multiply_commutative _ _).eqTrans (multiply_zero_right _)))
  have hb : Γ ⊢[PRAAx] term (panelBody m) zero (nextInput e U B M) ≐ fraction zero one :=
    (next_at m e U B M zero).eqTrans
      ((multiply_congr (endpoint_samples_zero (m+1) M hM).1 (.eqRefl _)).eqTrans
        ((multiply_commutative _ _).eqTrans (multiply_zero_right _)))
  have hA := join_zero_prefix _ _ M hM ha
  have hB := join_zero_prefix _ _ M hM hb
  have h₀ : Γ ⊢[PRAAx] rawResidual m e U B M ≐
      sub (multiply L (sub (multiply c (add z W)) a)) (multiply K b) :=
    add_congr (multiply_congr (.eqRefl _) (add_congr (multiply_congr (.eqRefl _) eW) (negative_congr hA)))
      (negative_congr (multiply_congr (.eqRefl _) hB))
  have h₁ : Γ ⊢[PRAAx] sub (multiply c (add z W)) a ≐ add (sub (multiply c W) a) (multiply c z) :=
    (add_congr (multiply_add _ _ _) (.eqRefl _)).eqTrans
      ((add_congr (add_commutative _ _) (.eqRefl _)).eqTrans (shuffle _ _ _))
  have h₂ : Γ ⊢[PRAAx] multiply L (sub (multiply c (add z W)) a) ≐
        add (multiply L (sub (multiply c W) a)) (multiply (multiply L c) z) :=
    (multiply_congr (.eqRefl _) h₁).eqTrans ((multiply_add _ _ _).eqTrans
      (add_congr (.eqRefl _) (multiply_associative _ _ _).eqSymm))
  exact h₀.eqTrans ((add_congr h₂ (.eqRefl _)).eqTrans ((shuffle _ _ _).eqTrans
    (add_congr (fold_identity m e hm he U B M hU hM).eqSymm (.eqRefl _))))

private theorem raw_error (m e : ℕ) (hm : 0<m) (he : 2≤e) (U B M : PTm n)
    (hU : Γ ⊢[PRAAx] le one U) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] bounded (embed (rawResidual m e U B M)) (errorCoefficient m e U B) one := by
  let c := embed (multiply (lowScalar m) (signedMean m) : PTm n)
  let z := weightAt e U B M zero
  have hc : Γ ⊢[PRAAx] bounded c (endpointCap m) one :=
    bound_congr (constant_at zero c) (.eqRefl _) (.eqRefl _)
      (GaussianNameBounds.sample_bound constantF c zero (constant_regular c))
  have hz := weight_bound e U B M zero hU hM
  have hP : Γ ⊢[PRAAx] bounded (embed (multiply (multiply (lowScalar m) (signedMean m)) z))
      (endpointCap m*power e B) one :=
    bound_congr (embed_multiply (multiply (lowScalar m) (signedMean m)) z).eqSymm (.eqRefl _) (one_mul one)
      (bounded_product _ _ _ _ _ _ (le_refl one) (le_refl one) hc hz)
  have hr := interior_density_bound m e hm he U B M hU hM
  have ef := (embed_congr (restore_endpoint m e hm he U B M hU hM)).eqTrans (embed_add _ _)
  exact bound_congr ef.eqSymm (.eqRefl _) (.eqRefl _) (bounded_sum_same _ _ _ _ _ (le_refl one) hr hP)

private theorem multiply_sub (w a b : PTm n) :
    Γ ⊢[PRAAx] multiply w (sub a b) ≐ sub (multiply w a) (multiply w b) :=
  (multiply_add _ _ _).eqTrans (add_congr (.eqRefl _) (multiply_negative _ _))

private theorem commute_scale (w a b : PTm n) :
    Γ ⊢[PRAAx] multiply w (multiply a b) ≐ multiply a (multiply w b) :=
  (multiply_associative _ _ _).eqSymm.eqTrans
    ((multiply_congr (multiply_commutative _ _) (.eqRefl _)).eqTrans (multiply_associative _ _ _))

theorem normalize_residual (m e : ℕ) (U B M : PTm n) :
    Γ ⊢[PRAAx] multiply (fraction one M) (rawResidual m e U B M) ≐ residual m e U B M := by
  let s := fraction one M
  let a := rsum (panelBody (m-1)) M (prevInput e U B M)
  let b := rsum (panelBody m) M (nextInput e U B M)
  let w := fullMass e U B M
  let c := signedMean (n := n) m
  let L := lowScalar (n := n) m
  let K := highScalar (n := n) e
  have h : Γ ⊢[PRAAx] multiply s (multiply L (sub (multiply c w) a)) ≐
      multiply L (sub (multiply c (multiply s w)) (multiply s a)) :=
    (commute_scale _ _ _).eqTrans (multiply_congr (.eqRefl _) ((multiply_sub _ _ _).eqTrans
      (add_congr (commute_scale _ _ _) (.eqRefl _))))
  exact (multiply_sub _ _ _).eqTrans (add_congr h (negative_congr (commute_scale _ _ _)))

theorem finite_panel_recurrence (m e : ℕ) (hm : 0<m) (he : 2≤e) (U B M : PTm n)
    (hU : Γ ⊢[PRAAx] le one U) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] bounded (embed (residual m e U B M)) (errorCoefficient m e U B) M := by
  let s := fraction one M
  let a := rawResidual m e U B M
  have hs : Γ ⊢[PRAAx] bounded (embed s) one M :=
    scalar_order_bound _ _ _ hM (fraction_order _ _ _ _ (le_refl one) hM (by ipra_le 1)) (reflexive _)
  have hb := raw_error m e hm he U B M hU hM
  have h := bounded_product _ _ _ _ _ _ hM (le_refl one) hs hb
  have e₂ := (embed_multiply (Γ := Γ) s a).eqSymm.eqTrans (embed_congr (normalize_residual m e U B M))
  exact bound_congr e₂ (one_mul _) (by ipra_ring) h

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderPanelPartsRecurrence
