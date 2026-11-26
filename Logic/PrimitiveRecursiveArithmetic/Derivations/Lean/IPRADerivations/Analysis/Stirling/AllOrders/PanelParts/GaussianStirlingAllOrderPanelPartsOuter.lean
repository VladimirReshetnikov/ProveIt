import IPRADerivations.Analysis.Stirling.AllOrders.PanelParts.GaussianStirlingAllOrderPanelPartsRecurrence
import IPRADerivations.Analysis.FiniteOperations.FiniteSums.GaussianUniformFiniteSumBound

/-!
# Quantitative outer sum of the actual panel recurrences

The finite error is uniform on every bounded prefix of the improper
integral. The original panel kernels and mesh are retained at every
runtime index.
-/

set_option autoImplicit false
set_option maxHeartbeats 950000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderPanelPartsOuter

open_ipra
open GaussianStirlingAllOrderPanelPartsRecurrence (residual endpointCap errorCoefficient finite_panel_recurrence)
open GaussianStirlingAllOrderPanelPartsRows (rowRadius)
open GaussianStirlingAllOrderReciprocalGridError (gridCoefficient)
open GaussianStirlingAllOrderReciprocalWeightError (power)
open GaussianUniformFiniteSumBound (summandsBounded uniform_sum_bound)
open GaussianRationalMetric (bounded)
open GaussianRationalReciprocal (bound_congr)
open GaussianCoefficientNameBounds (bounded_radius_mono)
open RationalGaussianEmbedding (embed)
open RationalGaussianRealPart (embedBody embed_congr embed_sum)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

def data (A B M : PTm n) : PTm n := pairT A (pairT B M)
def body (m e : ℕ) : PTm 2 :=
  let x := var 1
  residual m e (fstT x+fstT (sndT x)*var 0) (fstT (sndT x)) (sndT (sndT x))

def errorSum (m e : ℕ) (A B M L : PTm n) : PTm n :=
  RationalFiniteSum.sum (body m e) L (data A B M)

ipra_subst data

@[simp] theorem subst_residual {l : ℕ} (σ : Fin n → PTm l) (m e : ℕ) (U B M : PTm n) :
    Syn.subst σ (residual m e U B M) = residual m e (Syn.subst σ U) (Syn.subst σ B) (Syn.subst σ M) := by
  simp [GaussianStirlingAllOrderPanelPartsRecurrence.residual,GaussianStirlingAllOrderPanelPartsRecurrence.panelMass,
    GaussianStirlingAllOrderPanelPartsRecurrence.fullMass,GaussianStirlingAllOrderPanelPartsFold.weightInput,
    GaussianStirlingAllOrderPanelPartsDensities.lowScalar,GaussianStirlingAllOrderPanelPartsDensities.highScalar,
    GaussianStirlingAllOrderPanelDerivative.signedMean,GaussianStirlingAllOrderDiscreteParts.sub,
    GaussianStirlingAllOrderReciprocalWeightError.coefficient,GaussianStirlingAllOrderPanelPartsFinite.parameters,
    GaussianEuclideanDistanceName.fraction,GaussianStirlingAllOrderPanelDerivative.meanNumerator,
    BernoulliBounds.zint]

theorem row_at (m e : ℕ) (A B M k : PTm n) : Γ ⊢[PRAAx]
    RationalFiniteSum.term (body m e) k (data A B M) ≐ residual m e (A+B*k) B M := by
  let x := data A B M
  have r : Γ ⊢[PRAAx] sndT x ≐ pairT B M := snd_pair _ _
  have p := (congrFst r).eqTrans (fst_pair _ _)
  have q := (congrSnd r).eqTrans (snd_pair _ _)
  have w : Γ ⊢[PRAAx] fstT x+fstT (sndT x)*k ≐ A+B*k :=
    congrAdd (fst_pair _ _) (congrMul p (.eqRefl _))
  simpa only [RationalFiniteSum.term,body,inst2,subst_residual,subst_fstT,subst_sndT,
    PTm.subst_add,PTm.subst_mul,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (Γ := Γ) (residual m e (var 0) (var 1) (var 2) : PTm 3)
      (σ := ![fstT x+fstT (sndT x)*k,fstT (sndT x),sndT (sndT x)]) (σ' := ![A+B*k,B,M])
      (fun i => by fin_cases i; exact w; exact p; exact q)

theorem error_coefficient_monotone (m e : ℕ) (U V B : PTm n)
    (h : Γ ⊢[PRAAx] le U V) : Γ ⊢[PRAAx] le (errorCoefficient m e U B) (errorCoefficient m e V B) := by
  let w := GaussianStirlingAllOrderReciprocalTaylorBound.width e
  have hl : Γ ⊢[PRAAx] le (power w (U+B)) (power w (V+B)) :=
    pw_le_pw (LeanProofs.IPRA.PTm.num w) (add_le_add_right B h)
  have hg : Γ ⊢[PRAAx] le (gridCoefficient e U B) (gridCoefficient e V B) := by
    unfold gridCoefficient
    ipra_le 𝔞 (power e B)*𝔞 (LeanProofs.IPRA.PTm.num (GaussianStirlingAllOrderReciprocalTaylorBound.size e))*𝔞 (power 4 B)*sl hl
  unfold errorCoefficient rowRadius
  ipra_le 𝔞 (GaussianStirlingAllOrderPanelPartsRows.profileCap m)*sl hg

ipra_subst errorCoefficient [rowRadius, gridCoefficient, power, GaussianStirlingAllOrderPanelPartsBoundary.boundaryCap, endpointCap, GaussianStirlingAllOrderPanelPartsRows.profileCap, GaussianStirlingAllOrderCentralBernoulliError.radiusNumerator, GaussianStirlingAllOrderPanelDerivative.signedMean, GaussianStirlingAllOrderPanelDerivative.meanNumerator, GaussianStirlingAllOrderPanelPartsDensities.lowScalar, BernoulliBounds.zint, RationalSupMetric.numeratorOf]

theorem finite_outer_recurrence (m e : ℕ) (hm : 0<m) (he : 2≤e) (A B M L : PTm n)
    (hA : Γ ⊢[PRAAx] le one A) (hM : Γ ⊢[PRAAx] le one M) : Γ ⊢[PRAAx]
    bounded (embed (errorSum m e A B M L)) (L*errorCoefficient m e (A+B*L) B) M := by
  let f := body m e
  let x := data A B M
  have rows : Γ ⊢[PRAAx] summandsBounded (embedBody f) L x (errorCoefficient m e (A+B*L) B) M := by
    refine .allI (.impI ?_)
    let a := Syn.shift A
    let b := Syn.shift B
    let z := Syn.shift M
    let l := Syn.shift L
    let j : PTm (n+1) := var 0
    let Δ := lt j l :: Γ.map Fm.shift
    have ha : Δ ⊢[PRAAx] le one a := by simpa [a,Δ,Fm.shift,Syn.shift] using hA.shift.wk
    have hz : Δ ⊢[PRAAx] le one z := by simpa [z,Δ,Fm.shift,Syn.shift] using hM.shift.wk
    have hj : Δ ⊢[PRAAx] lt j l := Prf.hyp0
    have hU := le_trans ha (le_add_right a (b*j))
    have hj' := le_trans (le_succ_self j) hj
    have hV : Δ ⊢[PRAAx] le (a+b*j) (a+b*l) := by ipra_le 𝔞 b*sl hj'
    have rb := finite_panel_recurrence m e hm he (a+b*j) b z hU hz
    have lifted := error_coefficient_monotone m e (a+b*j) (a+b*l) b hV
    have hm' : Δ ⊢[PRAAx] le (errorCoefficient m e (a+b*j) b*z) (errorCoefficient m e (a+b*l) b*z) :=
      mul_le_mul_right _ lifted
    have hb := bounded_radius_mono _ _ _ _ _ hz hz hm' rb
    have eq := (show Δ ⊢[PRAAx] inst2 (embedBody f) j (data a b z) ≐ embed (RationalFiniteSum.term f j (data a b z)) by
      simp only [embedBody,inst2,RationalGaussianEmbedding.subst_embed,RationalFiniteSum.term]
      exact .eqRefl _).eqTrans (embed_congr (row_at m e a b z j))
    have rr : Δ ⊢[PRAAx] bounded (inst2 (embedBody f) j (data a b z)) (errorCoefficient m e (a+b*l) b) z :=
      bound_congr eq.eqSymm (.eqRefl _) (.eqRefl _) hb
    simpa [summandsBounded,x,a,b,z,l,j,Δ,Syn.shift] using rr
  exact bound_congr (embed_sum f L x).eqSymm (.eqRefl _) (.eqRefl _)
    (uniform_sum_bound (embedBody f) L x _ M hM rows)

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderPanelPartsOuter
