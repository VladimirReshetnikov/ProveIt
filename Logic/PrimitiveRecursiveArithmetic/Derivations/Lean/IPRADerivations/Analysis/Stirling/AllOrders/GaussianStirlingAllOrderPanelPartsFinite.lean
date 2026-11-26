import IPRADerivations.Analysis.Stirling.AllOrders.GaussianStirlingAllOrderPanelPartsRows
import IPRADerivations.Analysis.Stirling.AllOrders.GaussianStirlingAllOrderDiscretePartsTransfer

/-!
# Finite discrete parts with the actual Bernoulli and reciprocal grids

The finite fold uses all interior grid points exactly once. The
local curvature differences therefore compare to the exact adjacent
boundary expression with the certified common dyadic-independent mesh error.
-/

set_option autoImplicit false
set_option maxHeartbeats 450000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderPanelPartsFinite

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianStirlingAllOrderCenteredBernoulli (sample)
open GaussianStirlingAllOrderBernoulliEnvelope (subst_sample)
open GaussianStirlingAllOrderPanelDerivative (secondSample secondNumerator)
open GaussianStirlingAllOrderReciprocalWeightError (weight power derivative coefficient)
open GaussianStirlingAllOrderReciprocalGridError (gridDen gridCoefficient)
open GaussianStirlingAllOrderPanelPartsRows (approxRow targetRow rowRadius row_error profileCap)
open GaussianStirlingAllOrderCentralBernoulliError (radiusNumerator)
open GaussianStirlingAllOrderDiscreteParts (defect secondDifference sub)
open GaussianStirlingAllOrderDiscretePartsTransfer (rawBody rawData boundary raw_row finite_error)
open GaussianEuclideanDistanceName (fraction)
open GaussianRationalHorner (positive_product)
open RationalGaussianEmbedding (embed)
open RationalGaussianRealPart (embedBody embed_congr)
open GaussianRationalRiemannRefinement (termsDistance)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr)
open RationalAlgebra (multiply_congr)
open RationalFiniteSum (term)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def interior (M : PTm n) : PTm n := monus M one
def profileBody (m : ℕ) : PTm 2 := sample (m+1) (var 0) (var 1)
def parameters (U B M : PTm n) : PTm n := pairT U (pairT B M)

def weightAt (e : ℕ) (U B M i : PTm n) : PTm n := weight e B M (gridDen U B M i)
def weightBody (e : ℕ) : PTm 2 :=
  let u := var 1
  weightAt e (fstT u) (fstT (sndT u)) (sndT (sndT u)) (var 0)

def densityBody (m e : ℕ) : PTm 2 :=
  let u := var 1
  targetRow m e (fstT u) (fstT (sndT u)) (sndT (sndT u)) (succ (var 0))

def interiorDensity (m e : ℕ) (U B M : PTm n) : PTm n :=
  RationalFiniteSum.sum (densityBody m e) (interior M) (parameters U B M)

def boundaryValue (m e : ℕ) (U B M : PTm n) : PTm n :=
  boundary (profileBody m) (weightBody e) (interior M) (fraction (M*M) one) M (parameters U B M)

@[simp] theorem subst_interior {l : ℕ} (σ : Fin n → PTm l) (M : PTm n) :
    Syn.subst σ (interior M) = interior (Syn.subst σ M) := by simp [interior]
@[simp] theorem subst_parameters {l : ℕ} (σ : Fin n → PTm l) (U B M : PTm n) :
    Syn.subst σ (parameters U B M) = parameters (Syn.subst σ U) (Syn.subst σ B) (Syn.subst σ M) := by simp [parameters]
@[simp] theorem subst_weightAt {l : ℕ} (σ : Fin n → PTm l) (e : ℕ) (U B M i : PTm n) :
    Syn.subst σ (weightAt e U B M i) = weightAt e (Syn.subst σ U) (Syn.subst σ B) (Syn.subst σ M) (Syn.subst σ i) := by
  simp [weightAt,weight,power,gridDen,pw]

private theorem subst_signed_sum {l d : ℕ} (σ : Fin n → PTm l) (f : Fin d → ZT n) :
    (ZT.sumFin f).subst σ = ZT.sumFin (fun i => (f i).subst σ) := by
  induction d with
  | zero => simp only [ZT.sumFin,ZT.subst_natLit]
  | succ d ih => simp only [ZT.sumFin,ZT.subst_add,ih]

@[simp] theorem subst_targetRow {l : ℕ} (σ : Fin n → PTm l) (m e : ℕ) (U B M r : PTm n) :
    Syn.subst σ (targetRow m e U B M r) = targetRow m e (Syn.subst σ U) (Syn.subst σ B) (Syn.subst σ M) (Syn.subst σ r) := by
  simp [targetRow,weight,power,derivative,coefficient,gridDen,secondSample,secondNumerator,
    GaussianStirlingAllOrderCenteredBernoulli.denominator,BernoulliBounds.pv,BernoulliBounds.zint,subst_signed_sum,pw]

@[simp] theorem profile_at (m : ℕ) (M i : PTm n) :
    inst2 (profileBody m) i M = sample (m+1) i M := by simp [profileBody,inst2]

private theorem selector₂ (U B M : PTm n) : Γ ⊢[PRAAx] fstT (sndT (parameters U B M)) ≐ B :=
  (congrFst (snd_pair U (pairT B M))).eqTrans (fst_pair B M)

private theorem selector₃ (U B M : PTm n) : Γ ⊢[PRAAx] sndT (sndT (parameters U B M)) ≐ M :=
  (congrSnd (snd_pair U (pairT B M))).eqTrans (snd_pair B M)

theorem weight_at (e : ℕ) (U B M i : PTm n) :
    Γ ⊢[PRAAx] inst2 (weightBody e) i (parameters U B M) ≐ weightAt e U B M i := by
  let x := parameters U B M
  simpa [weightBody,inst2,x] using Prf.eqCongr (Γ := Γ) (weightAt e (var 0) (var 1) (var 2) (var 3) : PTm 4)
    (σ := ![fstT x,fstT (sndT x),sndT (sndT x),i]) (σ' := ![U,B,M,i]) (fun j => by
      fin_cases j
      exact fst_pair _ _
      exact selector₂ U B M
      exact selector₃ U B M
      exact .eqRefl _)

theorem density_at (m e : ℕ) (U B M i : PTm n) :
    Γ ⊢[PRAAx] term (densityBody m e) i (parameters U B M) ≐ targetRow m e U B M (succ i) := by
  let x := parameters U B M
  simpa [densityBody,term,inst2,x] using Prf.eqCongr (Γ := Γ)
    (targetRow m e (var 0) (var 1) (var 2) (var 3) : PTm 4)
    (σ := ![fstT x,fstT (sndT x),sndT (sndT x),succ i]) (σ' := ![U,B,M,succ i]) (fun j => by
      fin_cases j
      exact fst_pair _ _
      exact selector₂ U B M
      exact selector₃ U B M
      exact .eqRefl _)

private theorem defect_congr {a b c d e f a' b' c' d' e' f' : PTm n}
    (ha : Γ ⊢[PRAAx] a ≐ a') (hb : Γ ⊢[PRAAx] b ≐ b') (hc : Γ ⊢[PRAAx] c ≐ c')
    (hd : Γ ⊢[PRAAx] d ≐ d') (he : Γ ⊢[PRAAx] e ≐ e') (hf : Γ ⊢[PRAAx] f ≐ f') :
    Γ ⊢[PRAAx] defect a b c d e f ≐ defect a' b' c' d' e' f' := by
  exact RationalAlgebra.add_congr
    (multiply_congr (RationalAlgebra.add_congr (RationalAlgebra.add_congr hc ha)
      (RationalAlgebra.negative_congr (RationalAlgebra.add_congr hb hb))) he)
    (RationalAlgebra.negative_congr (multiply_congr hb
      (RationalAlgebra.add_congr (RationalAlgebra.add_congr hf hd)
        (RationalAlgebra.negative_congr (RationalAlgebra.add_congr he he)))))

private theorem profile_congr (m : ℕ) (M i j : PTm n) (h : Γ ⊢[PRAAx] i ≐ j) :
    Γ ⊢[PRAAx] sample (m+1) i M ≐ sample (m+1) j M :=
  GaussianStirlingAllOrderBernoulliEnvelope.sample_congr (m+1) h (.eqRefl _)

private theorem weight_congr (e : ℕ) (U B M i j : PTm n) (h : Γ ⊢[PRAAx] i ≐ j) :
    Γ ⊢[PRAAx] weightAt e U B M i ≐ weightAt e U B M j :=
  RationalNonnegativePowers.fraction_congr (.eqRefl _) (congrAp2 powF (.eqRefl _) (congrAdd (.eqRefl _) (congrMul (.eqRefl _) h)))

theorem actual_row_at (m e : ℕ) (U B M i : PTm n) :
    Γ ⊢[PRAAx] term (rawBody (profileBody m) (weightBody e)) i (rawData (fraction (M*M) one) M (parameters U B M)) ≐
      approxRow m e U B M (succ i) := by
  have l : Γ ⊢[PRAAx] i ≐ monus (succ i) one := by
    have hi := natEq (eq_add_of_le (zero_lt_succ (Γ := Γ) i))
    apply deriveNat
    ipra_simps
    linear_combination hi
  have r : Γ ⊢[PRAAx] succ (succ i) ≐ succ i+one := by ipra_ring
  have rw (u v : PTm n) (h : Γ ⊢[PRAAx] u ≐ v) :
      Γ ⊢[PRAAx] inst2 (weightBody e) u (parameters U B M) ≐ weightAt e U B M v :=
    (weight_at e U B M u).eqTrans (weight_congr e U B M u v h)
  refine (raw_row (profileBody m) (weightBody e) i (fraction (M*M) one) M (parameters U B M)).eqTrans ?_
  simp only [profile_at]
  exact multiply_congr (.eqRefl _) (defect_congr (profile_congr m M _ _ l) (.eqRefl _)
    (profile_congr m M _ _ r) (rw i _ l) (weight_at e U B M (succ i)) (rw (succ (succ i)) _ r))

theorem interior_le_mesh (M : PTm n) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] le (interior M) M :=
  le_congr (.eqRefl _) (eq_add_of_le hM).eqSymm (le_add_left (interior M) one)

theorem interior_error (m e : ℕ) (hm : 0<m) (he : 2≤e) (U B M : PTm n)
    (hU : Γ ⊢[PRAAx] le one U) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] distanceBounded (embed (boundaryValue m e U B M)) (embed (interiorDensity m e U B M))
      (interior M*rowRadius m e U B) (M*M) := by
  let f := profileBody m
  let g := weightBody e
  let t := densityBody m e
  let v := fraction (M*M) one
  let x := parameters U B M
  have rows : Γ ⊢[PRAAx] termsDistance (embedBody (rawBody f g)) (embedBody t) (interior M) (rawData v M x) x
      (rowRadius m e U B) (M*M) := by
    refine .allI (.impI ?_)
    let u := Syn.shift U
    let b := Syn.shift B
    let d := Syn.shift M
    let Δ := lt (var 0) (Syn.shift (interior M)) :: Γ.map Fm.shift
    have hu : Δ ⊢[PRAAx] le one u := by simpa [u,Δ,Syn.shift,Fm.shift] using hU.shift.wk
    have hd : Δ ⊢[PRAAx] le one d := by simpa [d,Δ,Syn.shift,Fm.shift] using hM.shift.wk
    have hr : Δ ⊢[PRAAx] le (succ (var 0)) (interior d) := by
      change Δ ⊢[PRAAx] lt (var 0) (interior d)
      simpa [Δ,d,Syn.shift] using (Prf.hyp0 : Δ ⊢[PRAAx] lt (var 0) (Syn.shift (interior M)))
    have hi := le_trans hr (interior_le_mesh d hd)
    have rowObs := row_error m e hm he u b d (succ (var 0)) hu hd (zero_lt_succ _) hi
    have ans := distance_congr (embed_congr (actual_row_at m e u b d (var 0))).eqSymm
      (embed_congr (density_at m e u b d (var 0))).eqSymm (.eqRefl _) (.eqRefl _) rowObs
    simpa [termsDistance,embedBody,term,inst2,rowRadius,f,g,t,v,x,u,b,d,Δ,Syn.shift,
      radiusNumerator,power,gridCoefficient,profileCap,pw,one,RationalSupMetric.numeratorOf,
      GaussianStirlingAllOrderBernoulliEnvelope.cap] using ans
  exact finite_error f g t (interior M) v M x x _ _ (positive_product _ _ hM hM) rows

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderPanelPartsFinite
