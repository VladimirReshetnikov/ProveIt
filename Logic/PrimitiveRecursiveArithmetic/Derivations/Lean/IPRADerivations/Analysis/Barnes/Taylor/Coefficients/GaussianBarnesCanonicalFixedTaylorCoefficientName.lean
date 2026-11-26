import IPRADerivations.Analysis.Barnes.Taylor.Coefficients.GaussianBarnesCanonicalTaylorProductCoefficientName
import IPRADerivations.Analysis.Barnes.Taylor.Coefficients.GaussianBarnesCanonicalTaylorProductFixedCutoff

/-!
# Regular Taylor coefficients at each literal finite Barnes cutoff

The coefficient sampler keeps the cutoff fixed and retimes only the
prefactor. An independent tail comparison relates this name to the
original cofinal coefficient when the fixed cutoff is late enough.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFixedTaylorCoefficientName

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianBarnesCanonicalExponentTaylorRetainedCoefficient (cutoff precision prefactorGain)
open GaussianBarnesCanonicalHigherRows (previous)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalTaylorProductCoefficientName (clock gain product_error_bound)
open GaussianBarnesCanonicalTaylorProductCoefficientCauchy (productCoefficient)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianExponentialReference (unit_monotone)
open GaussianFastValueCut (query_budget)
open GaussianGammaCanonicalExponent (constantF)
open GaussianNamedInverseRate (independentRate)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def ready (p z R B M e q : PTm n) : Fm PTm n :=
  le (prefactorGain R*unit (clock p z R B M e)) (unit q)

def sample (p z R B r M e : PTm n) : PTm n :=
  productCoefficient (precision (clock p z R B M e) R) z R B r M e

def data (z R B r M e : PTm n) : PTm n :=
  pairT r (GaussianBarnesCanonicalTaylorProductCoefficientName.data z R B M e)

private def sampleBody : PTm 2 :=
  let x := var 1
  let y := sndT x
  sample (var 0) (fstT y) (fstT (sndT y)) (fstT (sndT (sndT y))) (fstT x)
    (fstT (sndT (sndT (sndT y)))) (sndT (sndT (sndT (sndT y))))

def nameF : PR 2 := PTm.toPR sampleBody

@[simp] theorem subst_sample {l : ℕ} (σ : Fin n → PTm l) (p z R B r M e : PTm n) :
    Syn.subst σ (sample p z R B r M e) =
      sample (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ r)
        (Syn.subst σ M) (Syn.subst σ e) := by
  simp [sample,precision,prefactorGain,productCoefficient,GaussianBarnesCanonicalTaylorProduct.polynomial,
    GaussianBarnesCanonicalTaylorProduct.headPolynomial,GaussianBarnesCanonicalTaylorProduct.headDegree,
    GaussianBarnesCanonicalExponentTaylorCoefficientCauchy.linearGain,GaussianBarnesCanonicalPrefactorLipschitz.halfGain,
    GaussianBarnesCanonicalPrefactor.negativeHalf,one,two]

@[simp] theorem subst_data {l : ℕ} (σ : Fin n → PTm l) (z R B r M e : PTm n) :
    Syn.subst σ (data z R B r M e) =
      data (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ r)
        (Syn.subst σ M) (Syn.subst σ e) := by simp [data]

theorem sample_at (p z R B r M e : PTm n) : Γ ⊢[PRAAx] ap2 nameF p (data z R B r M e) ≐ sample p z R B r M e := by
  let x := data z R B r M e
  let y := sndT x
  have raw : Γ ⊢[PRAAx] ap2 nameF p x ≐ sample p (fstT y) (fstT (sndT y)) (fstT (sndT (sndT y)))
      (fstT x) (fstT (sndT (sndT (sndT y)))) (sndT (sndT (sndT (sndT y)))) := by
    simpa [nameF,sampleBody,ap2,y] using toPR_eq (Γ := Γ) sampleBody ![p,x]
  have hy : Γ ⊢[PRAAx] y ≐ pairT z (pairT R (pairT B (pairT M e))) := snd_pair _ _
  have tail := (congrSnd hy).eqTrans (snd_pair z (pairT R (pairT B (pairT M e))))
  have tail₂ := (congrSnd tail).eqTrans (snd_pair R (pairT B (pairT M e)))
  have tail₃ := (congrSnd tail₂).eqTrans (snd_pair B (pairT M e))
  refine raw.eqTrans ?_
  unfold x data
  ipra_congr (sample (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) : PTm 7) with
    [.eqRefl p, (congrFst hy).eqTrans (fst_pair z _), (congrFst tail).eqTrans (fst_pair R _),
      (congrFst tail₂).eqTrans (fst_pair B _), fst_pair r _, (congrFst tail₃).eqTrans (fst_pair M e),
      (congrSnd tail₃).eqTrans (snd_pair M e)]

theorem sample_ready (p z R B M e : PTm n) : Γ ⊢[PRAAx] ready p z R B M e (precision (clock p z R B M e) R) :=
  (GaussianBarnesCanonicalTaylorProductCoefficientName.sample_ready p z R B M e).andE₁

private theorem ready_weaken (p P z R B M e q : PTm n) (hp : Γ ⊢[PRAAx] le p P)
    (h : Γ ⊢[PRAAx] ready P z R B M e q) : Γ ⊢[PRAAx] ready p z R B M e q :=
  le_trans (le_mul_mono (le_refl _) (unit_monotone (add_le_add_right _ hp))) h

theorem ready_gap (p q t z R B r M e : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (he : Γ ⊢[PRAAx] le e (previous M)) (hq : Γ ⊢[PRAAx] ready p z R B M e q)
    (ht : Γ ⊢[PRAAx] ready p z R B M e t) :
    Γ ⊢[PRAAx] distanceBounded (productCoefficient q z R B r M e) (productCoefficient t z R B r M e) one (unit p) := by
  let P := clock p z R B M e
  have gap := GaussianBarnesCanonicalTaylorProductFixedCutoff.late_product_gap P q t z R B r M e hz he hq ht
  have realGap := GaussianCoefficientNormEntries.l1_to_euclidean _ _ _ (unit_positive P)
    (RationalArgmin.transitive gap (product_error_bound P z R B M e))
  exact distance_radius_mono _ _ _ _ _ _ (unit_positive P) (unit_positive p)
    (le_congr (.eqRefl _) (one_mul _).eqSymm (query_budget (gain z R B M e) p)) realGap

private theorem sample_gap (p q z R B r M e : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (he : Γ ⊢[PRAAx] le e (previous M)) :
    Γ ⊢[PRAAx] distanceBounded (sample p z R B r M e) (sample q z R B r M e)
      (unit p+unit q) (unit p*unit q) := by
  have hd := positive_product _ _ (unit_positive (Γ := Γ) p) (unit_positive q)
  have hp := sample_ready (Γ := Γ) p z R B M e
  have hq := sample_ready (Γ := Γ) q z R B M e
  refine .orE (le_total p q) ?_ ?_
  · exact distance_radius_mono _ _ _ _ _ _ (unit_positive p) hd.wk
      (le_of_eq_add (d := unit p*unit p) (by ipra_ring))
      (ready_gap p _ _ z R B r M e hz.wk he.wk hp.wk (ready_weaken p q z R B M e _ Prf.hyp0 hq.wk))
  · exact distance_radius_mono _ _ _ _ _ _ (unit_positive q) hd.wk
      (le_of_eq_add (d := unit q*unit q) (by ipra_ring))
      (ready_gap q _ _ z R B r M e hz.wk he.wk (ready_weaken q p z R B M e _ Prf.hyp0 hp.wk) hq.wk)

theorem regular (z R B r M e : PTm n) (hz : Γ ⊢[PRAAx] source z R B) (he : Γ ⊢[PRAAx] le e (previous M)) :
    Γ ⊢[PRAAx] pointCN nameF (data z R B r M e) := by
  refine .allI (.allI ?_)
  let sh (v : PTm n) := Syn.shift (Syn.shift v)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  let p : PTm (n+2) := var 1
  let q : PTm (n+2) := var 0
  have hz' : Δ ⊢[PRAAx] source (sh z) (sh R) (sh B) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hz.shift.shift
  have he' : Δ ⊢[PRAAx] le (sh e) (previous (sh M)) := by simpa [Δ,sh,Fm.shift,Syn.shift] using he.shift.shift
  simpa [pointCN,Δ,sh,p,q,Syn.shift,unit,GaussianEuclideanPointDistance.unit] using
    distance_congr (sample_at p (sh z) (sh R) (sh B) (sh r) (sh M) (sh e)).eqSymm
      (sample_at q (sh z) (sh R) (sh B) (sh r) (sh M) (sh e)).eqSymm (.eqRefl _) (.eqRefl _)
      (sample_gap p q (sh z) (sh R) (sh B) (sh r) (sh M) (sh e) hz' he')

theorem finite_rate (p z R B r M e q : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (he : Γ ⊢[PRAAx] le e (previous M)) (hq : Γ ⊢[PRAAx] ready p z R B M e q) :
    Γ ⊢[PRAAx] independentRate nameF constantF (data z R B r M e) (productCoefficient q z R B r M e)
      (one+one) (unit p) := by
  let x := data z R B r M e
  let u := ap2 nameF p x
  let v := productCoefficient q z R B r M e
  have h := ready_gap p _ q z R B r M e hz he (sample_ready p z R B M e) hq
  have exactSample : Γ ⊢[PRAAx] distanceBounded u v one (unit p) :=
    distance_congr (sample_at p z R B r M e).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) h
  exact GaussianNamedRateComposition.same_denominator nameF constantF constantF x u v one (unit p) one
    (unit_positive p) (GaussianSignedNameExponentialOrder.own_sample_rate _ _ _ (regular z R B r M e hz he))
    (GaussianNamedAddRate.constant_rate u v one (unit p) (unit_positive p) exactSample)

theorem cofinal_rate (p z R B r M e : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (he : Γ ⊢[PRAAx] le e (previous M)) (hr : Γ ⊢[PRAAx] le (cutoff (clock p z R B M e) R M) r) :
    Γ ⊢[PRAAx] independentRate GaussianBarnesCanonicalTaylorProductCoefficientName.nameF nameF
      (GaussianBarnesCanonicalTaylorProductCoefficientName.data z R B M e) (data z R B r M e)
      (one+(one+one)) (unit p) := by
  let q := precision (clock p z R B M e) R
  have hq := sample_ready (Γ := Γ) p z R B M e
  have left := GaussianBarnesCanonicalTaylorProductCoefficientName.finite_rate p z R B M e q r hz he (.andI hq hr)
  have right := finite_rate p z R B r M e q hz he hq
  exact GaussianNamedRateComposition.same_denominator _ _ _ _ _ _ one (unit p) (one+one)
    (unit_positive p) left (GaussianNamedRateComposition.symmetric _ _ _ _ _ _ (unit_positive p) right)

theorem actual_Barnes_fixed_cutoff_coefficient_regular_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    ((source (var 0) (var 1) (var 2) ⋏ le (var 5) (previous (var 4))) ⟶
      pointCN nameF (data (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))) :=
  closeUniv 6 (.impI (regular _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFixedTaylorCoefficientName
