import IPRADerivations.Analysis.Polynomials.Horner.Perturbation.GaussianRationalHornerRadiusLipschitz
import IPRADerivations.Analysis.Polynomials.RootFinding.Adequacy.Membership.GaussianRootResidualFromHit
import IPRADerivations.Analysis.Geometry.Distances.GaussianEuclideanDistanceName
import IPRADerivations.Analysis.Names.Approximation.GaussianRepresentedPointBounds
import IPRADerivations.Analysis.Names.Order.GaussianFastValueCut
import IPRADerivations.Analysis.Polynomials.Evaluation.GaussianPolynomialValueName

/-!
# Sharp M_Z residual estimates from actual finite root hits

The sample disk is Z+2^(-s), not the smaller disk Z. Actual rational-disk
Horner variation and the computed weighted power envelope retain M_Z as
the main constant and put the enlargement in finite dyadic slack. An
original represented distance cut supplies a genuine stored-point hit;
its index is sealed before deriving the residual of the actual sample
polynomial. No minimizing root, final radius or residual law is supplied.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRootSharpResidualSamples

open_ipra
open LeanProofs.IPRA.Analysis.GaussianCoefficientNameBounds (A R CN unit unit_positive subst_unit)
open LeanProofs.IPRA.Analysis.GaussianFactorParameters (monicRD)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (bounded distanceBounded)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (evaluate positive_product)
open LeanProofs.IPRA.Analysis.GaussianRootRadius (roots)
open LeanProofs.IPRA.Analysis.GaussianEuclideanDistanceName (pointCN distanceLE hit_triangle hit_radius_mono)
open LeanProofs.IPRA.Analysis.GaussianRationalCover (hit)
open LeanProofs.IPRA.Analysis.GaussianRepresentedPointBounds (normLE)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def M (a : PR 3) (N Z x : PTm n) : PTm n := GaussianRationalHornerLipschitz.constant N Z (A a N x)
def c (a : PR 3) (N x : PTm n) : PTm n := GaussianRootSchedule.coefficientConstant N (R a N x)
def D (a : PR 3) (N t x : PTm n) : PTm n := GaussianRootFiniteEvaluation.denominator a N t x
def hitCost (a : PR 3) (N Z x J : PTm n) : PTm n :=
  A a N x*GaussianRationalPowerEnvelope.weightedError Z N*J+c a N x
def hitNumerator (a : PR 3) (N Z t s x p q J : PTm n) : PTm n :=
  M a N Z x*p*D a N t x*unit s+two*c a N x*q*unit s+hitCost a N Z x J*q*D a N t x
def hitDenominator (a : PR 3) (N t s x q : PTm n) : PTm n := q*D a N t x*unit s
def cutCost (a : PR 3) (N Z x r : PTm n) : PTm n :=
  GaussianRootSchedule.four*M a N Z x+A a N x*GaussianRationalPowerEnvelope.weightedError Z N*(r+GaussianRootSchedule.four)+c a N x
def baseNumerator (a : PR 3) (N Z t x r b : PTm n) : PTm n := M a N Z x*r*D a N t x+two*c a N x*b
def baseDenominator (a : PR 3) (N t x b : PTm n) : PTm n := b*D a N t x
def observation (a : PR 3) (point : PR 2) (N x s : PTm n) : PTm n :=
  GaussianPolynomialValueName.observation a point N x s

ipra_subst M
ipra_subst c
ipra_subst D
ipra_subst hitCost
ipra_subst hitNumerator
ipra_subst hitDenominator
ipra_subst cutCost
ipra_subst baseNumerator
ipra_subst baseDenominator
ipra_subst observation

/-- The rational weighted constant keeps M_Z unchanged. A genuine finite
distance cap absorbs its O(1/H) enlargement into computed slack. -/
theorem variation_budget (N Z H C p q J : PTm n)
    (hH : Γ ⊢[PRAAx] le one H) (hCap : Γ ⊢[PRAAx] le p (J*q)) : Γ ⊢[PRAAx]
    le ((C*GaussianRationalPowerEnvelope.weighted (Z*H+one) H N*p)*(q*H))
      ((GaussianRationalHornerLipschitz.constant N Z C*p*H+C*GaussianRationalPowerEnvelope.weightedError Z N*J*q)*(pw H N*q)) := by
  have first := mul_le_mul_right (p*q) (GaussianRationalPowerEnvelope.constant_envelope Z H N C hH)
  have cap := mul_le_mul_right (C*GaussianRationalPowerEnvelope.weightedError Z N*pw H N*q) hCap
  have enlarged := add_le_add_right (GaussianRationalHornerLipschitz.constant N Z C*H*pw H N*p*q) cap
  exact le_trans (le_congr (by ipra_ring) (.eqRefl _) first)
    (le_congr (by ipra_ring) (by ipra_ring) enlarged)

theorem point_residual_bound (step a : PR 3) (N Z t s x z p q J i : PTm n)
    (hRD : Γ ⊢[PRAAx] monicRD step) (hCN : Γ ⊢[PRAAx] CN a N x)
    (hN : Γ ⊢[PRAAx] le one N) (hRZ : Γ ⊢[PRAAx] le (R a N x) Z)
    (hz : Γ ⊢[PRAAx] bounded z (Z*unit s+one) (unit s)) (hq : Γ ⊢[PRAAx] le one q)
    (hCap : Γ ⊢[PRAAx] le p (J*q)) (hi : Γ ⊢[PRAAx] lt i N)
    (hHit : Γ ⊢[PRAAx] distanceBounded z (entry (roots step a N t x) i) p q) : Γ ⊢[PRAAx]
    bounded (evaluate (GaussianRootSamples.sample a N s x) z)
      (hitNumerator a N Z t s x p q J) (hitDenominator a N t s x q) := by
  let H := unit s
  have hp : Γ ⊢[PRAAx] le one H := unit_positive s
  have hqH := positive_product (Γ := Γ) _ _ hq hp
  have hDH := positive_product (Γ := Γ) _ _ (GaussianRootFiniteEvaluation.denominator_positive a N t x) hp
  have rootDisk := GaussianCoefficientNameBounds.bounded_radius_mono _ (R a N x) one (Z*H+one) H
    (le_refl _) hp (le_congr (.eqRefl _) (by ipra_ring)
      (le_trans (mul_le_mul_right H hRZ) (le_add_right _ one)))
    (GaussianRootRadius.root_radius step a N t x i hRD hCN hN hi)
  have actual := GaussianRationalHornerRadiusLipschitz.evaluation_bound (GaussianRootSamples.sample a N s x)
    z (entry (roots step a N t x) i) N (Z*H+one) H (A a N x) p q
    (GaussianRootSamples.sample_length a N s x) (GaussianRootResidualFromHit.sample_coefficients a N s x hCN)
    hp hz rootDisk hq hHit
  have variation := GaussianRationalDistanceOrder.distance_radius_mono _ _ _ _ _ _
    (positive_product _ _ (GaussianFactorBudget.power_positive _ _ hp) hq) hqH
    (variation_budget N Z H (A a N x) p q J hp hCap) actual
  have residual := GaussianRootResidualFromHit.sample_at_listed_root step a N t s x i hRD hCN hN hi
  have combined := GaussianReconstructionRoots.norm_from_distance _ _ _ _ _ _ hqH hDH variation residual
  have targetDen : Γ ⊢[PRAAx] le one (hitDenominator a N t s x q) :=
    positive_product _ _ (positive_product _ _ hq (GaussianRootFiniteEvaluation.denominator_positive a N t x)) hp
  have cross : Γ ⊢[PRAAx] le
      (((GaussianRationalHornerLipschitz.constant N Z (A a N x)*p*H+A a N x*GaussianRationalPowerEnvelope.weightedError Z N*J*q)*
        GaussianRootFiniteEvaluation.coefficientDenominator a N t s x+
        (GaussianRootSchedule.coefficientConstant N (R a N x)*GaussianRootFiniteEvaluation.coefficientNumerator a N t s x)*(q*H))
        *hitDenominator a N t s x q)
      (hitNumerator a N Z t s x p q J*((q*H)*GaussianRootFiniteEvaluation.coefficientDenominator a N t s x)) :=
    le_of_eq_add (d := zero) (by
      unfold hitNumerator hitDenominator hitCost M c D GaussianRootFiniteEvaluation.coefficientDenominator
        GaussianRootFiniteEvaluation.coefficientNumerator
      dsimp [H]
      ipra_ring)
  exact GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _
    (positive_product _ _ hqH hDH) targetDen cross combined

/-- Seal the actual original finite-hit index before returning the bound. -/
theorem residual_from_hit (step a : PR 3) (N Z t s x z p q J : PTm n)
    (hRD : Γ ⊢[PRAAx] monicRD step) (hCN : Γ ⊢[PRAAx] CN a N x)
    (hN : Γ ⊢[PRAAx] le one N) (hRZ : Γ ⊢[PRAAx] le (R a N x) Z)
    (hz : Γ ⊢[PRAAx] bounded z (Z*unit s+one) (unit s)) (hq : Γ ⊢[PRAAx] le one q)
    (hCap : Γ ⊢[PRAAx] le p (J*q))
    (hHit : Γ ⊢[PRAAx] hit z (roots step a N t x) p q) : Γ ⊢[PRAAx]
    bounded (evaluate (GaussianRootSamples.sample a N s x) z)
      (hitNumerator a N Z t s x p q J) (hitDenominator a N t s x q) := by
  refine .exE hHit ?_
  let E : Fm PTm (n+1) := lt (var 0) (length (Syn.shift (roots step a N t x))) ⋏
    distanceBounded (Syn.shift z) (entry (Syn.shift (roots step a N t x)) (var 0)) (Syn.shift p) (Syn.shift q)
  have rd : Γ.map Fm.shift ⊢[PRAAx] monicRD step := by
    simpa only [Fm.shift,GaussianFactorParameters.subst_monicRD] using hRD.shift
  have cn : Γ.map Fm.shift ⊢[PRAAx] CN a (Syn.shift N) (Syn.shift x) := by
    simpa only [Fm.shift,GaussianCoefficientNameBounds.subst_CN,Syn.shift] using hCN.shift
  have hn : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift N) := by
    simpa only [Fm.shift,subst_le,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift] using hN.shift
  have rz : Γ.map Fm.shift ⊢[PRAAx] le (R a (Syn.shift N) (Syn.shift x)) (Syn.shift Z) := by
    simpa only [Fm.shift,subst_le,GaussianCoefficientNameBounds.subst_R,Syn.shift] using hRZ.shift
  have zf : Γ.map Fm.shift ⊢[PRAAx] bounded (Syn.shift z) (Syn.shift Z*unit (Syn.shift s)+one) (unit (Syn.shift s)) := by
    simpa only [Fm.shift,GaussianRationalMetric.subst_bounded,subst_unit,PTm.subst_add,PTm.subst_mul,
      ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift] using hz.shift
  have qf : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift q) := by
    simpa only [Fm.shift,subst_le,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift] using hq.shift
  have cap : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift p) (Syn.shift J*Syn.shift q) := by
    simpa only [Fm.shift,subst_le,PTm.subst_mul,Syn.shift] using hCap.shift
  have inside : E :: Γ.map Fm.shift ⊢[PRAAx] lt (var 0) (Syn.shift N) :=
    lt_congr (.eqRefl _) (GaussianRootRadius.roots_length (Γ := Γ.map Fm.shift) step a (Syn.shift N) (Syn.shift t) (Syn.shift x)).wk
      (by simpa only [E,Syn.shift,GaussianRootRadius.subst_roots] using Prf.andE₁ Prf.hyp0)
  have near : E :: Γ.map Fm.shift ⊢[PRAAx] distanceBounded (Syn.shift z)
      (entry (roots step a (Syn.shift N) (Syn.shift t) (Syn.shift x)) (var 0)) (Syn.shift p) (Syn.shift q) := by
    simpa only [E,Syn.shift,GaussianRootRadius.subst_roots] using Prf.andE₂ Prf.hyp0
  have result := point_residual_bound step a (Syn.shift N) (Syn.shift Z) (Syn.shift t) (Syn.shift s) (Syn.shift x)
    (Syn.shift z) (Syn.shift p) (Syn.shift q) (Syn.shift J) (var 0) rd.wk cn.wk hn.wk rz.wk zf.wk qf.wk cap.wk inside near
  simpa only [E,Fm.shift,GaussianRationalMetric.subst_bounded,GaussianRationalHorner.subst_evaluate,
    GaussianRootSamples.subst_sample,subst_hitNumerator,subst_hitDenominator,Syn.shift] using result

/-- Transfer the represented cut to the actual sample at precision s.
Only the genuine point CN law and 2^s<=2^(s+2) are used. -/
theorem sample_hit_from_cut (step a : PR 3) (point : PR 2) (N t x s r b : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (hPoint : Γ ⊢[PRAAx] pointCN point x)
    (hb : Γ ⊢[PRAAx] le one b)
    (hCut : Γ ⊢[PRAAx] distanceLE point (roots step a N t x) x r b) : Γ ⊢[PRAAx]
    hit (ap2 point s x) (roots step a N t x) (r*unit s+GaussianRootSchedule.four*b) (b*unit s) := by
  let H := unit s
  let K := unit (s+two)
  have hp : Γ ⊢[PRAAx] le one H := unit_positive s
  have kp : Γ ⊢[PRAAx] le one K := unit_positive _
  have bp := positive_product (Γ := Γ) _ _ hb hp
  have hkp := positive_product (Γ := Γ) _ _ hp kp
  have nonempty := le_congr (.eqRefl _) (GaussianRootRadius.roots_length step a N t x).eqSymm hN
  have found := GaussianEuclideanDistanceName.cut_to_hit point (roots step a N t x) x r b s nonempty hb hCut
  have moved := hit_triangle (ap2 point s x) (ap2 point (s+two) x) (roots step a N t x)
    (H+K) (H*K) (r*H+two*b) (b*H) hkp bp
    (GaussianEuclideanDistanceName.point_cn_at point x s (s+two) hPoint) found
  have order : Γ ⊢[PRAAx] le H K := GaussianFactorBudget.power_monotone_length two s (s+two)
    (le_succ_self one) (le_add_right s two)
  have gap := natEq (eq_add_of_le order)
  have cross : Γ ⊢[PRAAx] le
      (((H+K)*(b*H)+(r*H+two*b)*(H*K))*(b*H))
      ((r*H+GaussianRootSchedule.four*b)*((H*K)*(b*H))) := by
    apply le_of_eq_add (d := b*b*H*H*PTm.monus K H)
    apply deriveNat
    unfold GaussianRootSchedule.four
    dsimp [H,K] at gap ⊢
    ipra_simps
    rw [gap]
    ring
  exact hit_radius_mono _ _ _ _ _ _ (positive_product _ _ hkp bp) bp cross moved

theorem cut_hit_cap (r b H : PTm n) (hb : Γ ⊢[PRAAx] le one b) (hH : Γ ⊢[PRAAx] le one H) : Γ ⊢[PRAAx]
    le (r*H+GaussianRootSchedule.four*b) ((r+GaussianRootSchedule.four)*(b*H)) := by
  have first := le_mul_mono hb (le_refl (r*H))
  have second := le_mul_mono (le_refl (GaussianRootSchedule.four*b)) hH
  exact le_congr (by ipra_ring) (by ipra_ring) (add_le_add₂ first second)

/-- The original represented distance cut implies the actual V_s residual
with sharp M_Z and slack independent of the sample precision. -/
theorem residual_from_cut (step a : PR 3) (point : PR 2) (N Z t x s r b : PTm n)
    (hRD : Γ ⊢[PRAAx] monicRD step) (hCN : Γ ⊢[PRAAx] CN a N x)
    (hN : Γ ⊢[PRAAx] le one N) (hRZ : Γ ⊢[PRAAx] le (R a N x) Z)
    (hPoint : Γ ⊢[PRAAx] pointCN point x) (hNorm : Γ ⊢[PRAAx] normLE point Z x)
    (hb : Γ ⊢[PRAAx] le one b)
    (hCut : Γ ⊢[PRAAx] distanceLE point (roots step a N t x) x r b) : Γ ⊢[PRAAx]
    bounded (observation a point N x s)
      (baseNumerator a N Z t x r b*unit s+cutCost a N Z x r*baseDenominator a N t x b)
      (baseDenominator a N t x b*unit s) := by
  have hp := unit_positive (Γ := Γ) s
  have bp := positive_product (Γ := Γ) _ _ hb hp
  have actual := residual_from_hit step a N Z t s x (ap2 point s x)
    (r*unit s+GaussianRootSchedule.four*b) (b*unit s) (r+GaussianRootSchedule.four)
    hRD hCN hN hRZ (GaussianRepresentedPointBounds.norm_le_at point Z x s hNorm) bp
    (cut_hit_cap r b (unit s) hb hp) (sample_hit_from_cut step a point N t x s r b hN hPoint hb hCut)
  have oldDen : Γ ⊢[PRAAx] le one (hitDenominator a N t s x (b*unit s)) :=
    positive_product _ _ (positive_product _ _ bp (GaussianRootFiniteEvaluation.denominator_positive a N t x)) hp
  have den := positive_product (Γ := Γ) _ _ hb (GaussianRootFiniteEvaluation.denominator_positive a N t x)
  have targetDen := positive_product (Γ := Γ) _ _ den hp
  have cross : Γ ⊢[PRAAx] le
      (hitNumerator a N Z t s x (r*unit s+GaussianRootSchedule.four*b) (b*unit s) (r+GaussianRootSchedule.four)*
        (baseDenominator a N t x b*unit s))
      ((baseNumerator a N Z t x r b*unit s+cutCost a N Z x r*baseDenominator a N t x b)*
        hitDenominator a N t s x (b*unit s)) :=
    le_of_eq_add (d := zero) (by unfold hitNumerator hitDenominator hitCost baseNumerator baseDenominator cutCost; ipra_ring)
  exact GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ oldDen targetDen cross actual

def data (N x : PTm n) : PTm n := pairT N x
def body (a : PR 3) (point : PR 2) : PTm 2 := observation a point (fstT (var 1)) (sndT (var 1)) (var 0)
def observationF (a : PR 3) (point : PR 2) : PR 2 := PTm.toPR (body a point)

ipra_subst data

theorem observation_congr (a : PR 3) (point : PR 2) {N N' x x' s s' : PTm n}
    (hN : Γ ⊢[PRAAx] N ≐ N') (hx : Γ ⊢[PRAAx] x ≐ x') (hs : Γ ⊢[PRAAx] s ≐ s') : Γ ⊢[PRAAx]
    observation a point N x s ≐ observation a point N' x' s' := by
  ipra_congr (observation a point (var 0) (var 1) (var 2) : PTm 3) with [hN, hx, hs]

theorem observation_at (a : PR 3) (point : PR 2) (N x s : PTm n) : Γ ⊢[PRAAx]
    ap2 (observationF a point) s (data N x) ≐ observation a point N x s := by
  have base : Γ ⊢[PRAAx] ap2 (observationF a point) s (data N x) ≐
      observation a point (fstT (data N x)) (sndT (data N x)) s := by
    simpa [observationF,body,ap2] using toPR_eq (Γ := Γ) (body a point) ![s,data N x]
  exact base.eqTrans (observation_congr a point (fst_pair _ _) (snd_pair _ _) (.eqRefl _))

/-- The whole envelope is derived from the original distance cut, for the
actual PR2 sampled value stream. No residual envelope is an input. -/
theorem residual_envelope (step a : PR 3) (point : PR 2) (N Z t x r b : PTm n)
    (hRD : Γ ⊢[PRAAx] monicRD step) (hCN : Γ ⊢[PRAAx] CN a N x)
    (hN : Γ ⊢[PRAAx] le one N) (hRZ : Γ ⊢[PRAAx] le (R a N x) Z)
    (hPoint : Γ ⊢[PRAAx] pointCN point x) (hNorm : Γ ⊢[PRAAx] normLE point Z x)
    (hb : Γ ⊢[PRAAx] le one b)
    (hCut : Γ ⊢[PRAAx] distanceLE point (roots step a N t x) x r b) : Γ ⊢[PRAAx]
    GaussianFastValueCut.rawEnvelope (observationF a point) (data N x)
      (baseNumerator a N Z t x r b) (baseDenominator a N t x b) (cutCost a N Z x r) := by
  refine .allI ?_
  have rd : Γ.map Fm.shift ⊢[PRAAx] monicRD step := by
    simpa only [Fm.shift,GaussianFactorParameters.subst_monicRD] using hRD.shift
  have cn : Γ.map Fm.shift ⊢[PRAAx] CN a (Syn.shift N) (Syn.shift x) := by
    simpa only [Fm.shift,GaussianCoefficientNameBounds.subst_CN,Syn.shift] using hCN.shift
  have hn : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift N) := by
    simpa only [Fm.shift,subst_le,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift] using hN.shift
  have rz : Γ.map Fm.shift ⊢[PRAAx] le (R a (Syn.shift N) (Syn.shift x)) (Syn.shift Z) := by
    simpa only [Fm.shift,subst_le,GaussianCoefficientNameBounds.subst_R,Syn.shift] using hRZ.shift
  have pc : Γ.map Fm.shift ⊢[PRAAx] pointCN point (Syn.shift x) := by
    simpa only [Fm.shift,GaussianEuclideanDistanceName.subst_pointCN,Syn.shift] using hPoint.shift
  have norm : Γ.map Fm.shift ⊢[PRAAx] normLE point (Syn.shift Z) (Syn.shift x) := by
    simpa only [Fm.shift,GaussianRepresentedPointBounds.subst_normLE,Syn.shift] using hNorm.shift
  have bpos : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift b) := by
    simpa only [Fm.shift,subst_le,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift] using hb.shift
  have cut : Γ.map Fm.shift ⊢[PRAAx] distanceLE point (roots step a (Syn.shift N) (Syn.shift t) (Syn.shift x)) (Syn.shift x) (Syn.shift r) (Syn.shift b) := by
    simpa only [Fm.shift,GaussianEuclideanDistanceName.subst_distanceLE,GaussianRootRadius.subst_roots,Syn.shift] using hCut.shift
  simpa only [Syn.shift,subst_data,subst_baseNumerator,subst_baseDenominator,subst_cutCost] using
    GaussianRationalReciprocal.bound_congr (observation_at a point (Syn.shift N) (Syn.shift x) (var 0)).eqSymm
      (.eqRefl _) (.eqRefl _)
      (residual_from_cut step a point (Syn.shift N) (Syn.shift Z) (Syn.shift t) (Syn.shift x) (var 0)
        (Syn.shift r) (Syn.shift b) rd cn hn rz pc norm bpos cut)

theorem residual_regular (a : PR 3) (point : PR 2) (N Z x : PTm n)
    (hCN : Γ ⊢[PRAAx] CN a N x) (hPoint : Γ ⊢[PRAAx] pointCN point x)
    (hNorm : Γ ⊢[PRAAx] normLE point Z x) : Γ ⊢[PRAAx]
    GaussianFastValueCut.regular (observationF a point) (GaussianRootApproximationWitness.T a N (Z+one) x) (data N x) := by
  have bounds := GaussianRepresentedPointBounds.uniform_sample_bound point Z x hNorm
  have u : Γ ⊢[PRAAx] le one (Z+one) := le_of_eq_add (d := Z) (by ipra_ring)
  refine .allI (.allI ?_)
  have cn : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] CN a (Syn.shift (Syn.shift N)) (Syn.shift (Syn.shift x)) := by
    simpa only [Fm.shift,GaussianCoefficientNameBounds.subst_CN,Syn.shift] using hCN.shift.shift
  have pc : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] pointCN point (Syn.shift (Syn.shift x)) := by
    simpa only [Fm.shift,GaussianEuclideanDistanceName.subst_pointCN,Syn.shift] using hPoint.shift.shift
  have disk : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx]
      GaussianRootApproximationWitness.pointBounds point (Syn.shift (Syn.shift (Z+one))) (Syn.shift (Syn.shift x)) := by
    simpa only [Fm.shift,GaussianRootApproximationWitness.subst_pointBounds,Syn.shift] using bounds.shift.shift
  have up : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] le one (Syn.shift (Syn.shift (Z+one))) := by
    simpa only [Fm.shift,subst_le,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift] using u.shift.shift
  simpa only [Syn.shift,subst_data,GaussianRootApproximationWitness.subst_T] using
    GaussianRationalDistanceOrder.distance_congr
      (observation_at a point (Syn.shift (Syn.shift N)) (Syn.shift (Syn.shift x)) (var 1)).eqSymm
      (observation_at a point (Syn.shift (Syn.shift N)) (Syn.shift (Syn.shift x)) (var 0)).eqSymm
      (.eqRefl _) (.eqRefl _)
      (GaussianPolynomialValueName.observation_regular_at a point (Syn.shift (Syn.shift N))
        (Syn.shift (Syn.shift (Z+one))) (Syn.shift (Syn.shift x)) (var 1) (var 0) cn pc disk up)

/-- A finite original distance cut gives the exact represented radius cut
of the actual normalized polynomial-value stream. The later joint-order
adapter, rather than this theorem alone, supplies the source D_t(z) RHS. -/
theorem represented_residual_cut (step a : PR 3) (point : PR 2) (N Z t x r b : PTm n)
    (hRD : Γ ⊢[PRAAx] monicRD step) (hCN : Γ ⊢[PRAAx] CN a N x)
    (hN : Γ ⊢[PRAAx] le one N) (hRZ : Γ ⊢[PRAAx] le (R a N x) Z)
    (hPoint : Γ ⊢[PRAAx] pointCN point x) (hNorm : Γ ⊢[PRAAx] normLE point Z x)
    (hb : Γ ⊢[PRAAx] le one b)
    (hCut : Γ ⊢[PRAAx] distanceLE point (roots step a N t x) x r b) : Γ ⊢[PRAAx]
    GaussianFastValueCut.radiusCut (observationF a point) (GaussianRootApproximationWitness.T a N (Z+one) x)
      (data N x) (baseNumerator a N Z t x r b) (baseDenominator a N t x b) :=
  GaussianFastValueCut.envelope_to_cut _ _ _ _ _ _ (residual_regular a point N Z x hCN hPoint hNorm)
    (positive_product _ _ hb (GaussianRootFiniteEvaluation.denominator_positive a N t x))
    (residual_envelope step a point N Z t x r b hRD hCN hN hRZ hPoint hNorm hb hCut)

theorem sharp_variation_budget_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (le one (var 2) ⟶ le (var 4) (var 6*var 5) ⟶
      le ((var 3*GaussianRationalPowerEnvelope.weighted (var 1*var 2+one) (var 2) (var 0)*var 4)*(var 5*var 2))
        ((GaussianRationalHornerLipschitz.constant (var 0) (var 1) (var 3)*var 4*var 2+
          var 3*GaussianRationalPowerEnvelope.weightedError (var 1) (var 0)*var 6*var 5)*(pw (var 2) (var 0)*var 5))) :=
  closeUniv 7 (.impI (.impI (variation_budget _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem sharp_sample_hit_closed (step a : PR 3) (point : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le one (var 0) ⟶ pointCN point (var 2) ⟶ le one (var 5) ⟶
      distanceLE point (roots step a (var 0) (var 1) (var 2)) (var 2) (var 4) (var 5) ⟶
        hit (ap2 point (var 3) (var 2)) (roots step a (var 0) (var 1) (var 2))
          (var 4*unit (var 3)+GaussianRootSchedule.four*var 5) (var 5*unit (var 3))) :=
  closeUniv 6 (.impI (.impI (.impI (.impI
    (sample_hit_from_cut _ _ _ _ _ _ _ _ _ Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))

theorem sharp_residual_envelope_closed (step a : PR 3) (point : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (monicRD step ⟶ CN a (var 0) (var 3) ⟶ le one (var 0) ⟶ le (R a (var 0) (var 3)) (var 1) ⟶
      pointCN point (var 3) ⟶ normLE point (var 1) (var 3) ⟶ le one (var 5) ⟶
        distanceLE point (roots step a (var 0) (var 2) (var 3)) (var 3) (var 4) (var 5) ⟶
          GaussianFastValueCut.rawEnvelope (observationF a point) (data (var 0) (var 3))
            (baseNumerator a (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
            (baseDenominator a (var 0) (var 2) (var 3) (var 5)) (cutCost a (var 0) (var 1) (var 3) (var 4))) := by
  apply closeUniv 6
  refine .impI (.impI (.impI (.impI (.impI (.impI (.impI (.impI ?_)))))))
  exact residual_envelope _ _ _ _ _ _ _ _ _ Prf.hyp0.wk.wk.wk.wk.wk.wk.wk Prf.hyp0.wk.wk.wk.wk.wk.wk
    Prf.hyp0.wk.wk.wk.wk.wk Prf.hyp0.wk.wk.wk.wk Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0

theorem sharp_represented_residual_cut_closed (step a : PR 3) (point : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (monicRD step ⟶ CN a (var 0) (var 3) ⟶ le one (var 0) ⟶ le (R a (var 0) (var 3)) (var 1) ⟶
      pointCN point (var 3) ⟶ normLE point (var 1) (var 3) ⟶ le one (var 5) ⟶
        distanceLE point (roots step a (var 0) (var 2) (var 3)) (var 3) (var 4) (var 5) ⟶
          GaussianFastValueCut.radiusCut (observationF a point) (GaussianRootApproximationWitness.T a (var 0) (var 1+one) (var 3))
            (data (var 0) (var 3)) (baseNumerator a (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
            (baseDenominator a (var 0) (var 2) (var 3) (var 5))) := by
  apply closeUniv 6
  refine .impI (.impI (.impI (.impI (.impI (.impI (.impI (.impI ?_)))))))
  exact represented_residual_cut _ _ _ _ _ _ _ _ _ Prf.hyp0.wk.wk.wk.wk.wk.wk.wk Prf.hyp0.wk.wk.wk.wk.wk.wk
    Prf.hyp0.wk.wk.wk.wk.wk Prf.hyp0.wk.wk.wk.wk Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0

theorem sharp_residual_program_closed (a : PR 3) (point : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (ap2 (observationF a point) (var 2) (data (var 0) (var 1)) ≐ observation a point (var 0) (var 1) (var 2)) :=
  closeUniv 3 (observation_at _ _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianRootSharpResidualSamples
