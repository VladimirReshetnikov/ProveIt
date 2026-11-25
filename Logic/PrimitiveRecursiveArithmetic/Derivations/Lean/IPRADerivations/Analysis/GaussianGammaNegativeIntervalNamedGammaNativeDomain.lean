import IPRADerivations.Analysis.GaussianGammaNegativeIntervalNative
import IPRADerivations.Analysis.GaussianNamedEulerUnitTime
import IPRADerivations.Analysis.GaussianGammaRadiusOverlap

/-!
# Uniform native Gamma input for a shifted named real offset

A decoded offset in the closed window [1/E,1-1/E] has a verified pole
certificate after translation by -(N+1). The uniform radius is N+2
and the pole margin is 1/E, independent of the decoded denominator.
The primitive-recursive translation reads the original input sample.
-/

set_option autoImplicit false
set_option maxHeartbeats 1400000

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalNamedGammaNativeDomain

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open ComplexLogarithmRemainder (scale oneCode normSq normSq_scale bounded)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaLocalPoleGuards (center localMargin center_Gamma_domain)
open GaussianGammaNegativeCriticalCorrection (guard)
open GaussianGammaNegativeIntervalNative (argument negative_source)
open GaussianGammaReciprocalInverse (gammaF gammaData gamma_regular)
open GaussianNameEquivalence (crossEquivalent point_at)
open GaussianRationalHorner (canonical_unique ofGaussian ofGaussian_represents ofGaussian_canonical
  positive_product represents_congr represents_rescale)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalMetric (distanceBounded qnegative qsub qsub_canonical qsub_represents)
open GaussianRationalNaturalScale (naturalPoint natural_point_represents)
open GaussianRationalSyntheticDivision (qsub_congr)
open GaussianRootAlgebra (equal equal_of_values re_add im_add re_sub im_sub re_neg im_neg re_scale im_scale re_one im_one)
open GaussianStirlingGammaLogarithm (arg)
open GaussianUnitIntervalInputDecoding (numerator denominator fraction_recode)
open GaussianPositiveRationalLogarithm (fraction)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

abbrev window (a b E : PTm n) : Fm PTm n := GaussianEulerUnitCompactTimeBounds.source a b E
abbrev input (f : PR 2) (x E : PTm n) : Fm PTm n := GaussianNamedEulerUnitTime.source f x E

def radius (N : PTm n) : PTm n := succ (succ N)
def encodedNumerator (f : PR 2) (k x N : PTm n) : PTm n :=
  argument (numerator (ap2 f k x)) (denominator (ap2 f k x)) N
def encodedDenominator (f : PR 2) (k x : PTm n) : PTm n := denominator (ap2 f k x)
def frozenData (f : PR 2) (k x E N : PTm n) : PTm n :=
  gammaData (encodedNumerator f k x N) (radius N) (encodedDenominator f k x) E

def shiftSample (f : PR 2) (k x N : PTm n) : PTm n :=
  qsub (GaussianFastValueCut.recode (ap2 f k x)) (naturalPoint (succ N))
def shiftData (x N : PTm n) : PTm n := pairT x N
def shiftF (f : PR 2) : PR 2 := PTm.toPR (shiftSample f (var 0) (fstT (var 1)) (sndT (var 1)))

@[simp] theorem subst_radius {m : ℕ} (σ : Fin n → PTm m) (N : PTm n) :
    Syn.subst σ (radius N) = radius (Syn.subst σ N) := by simp [radius]
@[simp] theorem subst_encodedNumerator {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (k x N : PTm n) :
    Syn.subst σ (encodedNumerator f k x N) = encodedNumerator f (Syn.subst σ k) (Syn.subst σ x) (Syn.subst σ N) := by
  simp [encodedNumerator,argument]
@[simp] theorem subst_encodedDenominator {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (k x : PTm n) :
    Syn.subst σ (encodedDenominator f k x) = encodedDenominator f (Syn.subst σ k) (Syn.subst σ x) := by
  simp [encodedDenominator]
@[simp] theorem subst_frozenData {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (k x E N : PTm n) :
    Syn.subst σ (frozenData f k x E N) = frozenData f (Syn.subst σ k) (Syn.subst σ x) (Syn.subst σ E) (Syn.subst σ N) := by
  simp [frozenData,gammaData,GaussianGammaReciprocalInverse.gammaHeight]
@[simp] theorem subst_shiftSample {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (k x N : PTm n) :
    Syn.subst σ (shiftSample f k x N) = shiftSample f (Syn.subst σ k) (Syn.subst σ x) (Syn.subst σ N) := by
  simp [shiftSample]
@[simp] theorem subst_shiftData {m : ℕ} (σ : Fin n → PTm m) (x N : PTm n) :
    Syn.subst σ (shiftData x N) = shiftData (Syn.subst σ x) (Syn.subst σ N) := by
  simp [shiftData]

theorem uniform_margin (a b E : PTm n) (h : Γ ⊢[PRAAx] window a b E) :
    Γ ⊢[PRAAx] localMargin (arg a) b one (monus E one) E := by
  let S := monus E one
  have hE := h.andE₂.andE₁
  have e := eq_add_of_le hE
  have shift := natEq e
  have upper : Γ ⊢[PRAAx] le (E*a) (S*b) := by
    dsimp only [S]
    ipra_le sl h.andE₂.andE₂.andE₂ with -𝔞 b*shift
  have hn := GaussianGammaGaussReference.scaled_one_norm (Γ := Γ) a
  have scaleNorm : Γ ⊢[PRAAx] normSq (scale E (arg a)) ≐ (E*a)*(E*a) :=
    (normSq_scale E (arg a)).eqTrans ((congrMul (.eqRefl _) hn).eqTrans (by ipra_ring))
  have cap : Γ ⊢[PRAAx] bounded (scale E (arg a)) (S*b) :=
    le_congr scaleNorm.eqSymm (.eqRefl _) (le_mul_mono upper upper)
  have lower := h.andE₂.andE₂.andE₁
  have margin : Γ ⊢[PRAAx] le ((one*b)*(one*b)) (E*E*normSq (arg a)) :=
    le_congr (by ipra_ring) ((show Γ ⊢[PRAAx] (E*a)*(E*a) ≐ E*E*(a*a) by ipra_ring).eqTrans
      (congrMul (.eqRefl _) hn.eqSymm)) (le_mul_mono lower lower)
  exact .andI (le_congr e (.eqRefl _) (le_refl E)) (.andI cap margin)

theorem uniform_source (a b E N : PTm n) (h : Γ ⊢[PRAAx] window a b E) :
    Γ ⊢[PRAAx] GaussianGammaReciprocalInverse.source (argument a b N) (radius N) b one E :=
  center_Gamma_domain (arg a) b one (monus E one) E (succ N)
    (le_trans h.andE₁.andE₁ (le_of_lt h.andE₁.andE₂)) (le_refl one) h.andE₂.andE₁ (uniform_margin a b E h)

theorem frozen_source (f : PR 2) (k x E N : PTm n) (h : Γ ⊢[PRAAx] input f x E) :
    Γ ⊢[PRAAx] GaussianGammaReciprocalInverse.source (encodedNumerator f k x N) (radius N)
      (encodedDenominator f k x) one E :=
  uniform_source _ _ E N (GaussianNamedEulerUnitTime.encoded_source f k x E h)

theorem frozen_regular (f : PR 2) (k x E N : PTm n) (h : Γ ⊢[PRAAx] input f x E) :
    Γ ⊢[PRAAx] pointCN gammaF (frozenData f k x E N) :=
  gamma_regular _ _ _ one E (frozen_source f k x E N h)

theorem uniform_cross (a b E N : PTm n) (h : Γ ⊢[PRAAx] window a b E) :
    Γ ⊢[PRAAx] crossEquivalent gammaF gammaF
      (gammaData (argument a b N) (radius N) b E) (GaussianGammaNegativeIntervalNative.data a b N) :=
  GaussianGammaRadiusOverlap.original_Gamma_overlap (argument a b N) (radius N) (radius N) b one E one b
    (uniform_source a b E N h) (negative_source a b N h.andE₁)

theorem frozen_cross (f : PR 2) (k x E N : PTm n) (h : Γ ⊢[PRAAx] input f x E) :
    Γ ⊢[PRAAx] crossEquivalent gammaF gammaF (frozenData f k x E N)
      (GaussianGammaNegativeIntervalNative.data (numerator (ap2 f k x)) (denominator (ap2 f k x)) N) :=
  uniform_cross _ _ E N (GaussianNamedEulerUnitTime.encoded_source f k x E h)

theorem shift_fraction (a b j : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] qsub (fraction a b) (naturalPoint j) ≐ ofGaussian (center (arg a) b j) b := by
  let z := arg a
  let w := scale (b*j) oneCode
  let u := scale b (scale j oneCode)
  have same : Γ ⊢[PRAAx] equal u w := by
    apply equal_of_values <;>
      simp only [u,w,re_scale,im_scale,re_one,im_one,Q.mk_mul,map_mul] <;> ring
  have rescale := represents_rescale (naturalPoint j) (scale j oneCode) one b
    (natural_point_represents (Γ := Γ) j)
  have right := represents_congr (.eqRefl _) same (one_mul b) rescale
  have diff := qsub_represents (fraction a b) (naturalPoint j) z w b hb (ofGaussian_represents z b hb) right
  have sameCenter : Γ ⊢[PRAAx] equal (GaussianRootAlgebra.sub z w) (center z b j) := by
    apply equal_of_values <;>
      simp only [center,GaussianGammaPoleZeros.poleNumerator,w,re_sub,im_sub,re_add,im_add,re_neg,im_neg] <;> ring
  exact canonical_unique _ _ _ b (qsub_canonical _ _) (ofGaussian_canonical _ _ hb) hb
    (represents_congr (.eqRefl _) sameCenter (.eqRefl _) diff) (ofGaussian_represents _ _ hb)

theorem shift_at (f : PR 2) (k x N : PTm n) : Γ ⊢[PRAAx]
    ap2 (shiftF f) k (shiftData x N) ≐ shiftSample f k x N := by
  let X := shiftData x N
  have raw : Γ ⊢[PRAAx] ap2 (shiftF f) k X ≐ shiftSample f k (fstT X) (sndT X) := by
    simpa only [shiftF,ap2,subst_shiftSample,Syn.subst_var,subst_fstT,subst_sndT,
      Matrix.cons_val_zero,Matrix.cons_val_one] using
      toPR_eq (Γ := Γ) (shiftSample f (var 0) (fstT (var 1)) (sndT (var 1)) : PTm 2) ![k,X]
  have fields := Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (shiftSample f (var 0) (var 1) (var 2) : PTm 3)
    (σ := ![k,fstT X,sndT X]) (σ' := ![k,x,N])
    (fun i => by fin_cases i; exact .eqRefl _; exact fst_pair _ _; exact snd_pair _ _)
  exact raw.eqTrans (by simpa only [subst_shiftSample,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using fields)

theorem frozen_shift_at (f : PR 2) (k x E N : PTm n) (h : Γ ⊢[PRAAx] input f x E) :
    Γ ⊢[PRAAx] ap2 (shiftF f) k (shiftData x N) ≐
      ofGaussian (encodedNumerator f k x N) (encodedDenominator f k x) := by
  let q := ap2 f k x
  have hq := GaussianNamedEulerUnitTime.source_at f k x E h
  have hb := GaussianUnitIntervalInputDecoding.denominator_positive (Γ := Γ) q
  exact (shift_at f k x N).eqTrans
    ((qsub_congr (fraction_recode q E hq).eqSymm (.eqRefl _)).eqTrans
      (shift_fraction (numerator q) (denominator q) (succ N) hb))

theorem shift_observations (f : PR 2) (p q x N : PTm n) (h : Γ ⊢[PRAAx] pointCN f x) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (shiftF f) p (shiftData x N)) (ap2 (shiftF f) q (shiftData x N))
      (unit p+unit q) (unit p*unit q) := by
  have hD := positive_product _ _ (unit_positive (Γ := Γ) p) (unit_positive q)
  have recode := GaussianFastValueCut.recode_distance_bound _ _ _ _ hD (point_at f x p q h)
  exact distance_congr (shift_at f p x N).eqSymm (shift_at f q x N).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianNameRingLaws.sum_left_error _ _ (qnegative (naturalPoint (succ N))) _ _ hD recode)

theorem shift_regular (f : PR 2) (x N : PTm n) (h : Γ ⊢[PRAAx] pointCN f x) :
    Γ ⊢[PRAAx] pointCN (shiftF f) (shiftData x N) := by
  let sh (u : PTm n) := Syn.shift (Syn.shift u)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  have hs : Δ ⊢[PRAAx] pointCN f (sh x) := by simpa [Δ,sh,Fm.shift,Syn.shift] using h.shift.shift
  refine .allI (.allI ?_)
  simpa only [pointCN,GaussianEuclideanPointDistance.unit,GaussianCoefficientNameBounds.unit,
    Δ,sh,Syn.shift,subst_shiftData] using shift_observations f (var 1) (var 0) (sh x) (sh N) hs

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalNamedGammaNativeDomain
