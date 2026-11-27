import IPRADerivations.Analysis.Names.RightHalfPlane.GaussianNamedRightHalfPlane
import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.FiniteHeads.GaussianLogGammaEulerHead
import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.Convergence.GaussianLogGammaEulerResidualDomain
import IPRADerivations.Analysis.Exponential.Names.Evaluators.GaussianExponentialReference

/-!
# Signed-rational inputs from the original named right-half-plane sampler

The actual sample's two scalar fractions give a common denominator and
a native Gaussian numerator. A positive real margin gives a positive
real numerator. An absolute value and a bit encode its imaginary part.
The resulting signed chart retains the original disk and margin.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedRightHalfPlaneSigned

open_ipra
open LeanProofs.IPRA.Foundations.GapDecision (zabs subst_zabs)
open ComplexLogarithmRemainder (re im eval_re_code eval_im_code)
open GaussianEulerLowerPowerCoefficients (realLower)
open GaussianFastValueCut (recode recode_canonical recode_represents)
open GaussianLogGammaEulerHead (argument)
open GaussianLogGammaEulerResidualDomain (native)
open GaussianNamedRightHalfPlane (actual_late_source actual_retimed_source precision radius source threshold)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalHorner
  (canonical canonical_unique ofGaussian ofGaussian_canonical ofGaussian_represents represents_congr)
open GaussianRationalL1 (rawGaussian rawDen raw_den_positive)
open GaussianRationalMetric (bounded bounded_of_cleared distanceBounded)
open GaussianRightHalfPlaneLogarithmOffset (signedImag)
open GaussianRootAlgebra (equal equal_of_values normSq_equal)
open PolynomialBisection (selector selector_cases selector_zero)
open RationalArithmetic (select select_zero select_one)
open RationalIntegerNormalization (positivePart negativePart parts_value scaled_parts)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (Q.mk _ t)

def sample (f : PR 2) (x M p : PTm n) : PTm n := ap2 f (precision p M) x
def realNumerator (q : PTm n) : PTm n := positivePart (re (rawGaussian q))
def imagNumerator (q : PTm n) : PTm n := zabs (im (rawGaussian q))
def sign (q : PTm n) : PTm n := selector (im (rawGaussian q))
def denominator (q : PTm n) : PTm n := rawDen q
def point (q : PTm n) : PTm n :=
  argument (realNumerator q) (imagNumerator q) (denominator q) (sign q)

ipra_subst sample

ipra_subst realNumerator

@[simp] theorem subst_imagNumerator {m : ℕ} (σ : Fin n → PTm m) (q : PTm n) :
    Syn.subst σ (imagNumerator q) = imagNumerator (Syn.subst σ q) := by
  simp only [imagNumerator, subst_zabs, ComplexLogarithmRemainder.subst_im, GaussianRationalL1.subst_rawGaussian]

@[simp] theorem subst_sign {m : ℕ} (σ : Fin n → PTm m) (q : PTm n) :
    Syn.subst σ (sign q) = sign (Syn.subst σ q) := by
  change Syn.subst σ (eqb (positivePart (im (rawGaussian q))) zero) =
    eqb (positivePart (im (rawGaussian (Syn.subst σ q)))) zero
  simp only [subst_eqb, RationalIntegerNormalization.subst_positivePart,
    ComplexLogarithmRemainder.subst_im, GaussianRationalL1.subst_rawGaussian, ConciseIPRA.PTm.subst_zero]

@[simp] theorem subst_denominator {m : ℕ} (σ : Fin n → PTm m) (q : PTm n) :
    Syn.subst σ (denominator q) = denominator (Syn.subst σ q) := by simp [denominator]

@[simp] theorem subst_point {m : ℕ} (σ : Fin n → PTm m) (q : PTm n) :
    Syn.subst σ (point q) = point (Syn.subst σ q) := by
  change Syn.subst σ (ofGaussian (native (realNumerator q) (imagNumerator q) (sign q)) (denominator q)) =
    ofGaussian (native (realNumerator (Syn.subst σ q)) (imagNumerator (Syn.subst σ q)) (sign (Syn.subst σ q)))
      (denominator (Syn.subst σ q))
  simp only [GaussianRationalHorner.subst_ofGaussian, GaussianLogGammaEulerResidualDomain.subst_native,
    subst_realNumerator, subst_imagNumerator, subst_sign, subst_denominator]

private theorem imaginary_value (u : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (signedImag (zabs u) (selector u)) u := by
  refine .orE (selector_cases u) ?_ ?_
  · let Δ := (selector u ≐ zero) :: Γ
    have order : Δ ⊢[PRAAx] le (zero + u.neg) (u.pos + zero) := selector_zero Prf.hyp0
    have nz : Δ ⊢[PRAAx] negativePart u ≐ zero :=
      le_congr (zero_add _) (add_zero _) order
    have mag : Δ ⊢[PRAAx] zabs u ≐ positivePart u :=
      (congrAdd (.eqRefl _) nz).eqTrans (add_zero _)
    have left := (select_zero (Γ := Δ) (selector u) (zabs u) zero Prf.hyp0).eqTrans mag
    have right := (select_zero (Γ := Δ) (selector u) zero (zabs u) Prf.hyp0).eqTrans nz.eqSymm
    exact ZT.derive (by
      change 𝔞(select (selector u) (zabs u) zero) - 𝔞(select (selector u) zero (zabs u)) = ZT.toZ Δ u
      rw [natEq left, natEq right]
      exact ZT.toZ_eq (parts_value (Γ := Δ) u))
  · let Δ := (selector u ≐ one) :: Γ
    have pz : Δ ⊢[PRAAx] positivePart u ≐ zero := Foundations.BoundedReflection.eq_of_eqb Prf.hyp0
    have mag : Δ ⊢[PRAAx] zabs u ≐ negativePart u :=
      (congrAdd pz (.eqRefl _)).eqTrans (zero_add _)
    have left := (select_one (Γ := Δ) (selector u) (zabs u) zero Prf.hyp0).eqTrans pz.eqSymm
    have right := (select_one (Γ := Δ) (selector u) zero (zabs u) Prf.hyp0).eqTrans mag
    exact ZT.derive (by
      change 𝔞(select (selector u) (zabs u) zero) - 𝔞(select (selector u) zero (zabs u)) = ZT.toZ Δ u
      rw [natEq left, natEq right]
      exact ZT.toZ_eq (parts_value (Γ := Δ) u))

private theorem real_margin (q K : PTm n)
    (h : Γ ⊢[PRAAx] realLower (rawGaussian q) K (denominator q)) : Γ ⊢[PRAAx]
    le (denominator q) (K * realNumerator q) := by
  let D := denominator q
  let u := re (rawGaussian q)
  let v := ZT.ofNat K * u
  have num : Γ ⊢[PRAAx] le (D + v.neg) v.pos := le_congr (.eqRefl _) (add_zero _) h
  have ord := le_trans (le_add_left v.neg D) num
  have gap : Γ ⊢[PRAAx] v.pos ≐ positivePart v + v.neg :=
    (eq_add_of_le ord).eqTrans (add_comm _ _)
  have lower := le_of_add_le_add_right (le_congr (.eqRefl _) gap num)
  exact le_congr (.eqRefl _) (scaled_parts v u K (.eqRefl _)).andE₁ lower

theorem real_positive (q K : PTm n) (h : Γ ⊢[PRAAx] le (denominator q) (K * realNumerator q)) :
    Γ ⊢[PRAAx] le one (realNumerator q) := by
  have hK := le_trans (raw_den_positive (Γ := Γ) q) h
  refine .orE (zero_or_succ (realNumerator q)) ?_ ?_
  · exact lt_zero_absurd _
      (le_congr (.eqRefl _) ((congrMul (.eqRefl _) Prf.hyp0).eqTrans (mul_zero _)) hK.wk)
  · exact Order.zero_lt_of_eq_succ Prf.hyp0

theorem native_value (q : PTm n) (h : Γ ⊢[PRAAx] le one (realNumerator q)) :
    Γ ⊢[PRAAx] equal (native (realNumerator q) (imagNumerator q) (sign q)) (rawGaussian q) := by
  let u := re (rawGaussian q)
  have hu : Γ ⊢[PRAAx] le u.neg u.pos := by
    refine .orE (le_total u.neg u.pos) Prf.hyp0 ?_
    exact lt_zero_absurd _ (le_congr (.eqRefl _) Prf.hyp0 h.wk)
  apply equal_of_values
  · have e := ZT.toZ_eq (parts_value (Γ := Γ) u)
    change 𝔞(positivePart u) - 𝔞(negativePart u) = ZT.toZ Γ u at e
    rw [natEq (show Γ ⊢[PRAAx] negativePart u ≐ zero from hu)] at e
    simpa [native, realNumerator, u, eval_re_code] using e
  · simpa only [native, imagNumerator, sign, eval_im_code] using
      ZT.toZ_eq (imaginary_value (Γ := Γ) (im (rawGaussian q)))

theorem point_eq_recode (q : PTm n) (h : Γ ⊢[PRAAx] le one (realNumerator q)) :
    Γ ⊢[PRAAx] point q ≐ recode q := by
  let w := native (realNumerator q) (imagNumerator q) (sign q)
  let D := denominator q
  have hD := raw_den_positive (Γ := Γ) q
  exact canonical_unique _ _ _ _ (ofGaussian_canonical w D hD) (recode_canonical q) hD
    (represents_congr (.eqRefl _) (native_value q h) (.eqRefl _) (ofGaussian_represents w D hD))
    (recode_represents q)

theorem point_eq_raw (q : PTm n) (h : Γ ⊢[PRAAx] le one (realNumerator q))
    (hq : Γ ⊢[PRAAx] canonical q) : Γ ⊢[PRAAx] point q ≐ q :=
  (point_eq_recode q h).eqTrans (GaussianExponentialReference.recode_fixed q hq)

theorem point_distance_raw (q : PTm n) (h : Γ ⊢[PRAAx] le one (realNumerator q)) :
    Γ ⊢[PRAAx] distanceBounded (point q) q zero one :=
  distance_congr (point_eq_recode q h).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (GaussianFastValueCut.recode_distance q)

def certificate (q R K : PTm n) : Fm PTm n :=
  GaussianLogGammaEulerResidualDomain.source (realNumerator q) (imagNumerator q) (denominator q) (sign q) R ⋏
    (le (denominator q) (K * realNumerator q) ⋏ (point q ≐ recode q))

@[simp] theorem subst_certificate {m : ℕ} (σ : Fin n → PTm m) (q R K : PTm n) :
    (certificate q R K).subst σ = certificate (Syn.subst σ q) (Syn.subst σ R) (Syn.subst σ K) := by
  simp [certificate]

theorem certify (q R K : PTm n)
    (h : Γ ⊢[PRAAx] GaussianEulerLowerPowerCoefficients.source (rawGaussian q) R (denominator q) K) :
    Γ ⊢[PRAAx] certificate q R K := by
  have margin := real_margin q K h.andE₂.andE₂
  have pos := real_positive q K margin
  have signBit : Γ ⊢[PRAAx] sign q ≐ zero ⋎ sign q ≐ one := selector_cases _
  have disk := le_congr (normSq_equal (native_value q pos)).eqSymm (.eqRefl _) h.andE₂.andE₁.andE₂
  exact .andI (.andI (.andI (.andI pos signBit) h.andE₂.andE₁.andE₁) disk)
    (.andI margin (point_eq_recode q pos))

theorem point_bound (q R K : PTm n) (h : Γ ⊢[PRAAx] certificate q R K) :
    Γ ⊢[PRAAx] bounded (point q) R one := by
  let w := native (realNumerator q) (imagNumerator q) (sign q)
  let D := denominator q
  have hD := raw_den_positive (Γ := Γ) q
  exact bounded_of_cleared (point q) w D R one hD (le_refl one) (ofGaussian_represents w D hD)
    (le_congr (by ipra_ring) (by ipra_ring) h.andE₁.andE₂)

theorem actual_late (f : PR 2) (x M p : PTm n) (h : Γ ⊢[PRAAx] source f x M)
    (hLate : Γ ⊢[PRAAx] le (threshold M) p) :
    Γ ⊢[PRAAx] certificate (ap2 f p x) (radius f x) (two*M) :=
  certify _ _ _ (actual_late_source f x M p h hLate)

theorem actual_retimed (f : PR 2) (x M p : PTm n) (h : Γ ⊢[PRAAx] source f x M) :
    Γ ⊢[PRAAx] certificate (sample f x M p) (radius f x) (two*M) :=
  certify _ _ _ (actual_retimed_source f x M p h)

theorem point_distance (q r E D : PTm n)
    (hq : Γ ⊢[PRAAx] le one (realNumerator q)) (hr : Γ ⊢[PRAAx] le one (realNumerator r))
    (hD : Γ ⊢[PRAAx] le one D) (h : Γ ⊢[PRAAx] distanceBounded q r E D) :
    Γ ⊢[PRAAx] distanceBounded (point q) (point r) E D :=
  distance_congr (point_eq_recode q hq).eqSymm (point_eq_recode r hr).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianFastValueCut.recode_distance_bound q r E D hD h)

theorem actual_named_half_plane_signed_rational_sample_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (source f (var 0) (var 1) ⟶ certificate (sample f (var 0) (var 1) (var 2)) (radius f (var 0)) (two*var 1)) :=
  closeUniv 3 (.impI (actual_retimed f _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianNamedRightHalfPlaneSigned
