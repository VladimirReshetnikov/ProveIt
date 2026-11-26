import IPRADerivations.Analysis.Gamma.Names.GaussianNamedGammaLateInput

/-!
# Rational observations preserving the exact named real margin and disk

With R=U(f,x)>=2 and U=2^r, replace the decoded observation q by
((U-1)q+R)/U. Both endpoints of this convex combination lie in the
same radius-R disk. The actual named lower margin gives Re(q)>=1/A-1/U;
the correction therefore has real part at least 1/A with A unchanged.
Its distance from the original decoded input is at most 2R/U.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedHalfPlaneCorrection

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianNamedRightHalfPlane (source radius numerator denominator actual_sample_disk actual_sample_upper)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (ofGaussian positive_product)
open GaussianRationalMetric (distanceBounded)
open ComplexLogarithmRemainder (scale oneCode re im normSq)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def weight (r : PTm n) : PTm n := monus (unit r) one
def correctedNumerator (f : PR 2) (r x : PTm n) : PTm n := ComplexLogarithmRemainder.add
  (scale (weight r) (numerator f r x)) (scale (denominator f r x*radius f x) oneCode)
def correctedDenominator (f : PR 2) (r x : PTm n) : PTm n := unit r*denominator f r x
def point (f : PR 2) (r x : PTm n) : PTm n := ofGaussian (correctedNumerator f r x) (correctedDenominator f r x)
@[simp] theorem subst_weight {m : ℕ} (σ : Fin n → PTm m) (r : PTm n) :
    Syn.subst σ (weight r) = weight (Syn.subst σ r) := by simp [weight]
@[simp] theorem subst_correctedNumerator {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (r x : PTm n) :
    Syn.subst σ (correctedNumerator f r x) = correctedNumerator f (Syn.subst σ r) (Syn.subst σ x) := by simp [correctedNumerator]
@[simp] theorem subst_correctedDenominator {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (r x : PTm n) :
    Syn.subst σ (correctedDenominator f r x) = correctedDenominator f (Syn.subst σ r) (Syn.subst σ x) := by simp [correctedDenominator]
@[simp] theorem subst_point {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (r x : PTm n) :
    Syn.subst σ (point f r x) = point f (Syn.subst σ r) (Syn.subst σ x) := by simp [point]

theorem weight_split (r : PTm n) : Γ ⊢[PRAAx] weight r+one ≐ unit r :=
  (add_comm _ _).eqTrans (eq_add_of_le (unit_positive r)).eqSymm


theorem radius_two (f : PR 2) (x : PTm n) : Γ ⊢[PRAAx] le two (radius f x) :=
  le_add_left two (GaussianNameBounds.ceiling f x)

theorem denominator_positive (f : PR 2) (r x : PTm n) : Γ ⊢[PRAAx] le one (correctedDenominator f r x) :=
  positive_product _ _ (unit_positive r) (GaussianRationalL1.raw_den_positive _)

theorem disk (f : PR 2) (r x : PTm n) (hf : Γ ⊢[PRAAx] GaussianEuclideanDistanceName.pointCN f x) : Γ ⊢[PRAAx]
    ComplexLogarithmRemainder.bounded (correctedNumerator f r x) (radius f x*correctedDenominator f r x) := by
  have oneBound : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded (oneCode : PTm n) one :=
    le_congr ComplexLogarithmRemainder.normSq_one.eqSymm (by ipra_ring) (le_refl one)
  have sum := ComplexLogarithmRemainder.bounded_add
    (ComplexLogarithmRemainder.bounded_scale (weight r) (actual_sample_disk f x r hf))
    (ComplexLogarithmRemainder.bounded_scale (denominator f r x*radius f x) oneBound)
  have eq : Γ ⊢[PRAAx] weight r*(radius f x*denominator f r x)+(denominator f r x*radius f x)*one ≐
      radius f x*correctedDenominator f r x := by
    apply deriveNat
    have e := natEq (weight_split (Γ := Γ) r)
    dsimp only [correctedDenominator]
    ipra_simps
    linear_combination (𝔞(radius f x)*𝔞(denominator f r x))*e
  exact le_congr (.eqRefl _) (congrMul eq eq) sum

/-- This is the original scalar named margin cleared against the SAME
raw native observation denominator. -/
theorem margin_clear (f : PR 2) (r x A : PTm n) (h : Γ ⊢[PRAAx] source f x A) : Γ ⊢[PRAAx]
    zle (ZT.ofNat (unit r*denominator f r x))
      (ZT.ofNat (unit r*A)*re (numerator f r x)+ZT.ofNat (A*denominator f r x)) := by
  have clear := RationalUpperRepresentation.upper_from_representations _ _ A (denominator f r x) one (unit r)
    (re oneCode) (re (numerator f r x))
    (GaussianRationalHorner.ofGaussian_represents oneCode A h.andE₂.andE₁).andE₁
    (GaussianRationalL1.raw_represents (ap2 f r x)).andE₁ (actual_sample_upper f x A r h.andE₂.andE₂)
  exact PolynomialBisection.zle_congr (by simp only [ZT.toZ_mul,ZT.toZ_ofNat,GaussianRootAlgebra.re_one]; ring)
    (by simp only [ZT.toZ_add,ZT.toZ_mul,ZT.toZ_ofNat]; ipra_simps; ring) clear

theorem exact_margin (f : PR 2) (r x A : PTm n) (h : Γ ⊢[PRAAx] source f x A) : Γ ⊢[PRAAx]
    GaussianEulerLowerPowerCoefficients.realLower (correctedNumerator f r x) A (correctedDenominator f r x) := by
  let U := unit r
  let V := weight r
  let B := denominator f r x
  let R := radius f x
  let z := numerator f r x
  let lo := ZT.ofNat (U*B)
  let hi := ZT.ofNat (U*A)*re z+ZT.ofNat (A*B)
  let g := PolynomialBisection.slack lo hi
  have old : Γ ⊢[PRAAx] zle lo hi := margin_clear f r x A h
  have em := zle_toZ old
  have hAR : Γ ⊢[PRAAx] le (A+one) (A*R) := by
    have a : Γ ⊢[PRAAx] le (A+one) (two*A) := le_congr (by ipra_ring) (by ipra_ring) (add_le_add_right A h.andE₂.andE₁)
    have b : Γ ⊢[PRAAx] le (two*A) (A*R) := le_congr (.eqRefl _) (mul_comm _ _) (mul_le_mul_right A (radius_two f x))
    exact le_trans a b
  let G := monus (A*R) (A+one)
  have eg := natEq (eq_add_of_le hAR)
  have ev := natEq (weight_split (Γ := Γ) r)
  apply PolynomialBisection.zle_scale_cancel (c := U) (unit_positive r)
  apply zle_of_toZ (V*g+B*(A+U*G))
  dsimp only [lo,hi] at em
  simp only [correctedNumerator,correctedDenominator,
    GaussianRootAlgebra.re_add,GaussianRootAlgebra.re_scale,GaussianRootAlgebra.re_one,
    ZT.toZ_mul,ZT.toZ_add,ZT.toZ_ofNat] at em ⊢
  dsimp only [U,V,B,R,z,g,G,PolynomialBisection.slack,lo,hi] at em eg ev ⊢
  ipra_simps
  linear_combination (𝔞(weight r))*em-(𝔞(unit r)*𝔞(denominator f r x))*eg-
    (𝔞(denominator f r x)*(𝔞(unit r)-𝔞 A))*ev

theorem original_source (f : PR 2) (r x A : PTm n) (h : Γ ⊢[PRAAx] source f x A) : Γ ⊢[PRAAx]
    GaussianEulerLowerPowerCoefficients.source (correctedNumerator f r x) (radius f x) (correctedDenominator f r x) A :=
  .andI h.andE₂.andE₁ (.andI (.andI (denominator_positive f r x) (disk f r x h.andE₁)) (exact_margin f r x A h))

theorem point_distance (f : PR 2) (r x : PTm n)
    (hf : Γ ⊢[PRAAx] GaussianEuclideanDistanceName.pointCN f x) : Γ ⊢[PRAAx]
    distanceBounded (point f r x) (ofGaussian (numerator f r x) (denominator f r x))
      (two*radius f x) (unit r) := by
  let z := numerator f r x
  let B := denominator f r x
  let R := radius f x
  let U := unit r
  let a := correctedNumerator f r x
  let E := correctedDenominator f r x
  have identity : Γ ⊢[PRAAx] GaussianRootAlgebra.equal (GaussianRootAlgebra.sub a (scale U z))
      (GaussianRootAlgebra.sub (scale (B*R) oneCode) z) := by
    have e := natEq (weight_split (Γ := Γ) r)
    apply GaussianRootAlgebra.equal_of_values <;>
      simp only [a,correctedNumerator,GaussianRootAlgebra.re_sub,GaussianRootAlgebra.im_sub,
        GaussianRootAlgebra.re_add,GaussianRootAlgebra.im_add,
        GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale]
    · dsimp only [B,R,U,z]; ipra_simps
      linear_combination (ZT.toZ Γ (re (numerator f r x)))*e
    · dsimp only [B,R,U,z]; ipra_simps
      linear_combination (ZT.toZ Γ (im (numerator f r x)))*e
  have oneBound : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded (oneCode : PTm n) one :=
    le_congr ComplexLogarithmRemainder.normSq_one.eqSymm (by ipra_ring) (le_refl one)
  have sum := ComplexLogarithmRemainder.bounded_add
    (ComplexLogarithmRemainder.bounded_scale (B*R) oneBound)
    (ComplexLogarithmRemainder.bounded_neg (actual_sample_disk f x r hf))
  have native : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded (GaussianRootAlgebra.sub a (scale U z)) (two*R*B) :=
    le_congr (GaussianRootAlgebra.normSq_equal identity).eqSymm (by dsimp only [B,R]; ipra_ring) sum
  have hB : Γ ⊢[PRAAx] le one B := GaussianRationalL1.raw_den_positive _
  have old := GaussianRationalSyntheticDivision.rescale_to (ofGaussian z B) z B U E
    (GaussianRationalHorner.ofGaussian_represents z B hB) (by dsimp only [E,correctedDenominator,B,U]; ipra_ring)
  apply (GaussianRationalMetric.bounded_difference_iff _ _ a (scale U z) E (two*R) U
    (denominator_positive f r x) (unit_positive r)
    (GaussianRationalHorner.ofGaussian_represents a E (denominator_positive f r x)) old).iffMpr
  have scaled : Γ ⊢[PRAAx] le ((U*U)*normSq (GaussianRootAlgebra.sub a (scale U z)))
      ((U*U)*((two*R*B)*(two*R*B))) :=
    le_congr (mul_comm _ _) (mul_comm _ _) (mul_le_mul_right (U*U) native)
  exact le_congr (.eqRefl _) (by dsimp only [E,correctedDenominator,B,U,R]; ipra_ring) scaled

theorem corrected_original_source_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (source f (var 1) (var 2) ⟶ GaussianEulerLowerPowerCoefficients.source
      (correctedNumerator f (var 0) (var 1)) (radius f (var 1))
      (correctedDenominator f (var 0) (var 1)) (var 2)) :=
  closeUniv 3 (.impI (original_source f _ _ _ Prf.hyp0))

theorem corrected_observation_distance_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (GaussianEuclideanDistanceName.pointCN f (var 1) ⟶
      distanceBounded (point f (var 0) (var 1)) (ofGaussian (numerator f (var 0) (var 1)) (denominator f (var 0) (var 1)))
        (two*radius f (var 1)) (unit (var 0))) :=
  closeUniv 2 (.impI (point_distance f _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianNamedHalfPlaneCorrection
