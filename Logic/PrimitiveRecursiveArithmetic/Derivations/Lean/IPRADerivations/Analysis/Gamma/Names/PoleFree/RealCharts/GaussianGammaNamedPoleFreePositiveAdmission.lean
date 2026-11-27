import IPRADerivations.Analysis.Gamma.Names.PoleFree.Regularity.GaussianGammaNamedPoleFreeProperness
import IPRADerivations.Analysis.Gamma.Names.PositiveAxis.GaussianNamedGammaPositiveLower
import IPRADerivations.Analysis.Optimization.CubeInfimum.RationalCubeInfimumIntervals

/-!
# Positive Gamma admission from a pole-free real observation

The pole inequality at zero bounds a nonnegative real observation
below by the certified pole separation. A sufficiently late observation
then gives a positive margin for the original name at independent clocks.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianGammaNamedPoleFreePositiveAdmission

open_ipra
open LeanProofs.IPRA.Foundations.GapDecision (zabs zabs_congr)
open ComplexLogarithmRemainder (re im normSq oneCode)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_at)
open GaussianGammaEulerHeadLower (poleAt translated translated_zero)
open GaussianNameEquivalence (point_at)
open GaussianNamedPositiveExponentialOrder (realOrder scalar_coordinate_distance)
open GaussianNamedRightHalfPlane (marginPoint threshold numerator denominator)
open GaussianRationalHorner (positive_product ofGaussian_represents)
open GaussianRationalL1 (raw_den_positive raw_represents)
open GaussianL1 (abs_ofNat)
open GaussianSignedNameExponentialOrder (realSamples)
open RationalValueBounds (upper upper_of_radius upper_mono upper_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "poleSource" => GaussianGammaNamedPoleFree.source
local notation "positiveSource" => GaussianNamedGammaPositiveLower.source

def nonnegativeAt (f : PR 2) (k x : PTm n) : Fm PTm n :=
  zle (ZT.ofNat zero) (re (numerator f k x))

theorem axis_pole_gap (z B E j : PTm n) (hi : Γ ⊢[PRAAx] ZT.eq (im (translated z B j)) (ZT.ofNat zero))
    (h : Γ ⊢[PRAAx] poleAt z B one E j) :
    Γ ⊢[PRAAx] le B (E*zabs (re (translated z B j))) := by
  let w := translated z B j
  let a := zabs (re w)
  have hi' : Γ ⊢[PRAAx] zabs (im w) ≐ zero :=
    (zabs_congr (ZT.toZ_eq hi)).eqTrans (abs_ofNat zero)
  have hn : Γ ⊢[PRAAx] normSq w ≐ a*a :=
    (GaussianCoordinateRadius.native_squared w).eqTrans
      ((congrAdd (.eqRefl (a*a)) (congrMul hi' hi')).eqTrans (by ipra_ring))
  have hsq : Γ ⊢[PRAAx] le (B*B) ((E*a)*(E*a)) :=
    le_congr (by ipra_ring) ((congrMul (.eqRefl (E*E)) hn).eqTrans (by ipra_ring)) h
  exact nat_sqrt_mono hsq

theorem nonnegative_gap (a : ZT n) (B E : PTm n) (h : Γ ⊢[PRAAx] zle (ZT.ofNat zero) a)
    (hGap : Γ ⊢[PRAAx] le B (E*zabs a)) :
    Γ ⊢[PRAAx] zle (ZT.ofNat B) (ZT.ofNat E*a) := by
  let w := PolynomialBisection.slack (ZT.ofNat zero) a
  have hw : ZT.toZ Γ a = ZT.toZ Γ (ZT.ofNat w) := by
    have he := zle_toZ h
    simp only [w,PolynomialBisection.slack,ZT.toZ_ofNat] at he ⊢
    ipra_simps
    linear_combination -he
  have habs : Γ ⊢[PRAAx] zabs a ≐ w := (zabs_congr hw).eqTrans (abs_ofNat w)
  have e := natEq (eq_add_of_le (le_congr (.eqRefl _) (congrMul (.eqRefl _) habs) hGap))
  apply zle_of_toZ (monus (E*w) B)
  simp only [ZT.toZ_mul,ZT.toZ_ofNat,hw]
  ipra_simps
  linear_combination -e

theorem snapshot_margin (f : PR 2) (k x R E : PTm n) (h : Γ ⊢[PRAAx] poleSource f x R E)
    (hr : Γ ⊢[PRAAx] realSamples f x) (hs : Γ ⊢[PRAAx] nonnegativeAt f k x) :
    Γ ⊢[PRAAx] zle (ZT.ofNat (denominator f k x)) (ZT.ofNat E*re (numerator f k x)) := by
  let z := numerator f k x
  let B := denominator f k x
  have hPole := GaussianGammaNamedPoleFreeProperness.every_pole_at z R B E zero
    (GaussianGammaNamedPoleFree.source_at f k x R E h)
  have ht := translated_zero (Γ := Γ) z B
  have hi : Γ ⊢[PRAAx] ZT.eq (im (translated z B zero)) (ZT.ofNat zero) :=
    ZT.derive ((GaussianRootAlgebra.equal_im ht).trans (ZT.toZ_eq
      (GaussianNamedGammaPositiveLower.decoded_imaginary_zero f k x hr)))
  have gap := axis_pole_gap z B E zero hi hPole
  have agree : Γ ⊢[PRAAx] zabs (re (translated z B zero)) ≐ zabs (re z) :=
    zabs_congr (GaussianRootAlgebra.equal_re ht)
  exact nonnegative_gap (re z) B E hs (le_congr (.eqRefl _) (congrMul (.eqRefl _) agree) gap)

theorem observation_margin (f : PR 2) (k q x E : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x)
    (hE : Γ ⊢[PRAAx] le one E) (hk : Γ ⊢[PRAAx] le (two*E) (unit k))
    (hY : Γ ⊢[PRAAx] zle (ZT.ofNat (denominator f k x)) (ZT.ofNat E*re (numerator f k x))) :
    Γ ⊢[PRAAx] upper (fstT (marginPoint (two*E))) (fstT (ap2 f q x)) one (unit q) := by
  let W := unit k
  let T := unit q
  let B := denominator f k x
  let C := denominator f q x
  let v := re (numerator f k x)
  let u := re (numerator f q x)
  let A := two*E
  have hW := unit_positive (Γ := Γ) k
  have hT := unit_positive (Γ := Γ) q
  have hB : Γ ⊢[PRAAx] le one B := raw_den_positive _
  have hC : Γ ⊢[PRAAx] le one C := raw_den_positive _
  have hA : Γ ⊢[PRAAx] le one A := positive_product _ _ (by ipra_le 1) hE
  have obs := upper_of_radius _ _ _ _ (scalar_coordinate_distance _ _ _ _
    (positive_product _ _ hW hT) (point_at f x k q hf))
  let left := ZT.ofNat ((W*T)*C)*v
  let right := ZT.ofNat ((W*T)*B)*u+ZT.ofNat ((W+T)*B*C)
  have cleared : Γ ⊢[PRAAx] zle left right :=
    RationalUpperRepresentation.upper_from_representations _ _ B C (W+T) (W*T) v u
      (raw_represents (ap2 f k x)).andE₁ (raw_represents (ap2 f q x)).andE₁ obs
  have e := zle_toZ cleared
  have ey := zle_toZ hY
  have ew : 𝔞 W = 𝔞 A+𝔞 (monus W A) := by
    simpa only [Q.mk_add,map_add] using natEq (eq_add_of_le hk)
  apply RationalCubeInfimumIntervals.upper_of_representations _ _ (re oneCode) u A C one T hA hC
    (ofGaussian_represents oneCode A hA).andE₁ (raw_represents (ap2 f q x)).andE₁
  apply PolynomialBisection.zle_scale_cancel (c := W*B) (positive_product _ _ hW hB)
  apply zle_of_toZ (A*PolynomialBisection.slack left right+
    two*W*T*C*PolynomialBisection.slack (ZT.ofNat B) (ZT.ofNat E*v)+T*B*C*monus W A)
  dsimp only [left,right,PolynomialBisection.slack] at e ⊢
  simp only [ZT.toZ_mul,ZT.toZ_add,ZT.toZ_sub,ZT.toZ_ofNat,GaussianRootAlgebra.re_one] at e ey ⊢
  dsimp only [A] at ew ⊢
  ipra_simps
  linear_combination (2*𝔞 E)*e+2*𝔞 W*𝔞 T*𝔞 C*ey-𝔞 T*𝔞 B*𝔞 C*ew

theorem certificate_at (f : PR 2) (k x E p q : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x)
    (hE : Γ ⊢[PRAAx] le one E) (hk : Γ ⊢[PRAAx] le (two*E) (unit k))
    (hY : Γ ⊢[PRAAx] zle (ZT.ofNat (denominator f k x)) (ZT.ofNat E*re (numerator f k x))) :
    Γ ⊢[PRAAx] upper (fstT (ap2 constantF p (marginPoint (two*E)))) (fstT (ap2 f q x))
      (unit p+unit q) (unit p*unit q) := by
  have small := observation_margin f k q x E hf hE hk hY
  have large := RationalValueBounds.upper_one_error (D := unit p) (unit_positive q) (le_refl _) small
  exact upper_congr (congrFst (constant_at p _)).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) large

theorem positive_source (f : PR 2) (k x R E : PTm n)
    (h : Γ ⊢[PRAAx] poleSource f x R E) (hr : Γ ⊢[PRAAx] realSamples f x)
    (hs : Γ ⊢[PRAAx] nonnegativeAt f k x) (hk : Γ ⊢[PRAAx] le (two*E) (unit k)) :
    Γ ⊢[PRAAx] positiveSource f x (two*E) := by
  have he := (GaussianGammaNamedPoleFree.source_at f k x R E h).andE₂.andE₂.andE₁
  have hy := snapshot_margin f k x R E h hr hs
  refine .andI (.andI h.andE₁ (.andI (positive_product _ _ (by ipra_le 1) he) (.allI (.allI ?_)))) hr
  let Δ := (Γ.map Fm.shift).map Fm.shift
  let sh (t : PTm n) := Syn.shift (Syn.shift t)
  have fs : Δ ⊢[PRAAx] pointCN f (sh x) := by simpa [Δ,sh,Fm.shift,Syn.shift] using h.andE₁.shift.shift
  have es : Δ ⊢[PRAAx] le one (sh E) := by simpa [Δ,sh,Fm.shift,Syn.shift,one] using he.shift.shift
  have ks : Δ ⊢[PRAAx] le (two*sh E) (unit (sh k)) := by
    simpa [Δ,sh,Fm.shift,Syn.shift,one,two] using hk.shift.shift
  have ys : Δ ⊢[PRAAx] zle (ZT.ofNat (denominator f (sh k) (sh x)))
      (ZT.ofNat (sh E)*re (numerator f (sh k) (sh x))) := by
    simpa [Δ,sh,Fm.shift,Syn.shift] using hy.shift.shift
  simpa only [GaussianNamedRightHalfPlane.certificate,realOrder,GaussianNamedRightHalfPlane.subst_marginPoint,
    LeanProofs.IPRA.PTm.subst_mul,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,
    sh,Syn.shift,two,one] using certificate_at f (sh k) (sh x) (sh E) (var 1) (var 0) fs es ks ys

theorem computed_positive_source (f : PR 2) (x R E : PTm n)
    (h : Γ ⊢[PRAAx] poleSource f x R E) (hr : Γ ⊢[PRAAx] realSamples f x)
    (hs : Γ ⊢[PRAAx] nonnegativeAt f (threshold E) x) :
    Γ ⊢[PRAAx] positiveSource f x (two*E) :=
  positive_source f (threshold E) x R E h hr hs (GaussianNamedRightHalfPlane.threshold_budget _ E (le_refl _))

theorem actual_pole_free_real_positive_admission_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((poleSource f (var 0) (var 1) (var 2) ⋏ (realSamples f (var 0) ⋏
      nonnegativeAt f (threshold (var 2)) (var 0))) ⟶ positiveSource f (var 0) (two*var 2)) :=
  closeUniv 3 (.impI (computed_positive_source f _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianGammaNamedPoleFreePositiveAdmission
