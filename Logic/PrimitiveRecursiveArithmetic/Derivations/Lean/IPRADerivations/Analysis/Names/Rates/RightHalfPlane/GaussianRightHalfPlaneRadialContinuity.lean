import IPRADerivations.Analysis.Logarithm.RightHalfPlane.GaussianRightHalfPlaneRadialLogarithm
import IPRADerivations.Analysis.Gamma.FunctionalEquations.Multiplication.PowerEstimates.GaussianGaussMultiplicationLogarithm
import IPRADerivations.Analysis.Names.Rates.GaussianNamedLipschitzRate
import IPRADerivations.Analysis.RationalArithmetic.Complex.GaussianCoordinateRadius
import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.Convergence.GaussianLogGammaEulerResidualRadius

/-!
# Quantitative radial continuity in the right half-plane

For two rational inputs with the same positive denominator, the
common denominator cancels from the scalar logarithm comparison.
The difference of the squared numerator norms is controlled by the
native displacement and the two coordinate sums. The actual radial
name inherits the estimate at independent observation clocks.
-/

set_option autoImplicit false
set_option maxHeartbeats 650000

namespace LeanProofs.IPRA.Analysis.GaussianRightHalfPlaneRadialContinuity

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.Foundations.GapDecision (zabs zabs_congr zabs_tri)
open LeanProofs.IPRA.Probability.Variance (ad)
open ComplexLogarithmRemainder (re im normSq normSq_eval eval_re_code eval_im_code)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianL1 (abs_multiply abs_ofNat)
open GaussianLogGammaEulerResidualDomain (native)
open GaussianNameArithmetic (sum_distance multiplyModulus)
open GaussianNameRingLaws (add_sample_error multiply_sample_error three)
open GaussianNamedInverseRate (rateNumerator rateDenominator)
open GaussianNamedLipschitzRate (diagonalEnvelope diagonalNumerator diagonalDenominator)
open GaussianPositiveRationalLogarithm (baseF negativeF logF)
open GaussianRationalHorner (qadd qmul positive_product)
open GaussianRationalMetric (bounded distanceBounded qsub)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalReciprocal (bound_congr bounded_product)
open GaussianRightHalfPlaneRadialLogarithm (normNum normDen)
open GaussianRootAlgebra (equal equal_of_values normSq_equal sub re_sub im_sub)
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (monus num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "R" => GaussianRightHalfPlaneRadialLogarithm.nameF
local notation "rdata" => GaussianRightHalfPlaneRadialLogarithm.data
local notation "L" => GaussianPositiveRationalLogarithm.data
local notation "half" => GaussianEulerSquareFactorInverse.half
local notation "source" => GaussianRightHalfPlaneLogarithm.source

def budget (A B a b H : PTm n) : PTm n := H*(A+B+a+b)

def admission (A B neg a b sign D H M : PTm n) : Fm PTm n :=
  source A D neg ⋏ (source a D sign ⋏
    (ComplexLogarithmRemainder.bounded (sub (native a b sign) (native A B neg)) H ⋏
      (le one M ⋏ (le M (normNum A B) ⋏ le M (normNum a b)))))

def shiftedLower (M H D i : PTm n) : PTm n := M+num 32*H*(i*D)

@[simp] theorem subst_budget {m : ℕ} (σ : Fin n → PTm m) (A B a b H : PTm n) :
    Syn.subst σ (budget A B a b H) = budget (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ H) := by
  simp [budget]

@[simp] theorem subst_admission {m : ℕ} (σ : Fin n → PTm m) (A B neg a b sign D H M : PTm n) :
    (admission A B neg a b sign D H M).subst σ =
      admission (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ neg) (Syn.subst σ a) (Syn.subst σ b)
        (Syn.subst σ sign) (Syn.subst σ D) (Syn.subst σ H) (Syn.subst σ M) := by
  simp [admission,GaussianRightHalfPlaneLogarithm.source,GaussianRightHalfPlaneArgument.source,normNum]

@[simp] theorem subst_shiftedLower {m : ℕ} (σ : Fin n → PTm m) (M H D i : PTm n) :
    Syn.subst σ (shiftedLower M H D i) = shiftedLower (Syn.subst σ M) (Syn.subst σ H) (Syn.subst σ D) (Syn.subst σ i) :=
  by simp [shiftedLower]

/-- Adding the same row offset to the two real numerators leaves their
native displacement exactly equal, including the original sign bits. -/
theorem shifted_displacement (i A B neg a b sign D : PTm n) :
    Γ ⊢[PRAAx] equal (sub (native (a+i*D) b sign) (native (A+i*D) B neg))
      (sub (native a b sign) (native A B neg)) := by
  apply equal_of_values
  · simp only [re_sub,GaussianLogGammaEulerResidualDomain.native,eval_re_code,ZT.toZ_ofNat]
    ipra_simps
    ring
  · simp only [im_sub,GaussianLogGammaEulerResidualDomain.native,eval_im_code]

private theorem shifted_norm_lower (A B M H D i : PTm n)
    (hM : Γ ⊢[PRAAx] le M (normNum A B)) (hH : Γ ⊢[PRAAx] le (num 16*H) A) :
    Γ ⊢[PRAAx] le (shiftedLower M H D i) (normNum (A+i*D) B) := by
  unfold shiftedLower normNum at *
  ipra_le sl hM + 2*𝔞(i*D)*sl hH + 𝔞((i*D)*(i*D))

theorem shifted_admission (i A B neg a b sign D H M : PTm n)
    (h : Γ ⊢[PRAAx] admission A B neg a b sign D H M)
    (hA : Γ ⊢[PRAAx] le (num 16*H) A) (ha : Γ ⊢[PRAAx] le (num 16*H) a) :
    Γ ⊢[PRAAx] admission (A+i*D) B neg (a+i*D) b sign D H (shiftedLower M H D i) := by
  have h₁ := GaussianLogGammaEulerHead.shifted_source i A D neg h.andE₁
  have h₂ := GaussianLogGammaEulerHead.shifted_source i a D sign h.andE₂.andE₁
  have displaced := le_congr (normSq_equal (shifted_displacement i A B neg a b sign D)).eqSymm
    (.eqRefl _) h.andE₂.andE₂.andE₁
  have base := h.andE₂.andE₂.andE₂
  have lower := le_trans base.andE₁ (le_add_right M (num 32*H*(i*D)))
  exact .andI h₁ (.andI h₂ (.andI displaced (.andI lower (.andI
    (shifted_norm_lower A B M H D i base.andE₂.andE₁ hA)
    (shifted_norm_lower a b M H D i base.andE₂.andE₂ ha)))))

theorem shifted_smallness (i A B a b D H M : PTm n)
    (hsmall : Γ ⊢[PRAAx] le (num 16*budget A B a b H) M) :
    Γ ⊢[PRAAx] le (num 16*budget (A+i*D) B (a+i*D) b H) (shiftedLower M H D i) :=
  le_congr (by unfold budget; ipra_ring) (.eqRefl _) (add_le_add_right (num 32*H*(i*D)) hsmall)

private theorem native_magnitudes (A B neg : PTm n)
    (hn : Γ ⊢[PRAAx] (neg ≐ zero) ⋎ (neg ≐ one)) :
    Γ ⊢[PRAAx] (zabs (re (native A B neg)) ≐ A) ⋏ (zabs (im (native A B neg)) ≐ B) := by
  let w := native A B neg
  have hRe : Γ ⊢[PRAAx] zabs (re w) ≐ A :=
    (zabs_congr (v := ZT.ofNat A) (by simp only [w,GaussianLogGammaEulerResidualDomain.native,eval_re_code])).eqTrans (abs_ofNat _)
  have hNorm := natEq (GaussianLogGammaEulerResidualRadius.native_norm A B neg hn)
  have hDecomp := natEq (GaussianCoordinateRadius.native_squared (Γ := Γ) w)
  have eRe := natEq hRe
  have eIm : Γ ⊢[PRAAx] zabs (im w)*zabs (im w) ≐ B*B := by
    apply deriveNat
    ipra_simps
    rw [eRe] at hDecomp
    linear_combination hNorm-hDecomp
  exact .andI hRe (le_antisymm
    (nat_sqrt_mono (le_congr (.eqRefl _) eIm (le_refl _)))
    (nat_sqrt_mono (le_congr (.eqRefl _) eIm.eqSymm (le_refl _))))

theorem squared_gap (A B neg a b sign H : PTm n)
    (hn : Γ ⊢[PRAAx] (neg ≐ zero) ⋎ (neg ≐ one))
    (hs : Γ ⊢[PRAAx] (sign ≐ zero) ⋎ (sign ≐ one))
    (h : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded (sub (native a b sign) (native A B neg)) H) :
    Γ ⊢[PRAAx] le (ad (normNum a b) (normNum A B)) (budget A B a b H) := by
  let u := native A B neg
  let v := native a b sign
  let w := sub v u
  let dr := re w
  let di := im w
  let sr := re v+re u
  let si := im v+im u
  let t := ZT.ofNat (normNum a b)-ZT.ofNat (normNum A B)
  have hm := native_magnitudes A B neg hn
  have hk := native_magnitudes a b sign hs
  have component : Γ ⊢[PRAAx] le (zabs dr) H ⋏ le (zabs di) H := by
    have raw := GaussianCoordinateRadius.native_coordinates w H one one (le_congr (by ipra_ring) (by ipra_ring) h)
    exact .andI (le_congr (one_mul _) (by ipra_ring) raw.andE₁) (le_congr (one_mul _) (by ipra_ring) raw.andE₂)
  have realSum : Γ ⊢[PRAAx] le (zabs sr) (a+A) :=
    le_congr (.eqRefl _) (congrAdd hk.andE₁ hm.andE₁)
      (zabs_tri (u := re v) (v := re u) (w := sr) (ZT.toZ_add _ _))
  have imagSum : Γ ⊢[PRAAx] le (zabs si) (b+B) :=
    le_congr (.eqRefl _) (congrAdd hk.andE₂ hm.andE₂)
      (zabs_tri (u := im v) (v := im u) (w := si) (ZT.toZ_add _ _))
  have normU : 𝔞(normSq u) = 𝔞(normNum A B) := natEq (GaussianLogGammaEulerResidualRadius.native_norm A B neg hn)
  have normV : 𝔞(normSq v) = 𝔞(normNum a b) := natEq (GaussianLogGammaEulerResidualRadius.native_norm a b sign hs)
  have split : ZT.toZ Γ t = ZT.toZ Γ (dr*sr)+ZT.toZ Γ (di*si) := by
    simp only [t,dr,di,sr,si,w,ZT.toZ_sub,ZT.toZ_ofNat,ZT.toZ_mul,ZT.toZ_add,re_sub,im_sub]
    rw [← normV,← normU,normSq_eval,normSq_eval]
    ring
  have gap : Γ ⊢[PRAAx] zabs t ≐ ad (normNum a b) (normNum A B) := by
    apply zabs_congr (v := ⟨normNum a b,normNum A B⟩)
    rw [show t = ZT.ofNat (normNum a b)-ZT.ofNat (normNum A B) from rfl,ZT.toZ_sub,ZT.toZ_ofNat,ZT.toZ_ofNat]
    rfl
  have rr := le_mul_mono component.andE₁ realSum
  have ii := le_mul_mono component.andE₂ imagSum
  have absZT := zabs_tri split
  exact le_congr gap (by unfold budget; ipra_ring)
    (le_trans (le_congr (.eqRefl _) (congrAdd (abs_multiply dr sr) (abs_multiply di si)) absZT)
      (add_le_add₂ rr ii))

private theorem integer_gap (p X Y K M : PTm n) (hM : Γ ⊢[PRAAx] le one M)
    (hx : Γ ⊢[PRAAx] le M X) (hy : Γ ⊢[PRAAx] le M Y) (h : Γ ⊢[PRAAx] le (ad Y X) K) :
    Γ ⊢[PRAAx] distanceBounded (ap2 baseF p Y) (ap2 baseF p X) K M := by
  refine (le_total X Y).orE ?_ ?_
  · have bound : (le X Y) :: Γ ⊢[PRAAx] le (monus Y X) K :=
      le_trans (le_add_right (monus Y X) (monus X Y)) h.wk
    have rate : (le X Y) :: Γ ⊢[PRAAx] le (M*monus Y X) (K*X) :=
      le_congr (.eqRefl _) (mul_comm _ _)
        (le_trans (le_mul_mono (le_refl M) bound) (mul_le_mul_right K hx.wk))
    exact GaussianGaussMultiplicationLogarithm.integer_log_distance_at X Y p K M
      (le_trans hM.wk hx.wk) Prf.hyp0 hM.wk rate
  · have bound : (le Y X) :: Γ ⊢[PRAAx] le (monus X Y) K :=
      le_trans (le_add_left (monus X Y) (monus Y X)) h.wk
    have rate : (le Y X) :: Γ ⊢[PRAAx] le (M*monus X Y) (K*Y) :=
      le_congr (.eqRefl _) (mul_comm _ _)
        (le_trans (le_mul_mono (le_refl M) bound) (mul_le_mul_right K hy.wk))
    exact distance_symmetric _ _ _ _ hM.wk (GaussianGaussMultiplicationLogarithm.integer_log_distance_at Y X p K M
      (le_trans hM.wk hy.wk) Prf.hyp0 hM.wk rate)

private theorem dyadic_into (x y C M p : PTm n) (hM : Γ ⊢[PRAAx] le one M)
    (h : Γ ⊢[PRAAx] distanceBounded x y C (unit p)) :
    Γ ⊢[PRAAx] distanceBounded x y (C*M) (M*unit p) :=
  distance_radius_mono _ _ _ _ _ _ (unit_positive p) (positive_product _ _ hM (unit_positive p))
    (le_of_eq_add (d := zero) (by ipra_ring)) h

private theorem log_diagonal (p X Y E K M : PTm n)
    (hM : Γ ⊢[PRAAx] le one M) (hE : Γ ⊢[PRAAx] le one E)
    (hx : Γ ⊢[PRAAx] le M X) (hy : Γ ⊢[PRAAx] le M Y) (h : Γ ⊢[PRAAx] le (ad Y X) K) :
    Γ ⊢[PRAAx] distanceBounded (ap2 logF p (L Y E)) (ap2 logF p (L X E))
      (K*unit p+num 6*M) (M*unit p) := by
  let x := ap2 baseF p X
  let y := ap2 baseF p Y
  let c := GaussianGammaEulerShift.negativeLogData E
  let z := ap2 negativeF p c
  let r := ap2 logF p (L Y E)
  let s := ap2 logF p (L X E)
  let U := unit p
  have hu := unit_positive (Γ := Γ) p
  have hD := positive_product _ _ hM hu
  have hn := GaussianGammaEulerShift.negative_log_regular E hE
  have hxN := GaussianGammaFiniteApproximantName.log_regular X (le_trans hM hx)
  have hyN := GaussianGammaFiniteApproximantName.log_regular Y (le_trans hM hy)
  have left := add_sample_error baseF negativeF Y c p hyN hn
  have right := add_sample_error baseF negativeF X c p hxN hn
  have mid := sum_distance y x z z K zero M hM (integer_gap p X Y K M hM hx hy h)
    (GaussianRationalPowerDifference.distance_refl_zero z M hM)
  have aligned := distance_radius_mono (qadd y z) (qadd x z) (K+zero) M (K*U) (M*U)
    hM hD (le_of_eq_add (d := zero) (by ipra_ring)) mid
  have first := distance_triangle_same r (qadd y z) (qadd x z) (three*M) (K*U) (M*U) hD
    (dyadic_into _ _ _ M p hM left) aligned
  have last := dyadic_into _ _ _ M p hM (distance_symmetric _ _ _ _ hu right)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold three; ipra_ring) (.eqRefl _)
    (distance_triangle_same r (qadd x z) s _ (three*M) (M*U) hD first last)

private def errorCost (A B a b D : PTm n) : PTm n :=
  let x := L (normNum A B) (normDen D)
  let y := L (normNum a b) (normDen D)
  (multiplyModulus constantF logF half y+one)+(multiplyModulus constantF logF half x+one)+num 6

@[simp] private theorem subst_errorCost {m : ℕ} (σ : Fin n → PTm m) (A B a b D : PTm n) :
    Syn.subst σ (errorCost A B a b D) =
      errorCost (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ D) := by
  simp [errorCost,normNum,normDen,GaussianEulerSquareFactorInverse.half,GaussianPositiveRationalLogarithm.fraction,one,two]

private theorem diagonal (p A B neg a b sign D H M : PTm n)
    (h : Γ ⊢[PRAAx] admission A B neg a b sign D H M) :
    Γ ⊢[PRAAx] distanceBounded (ap2 R p (rdata a b D)) (ap2 R p (rdata A B D))
      (diagonalNumerator (budget A B a b H) M (errorCost A B a b D) p) (diagonalDenominator M p) := by
  let X := normNum A B
  let Y := normNum a b
  let E := normDen D
  let x := L X E
  let y := L Y E
  let u := ap2 logF p x
  let v := ap2 logF p y
  let first := ap2 R p (rdata a b D)
  let last := ap2 R p (rdata A B D)
  let C := multiplyModulus constantF logF half y+one
  let F := multiplyModulus constantF logF half x+one
  let K := budget A B a b H
  let U := unit p
  have h₁ : Γ ⊢[PRAAx] source A D neg := h.andE₁
  have h₂ : Γ ⊢[PRAAx] source a D sign := h.andE₂.andE₁
  have hM : Γ ⊢[PRAAx] le one M := h.andE₂.andE₂.andE₂.andE₁
  have hX : Γ ⊢[PRAAx] le M X := h.andE₂.andE₂.andE₂.andE₂.andE₁
  have hY : Γ ⊢[PRAAx] le M Y := h.andE₂.andE₂.andE₂.andE₂.andE₂
  have hE := positive_product D D h₁.andE₂ h₁.andE₂
  have hGap := squared_gap A B neg a b sign H h₁.andE₁.andE₂ h₂.andE₁.andE₂ h.andE₂.andE₂.andE₁
  have hSmall := log_diagonal p X Y E K M hM hE hX hY hGap
  have hHalf : Γ ⊢[PRAAx] bounded half one one :=
    GaussianEulerExponentCompactBounds.fraction_bound one two one (zero_lt_succ one)
      (le_of_eq_add (d := one) (by ipra_ring))
  have hu := unit_positive (Γ := Γ) p
  have hD := positive_product _ _ hM hu
  have mid : Γ ⊢[PRAAx] distanceBounded (qmul half v) (qmul half u) (K*U+num 6*M) (M*U) :=
    bound_congr (GaussianRationalRoundedPower.multiplication_difference half v u).eqSymm (one_mul _) (one_mul _)
      (bounded_product half (qsub v u) one one _ _ (le_refl _) hD hHalf hSmall)
  have hx := GaussianPositiveRationalLogarithm.name_regular X E (.andI (le_trans hM hX) hE)
  have hy := GaussianPositiveRationalLogarithm.name_regular Y E (.andI (le_trans hM hY) hE)
  have left : Γ ⊢[PRAAx] distanceBounded first (qmul half v) C U :=
    distance_congr (.eqRefl _) (GaussianRationalSyntheticDivision.qmul_congr (constant_at p half) (.eqRefl _))
      (.eqRefl _) (.eqRefl _) (multiply_sample_error constantF logF half y p (constant_regular _) hy)
  have right : Γ ⊢[PRAAx] distanceBounded last (qmul half u) F U :=
    distance_congr (.eqRefl _) (GaussianRationalSyntheticDivision.qmul_congr (constant_at p half) (.eqRefl _))
      (.eqRefl _) (.eqRefl _) (multiply_sample_error constantF logF half x p (constant_regular _) hx)
  have pair := distance_triangle_same first (qmul half v) (qmul half u) (C*M) (K*U+num 6*M) (M*U) hD
    (dyadic_into _ _ _ M p hM left) mid
  have joined := distance_triangle_same first (qmul half u) last _ (F*M) (M*U) hD pair
    (dyadic_into _ _ _ M p hM (distance_symmetric _ _ _ _ hu right))
  exact distance_congr (.eqRefl _) (.eqRefl _)
    (by dsimp only [diagonalNumerator,errorCost,C,F,K,U,x,y,X,Y,E]; ipra_ring) (.eqRefl _) joined

theorem radial_distance (p q A B neg a b sign D H M : PTm n)
    (h : Γ ⊢[PRAAx] admission A B neg a b sign D H M) :
    Γ ⊢[PRAAx] distanceBounded (ap2 R p (rdata a b D)) (ap2 R q (rdata A B D))
      (rateNumerator (budget A B a b H) M p q) (rateDenominator M p q) := by
  have h₁ : Γ ⊢[PRAAx] source A D neg := h.andE₁
  have h₂ : Γ ⊢[PRAAx] source a D sign := h.andE₂.andE₁
  have hM : Γ ⊢[PRAAx] le one M := h.andE₂.andE₂.andE₂.andE₁
  apply GaussianNamedLipschitzRate.independent_at R R (rdata a b D) (rdata A B D) (budget A B a b H) M
    (errorCost A B a b D) p q hM
    (GaussianRightHalfPlaneRadialLogarithm.regular a b D h₂.andE₁.andE₁ h₂.andE₂)
    (GaussianRightHalfPlaneRadialLogarithm.regular A B D h₁.andE₁.andE₁ h₁.andE₂)
  refine .allI ?_
  let sh (t : PTm n) := Syn.shift t
  let Δ := Γ.map Fm.shift
  have hs : Δ ⊢[PRAAx] admission (sh A) (sh B) (sh neg) (sh a) (sh b) (sh sign) (sh D) (sh H) (sh M) := by
    simpa only [Δ,sh,Fm.shift,Syn.shift,subst_admission] using h.shift
  simpa only [diagonalEnvelope,sh,Syn.shift,GaussianRightHalfPlaneRadialLogarithm.subst_data,subst_budget,subst_errorCost] using
    diagonal (var 0) (sh A) (sh B) (sh neg) (sh a) (sh b) (sh sign) (sh D) (sh H) (sh M) hs

theorem small_radial_distance (p q A B neg a b sign D H M : PTm n)
    (h : Γ ⊢[PRAAx] admission A B neg a b sign D H M)
    (hsmall : Γ ⊢[PRAAx] le (num 16*budget A B a b H) M)
    (hp : Γ ⊢[PRAAx] le (num 32) (unit p)) (hq : Γ ⊢[PRAAx] le (num 32) (unit q)) :
    Γ ⊢[PRAAx] distanceBounded (ap2 R p (rdata a b D)) (ap2 R q (rdata A B D)) one (num 8) := by
  have hM : Γ ⊢[PRAAx] le one M := h.andE₂.andE₂.andE₂.andE₁
  have hD := GaussianNamedInverseRate.denominator_positive M p q hM
  have h8 : Γ ⊢[PRAAx] le one (num 8) := le_of_eq_add (d := num 7) (by ipra_ring)
  have h4 : Γ ⊢[PRAAx] le one (num 4) := le_of_eq_add (d := num 3) (by ipra_ring)
  apply distance_radius_mono _ _ _ _ _ _ hD h8 ?_ (radial_distance p q A B neg a b sign D H M h)
  apply RationalValueBounds.positive_cancel h4
  unfold rateNumerator rateDenominator
  ipra_le 2*𝔞(unit p)*𝔞(unit q)*sl hsmall + 𝔞(M)*𝔞(unit p)*sl hq + 𝔞(M)*𝔞(unit q)*sl hp

theorem shifted_small_radial_distance (p q i A B neg a b sign D H M : PTm n)
    (h : Γ ⊢[PRAAx] admission A B neg a b sign D H M)
    (hsmall : Γ ⊢[PRAAx] le (num 16*budget A B a b H) M)
    (hA : Γ ⊢[PRAAx] le (num 16*H) A) (ha : Γ ⊢[PRAAx] le (num 16*H) a)
    (hp : Γ ⊢[PRAAx] le (num 32) (unit p)) (hq : Γ ⊢[PRAAx] le (num 32) (unit q)) :
    Γ ⊢[PRAAx] distanceBounded (ap2 R p (rdata (a+i*D) b D)) (ap2 R q (rdata (A+i*D) B D)) one (num 8) :=
  small_radial_distance p q (A+i*D) B neg (a+i*D) b sign D H (shiftedLower M H D i)
    (shifted_admission i A B neg a b sign D H M h hA ha) (shifted_smallness i A B a b D H M hsmall) hp hq

theorem actual_right_half_plane_radial_continuity_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 11
      (admission (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⟶
        distanceBounded (ap2 R (var 9) (rdata (var 3) (var 4) (var 6))) (ap2 R (var 10) (rdata (var 0) (var 1) (var 6)))
          (rateNumerator (budget (var 0) (var 1) (var 3) (var 4) (var 7)) (var 8) (var 9) (var 10))
          (rateDenominator (var 8) (var 9) (var 10))) :=
  closeUniv 11 (.impI (radial_distance _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianRightHalfPlaneRadialContinuity
