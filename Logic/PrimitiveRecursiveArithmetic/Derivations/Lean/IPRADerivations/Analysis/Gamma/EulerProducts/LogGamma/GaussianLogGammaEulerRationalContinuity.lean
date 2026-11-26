import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.GaussianLogGammaEulerReciprocalSlopeBound
import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.GaussianLogGammaEulerTaylorUniform
import IPRADerivations.Analysis.Names.Rates.GaussianNamedRateRadius

/-!
# A computable local continuity bound for the original log-Gamma name

The weighted cofinal slope is bounded uniformly by the displacement
times the disk-and-margin slope bound. The certified Taylor remainder
is then at most linear in that displacement. Independent observation
clocks retain exactly their standard dyadic allowances.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000

namespace LeanProofs.IPRA.Analysis.GaussianLogGammaEulerRationalContinuity

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianCoefficientNameBounds (bounded_radius_mono unit unit_positive)
open GaussianGammaCanonicalExponent (constantF constant_at)
open GaussianLogGammaEulerArgumentIncrement (step step_represents)
open GaussianLogGammaEulerReciprocalSlopeBound (bound)
open GaussianLogGammaEulerResidualDomain (native)
open GaussianLogGammaEulerResidualRadius (native_norm)
open GaussianLogGammaEulerTaylorCofinal (incrementF incrementData weightedF weightedData)
open GaussianLogGammaEulerTaylorRows (coefficient)
open GaussianLogGammaEulerTaylorUniform (source)
open GaussianNameArithmetic (multiply_at multiplyModulus recode_congr)
open GaussianNamedInverseRate (diagonal_rate independentRate)
open GaussianNamedLipschitzRate (diagonalDenominator diagonalEnvelope diagonalNumerator)
open GaussianRationalDistanceOrder (distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (positive_product qmul)
open GaussianRationalMetric (bounded bounded_of_cleared distanceBounded qsub)
open GaussianRationalReciprocal (bound_congr bounded_product)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianReconstructionRoots (norm_from_distance)
open GaussianRightHalfPlaneLogarithmIncrementMargin (smallStep)
open RationalValueBounds (positive_cancel)
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)
local notation "F" => GaussianLogGammaEulerCofinal.nameF
local notation "logData" => GaussianLogGammaEulerCofinal.canonicalData
local notation "S" => GaussianLogGammaEulerReciprocalSlopeCofinal.nameF
local notation "slopeData" => GaussianLogGammaEulerReciprocalSlopeCofinal.canonicalData

def response (K C : PTm n) : PTm n := bound C K + num 4*(K*K+two)

/-- The gain also pays for the local Taylor guard and the rounding of a
nonzero displacement to a natural radius. -/
def gain (K C : PTm n) : PTm n := two*response K C + num 256*(C+one)*(K*K)

@[simp] theorem subst_response {m : ℕ} (σ : Fin n → PTm m) (K C : PTm n) :
    Syn.subst σ (response K C) = response (Syn.subst σ K) (Syn.subst σ C) := by simp [response]

@[simp] theorem subst_gain {m : ℕ} (σ : Fin n → PTm m) (K C : PTm n) :
    Syn.subst σ (gain K C) = gain (Syn.subst σ K) (Syn.subst σ C) := by simp [gain]

theorem local_guard (H E K C d D : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (hStep : Γ ⊢[PRAAx] le (H*D) (two*E*d)) (hClose : Γ ⊢[PRAAx] le (gain K C*E) D) :
    Γ ⊢[PRAAx] smallStep H K C d := by
  apply positive_cancel (c := D) hD
  unfold gain at hClose
  ipra_le 128*(𝔞(C)+1)*𝔞(K)^2*sl hStep+𝔞(d)*sl hClose+2*𝔞(response K C)*𝔞(E)*𝔞(d)

private theorem source_disk (A B neg a b sign D H K C : PTm n)
    (h : Γ ⊢[PRAAx] source A B neg a b sign D H K C) :
    Γ ⊢[PRAAx] GaussianLogGammaEulerResidualDomain.source A B D neg C := by
  have total := h.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂.andE₁
  have hAB : Γ ⊢[PRAAx] le (A+B) (C*D) :=
    le_trans (le_congr (.eqRefl _) (by ipra_ring) (le_add_right (A+B) (a+b))) total
  have sq : Γ ⊢[PRAAx] le (A*A+B*B) ((A+B)*(A+B)) :=
    le_of_eq_add (d := two*A*B) (by ipra_ring)
  exact .andI h.andE₁ (le_congr (native_norm A B neg h.andE₁.andE₁.andE₂).eqSymm (.eqRefl _)
    (le_trans sq (le_mul_mono hAB hAB)))

private theorem step_le_denominator (H K C D : PTm n) (hK : Γ ⊢[PRAAx] le one K)
    (h : Γ ⊢[PRAAx] smallStep H K C D) : Γ ⊢[PRAAx] le H D := by
  have scale := positive_product (num 128*(C+one)) (K*K)
    (positive_product (num 128) (C+one) (le_of_eq_add (d := num 127) (by ipra_ring)) (le_add_left one C))
    (positive_product K K hK hK)
  exact le_trans (le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right H scale)) h

private theorem weighted_bound (p A B neg a b sign D H K C : PTm n)
    (h : Γ ⊢[PRAAx] source A B neg a b sign D H K C) :
    Γ ⊢[PRAAx] bounded (ap2 weightedF p (weightedData A B neg a b sign D)) (H*bound C K) D := by
  let w := step A B neg a b sign D
  let x := slopeData A B D neg
  let δ := GaussianRootAlgebra.sub (native a b sign) (native A B neg)
  let t := GaussianFastValueCut.exponent (multiplyModulus constantF S w x) p
  have hD := h.andE₁.andE₂
  have hK := h.andE₂.andE₂.andE₂.andE₁
  have hMargin := h.andE₂.andE₂.andE₂.andE₂.andE₁
  have disp : Γ ⊢[PRAAx] bounded w H D :=
    bounded_of_cleared w δ D H D hD hD (step_represents A B neg a b sign D hD)
      (le_congr (.eqRefl _) (by ipra_ring)
        (le_mul_mono (le_refl (D*D)) h.andE₂.andE₂.andE₁))
  have slope := GaussianLogGammaEulerReciprocalSlopeBound.canonical_at t A B D neg C K
    (source_disk A B neg a b sign D H K C h) hK hMargin
  let product := qmul w (ap2 S t x)
  have hb : Γ ⊢[PRAAx] bounded product (H*bound C K) D :=
    bound_congr (.eqRefl _) (.eqRefl _) (by ipra_ring)
      (bounded_product w (ap2 S t x) H D (bound C K) one hD (le_refl one) disp slope)
  have exactSample : Γ ⊢[PRAAx]
      ap2 weightedF p (weightedData A B neg a b sign D) ≐ GaussianFastValueCut.recode product :=
    (multiply_at constantF S w x p).eqTrans
      (recode_congr (qmul_congr (constant_at t w) (.eqRefl _)))
  exact bound_congr exactSample.eqSymm (.eqRefl _) (.eqRefl _)
    ((GaussianFastValueCut.recode_bound_iff product _ D hD).iffMpr hb)

theorem diagonal_at (p A B neg a b sign D H K C : PTm n)
    (h : Γ ⊢[PRAAx] source A B neg a b sign D H K C) :
    Γ ⊢[PRAAx] distanceBounded (ap2 F p (logData a b D sign)) (ap2 F p (logData A B D neg))
      (diagonalNumerator (response K C*H) D (num 8) p) (diagonalDenominator D p) := by
  let x := logData a b D sign
  let y := logData A B D neg
  let i := incrementData A B neg a b sign D
  let w := weightedData A B neg a b sign D
  let raw := qsub (ap2 F p x) (ap2 F p y)
  let U := unit p
  let Q := D*D*U
  let P := num 6*(D*D) + (coefficient H K*U+two*(D*D))
  have hD := h.andE₁.andE₂
  have hK := h.andE₂.andE₂.andE₂.andE₁
  have hSmall := h.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂
  have hHD := step_le_denominator H K C D hK hSmall
  have hDD := positive_product D D hD hD
  have hU := unit_positive (Γ := Γ) p
  have hQ := positive_product _ _ hDD hU
  have hDU := positive_product D U hD hU
  have hx := GaussianLogGammaEulerCofinal.canonical_regular a b D sign h.andE₂.andE₁
  have hy := GaussianLogGammaEulerCofinal.canonical_regular A B D neg h.andE₁
  have sample := distance_symmetric _ _ _ _ hU (GaussianNamedDifference.sample_error F F x y p hx hy)
  have first : Γ ⊢[PRAAx] distanceBounded raw (ap2 incrementF p i) (num 6*(D*D)) Q :=
    distance_radius_mono _ _ _ _ _ _ hU hQ (le_of_eq_add (d := zero) (by dsimp only [Q]; ipra_ring)) sample
  have taylor := diagonal_rate incrementF weightedF i w (coefficient H K) (D*D) p hDD
    (GaussianLogGammaEulerTaylorUniform.independent_rate A B neg a b sign D H K C h)
  have fromSlope : Γ ⊢[PRAAx] distanceBounded raw (ap2 weightedF p w) P Q :=
    distance_triangle_same raw (ap2 incrementF p i) (ap2 weightedF p w) _ _ Q hQ first taylor
  have size := norm_from_distance raw (ap2 weightedF p w) P Q (H*bound C K) D hQ hD fromSlope
    (weighted_bound p A B neg a b sign D H K C h)
  exact bounded_radius_mono raw (P*D+H*bound C K*Q) (Q*D)
    (diagonalNumerator (response K C*H) D (num 8) p) (diagonalDenominator D p)
    (positive_product Q D hQ hD) hDU
    (by
      unfold diagonalNumerator diagonalDenominator response
      dsimp only [P, Q, U, coefficient]
      ipra_le 4*𝔞(H)*(𝔞(K)^2+2)*𝔞(D)^2*𝔞(unit p)^2*sl hHD) size

theorem independent_rate (A B neg a b sign D H K C : PTm n)
    (h : Γ ⊢[PRAAx] source A B neg a b sign D H K C) :
    Γ ⊢[PRAAx] independentRate F F (logData a b D sign) (logData A B D neg) (response K C*H) D := by
  apply GaussianNamedLipschitzRate.independent_rate F F _ _ _ _ (num 8) h.andE₁.andE₂
    (GaussianLogGammaEulerCofinal.canonical_regular a b D sign h.andE₂.andE₁)
    (GaussianLogGammaEulerCofinal.canonical_regular A B D neg h.andE₁)
  refine .allI ?_
  let s (v : PTm n) := Syn.shift v
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (s A) (s B) (s neg) (s a) (s b) (s sign) (s D) (s H) (s K) (s C) := by
    simpa only [Fm.shift, Syn.shift, s, source, Fm.subst_and, subst_le, one, ConciseIPRA.PTm.subst_zero,
      ConciseIPRA.PTm.subst_succ, PTm.subst_mul, PTm.subst_add, GaussianRightHalfPlaneLogarithm.source,
      GaussianRightHalfPlaneArgument.subst_source,
      ComplexLogarithmRemainder.subst_bounded, GaussianRootAlgebra.subst_sub,
      GaussianLogGammaEulerResidualDomain.subst_native, GaussianRightHalfPlaneLogarithmIncrementMargin.subst_smallStep]
      using h.shift
  simpa only [diagonalEnvelope, Syn.shift, s, PTm.subst_mul, PTm.subst_num, subst_response,
    GaussianLogGammaEulerCofinal.subst_canonicalData] using
    diagonal_at (var 0) (s A) (s B) (s neg) (s a) (s b) (s sign) (s D) (s H) (s K) (s C) hs

theorem widened_rate (A B neg a b sign d H K C E D : PTm n)
    (h : Γ ⊢[PRAAx] source A B neg a b sign d H K C)
    (hD : Γ ⊢[PRAAx] le one D) (hStep : Γ ⊢[PRAAx] le (H*D) (two*E*d)) :
    Γ ⊢[PRAAx] independentRate F F (logData a b d sign) (logData A B d neg) (gain K C*E) D := by
  apply GaussianNamedRateRadius.weaken F F _ _ _ d _ D h.andE₁.andE₂ hD _ (independent_rate _ _ _ _ _ _ _ _ _ _ h)
  unfold gain
  ipra_le 𝔞(response K C)*sl hStep+256*(𝔞(C)+1)*𝔞(K)^2*𝔞(E)*𝔞(d)

theorem actual_cofinal_log_Gamma_rational_continuity_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
      (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) ⟶
        independentRate F F (logData (var 3) (var 4) (var 6) (var 5)) (logData (var 0) (var 1) (var 6) (var 2))
          (response (var 8) (var 9)*var 7) (var 6)) :=
  closeUniv 10 (.impI (independent_rate _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianLogGammaEulerRationalContinuity
