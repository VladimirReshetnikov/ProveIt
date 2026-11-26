import IPRADerivations.Analysis.Names.Rates.GaussianNamedLipschitzRate
import IPRADerivations.Analysis.Names.GaussianNameRingLaws

/-!
# Exact product rates for the actual normalized Gaussian names

The genuine raw product difference uses the sampled bound on G for
F-H and the sampled bound on H for G-K. Both original normalization
errors are retained in a finite diagonal envelope. The proved finite
integer-gap bridge removes that auxiliary envelope, leaving the exact
weighted sum of the two input rates and independent output errors.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedMultiplyRate

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianNameArithmetic (multiplyF multiplyData multiplyModulus multiply_fast)
open GaussianNamedInverseRate (independentRate rate_at rateNumerator rateDenominator denominator_positive)
open GaussianNamedLipschitzRate (diagonalNumerator diagonalDenominator diagonalEnvelope)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same distance_symmetric)
open GaussianEuclideanDistanceName (pointCN)
open GaussianCoefficientNameBounds (unit unit_positive)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def sampleBound (F : PR 2) (x M : PTm n) : Fm PTm n := .all
  (bounded (ap2 F (var 0) (Syn.shift x)) (Syn.shift M) one)
def leadingNumerator (A B C E M R : PTm n) : PTm n := M*A*E+R*C*B
def leadingDenominator (B E : PTm n) : PTm n := B*E
def observationCost (F G H K : PR 2) (x y u v M R : PTm n) : PTm n :=
  (multiplyModulus F G x y+one)+(multiplyModulus H K u v+one)+two*(M+R)
def input (F G H K : PR 2) (x y u v A B C E M R : PTm n) : Fm PTm n :=
  le one B ⋏ (le one E ⋏ (pointCN F x ⋏ (pointCN G y ⋏ (pointCN H u ⋏ (pointCN K v ⋏
    (sampleBound G y M ⋏ (sampleBound H u R ⋏ (independentRate F H x u A B ⋏ independentRate G K y v C E))))))))

@[simp] theorem subst_sampleBound {m : ℕ} (σ : Fin n → PTm m) (F : PR 2) (x M : PTm n) :
    (sampleBound F x M).subst σ = sampleBound F (Syn.subst σ x) (Syn.subst σ M) := by
  simp [sampleBound,Syn.subst_shift,Syn.shift_subst]
@[simp] theorem subst_leadingNumerator {m : ℕ} (σ : Fin n → PTm m) (A B C E M R : PTm n) :
    Syn.subst σ (leadingNumerator A B C E M R) = leadingNumerator (Syn.subst σ A) (Syn.subst σ B)
      (Syn.subst σ C) (Syn.subst σ E) (Syn.subst σ M) (Syn.subst σ R) := by simp [leadingNumerator]
@[simp] theorem subst_leadingDenominator {m : ℕ} (σ : Fin n → PTm m) (B E : PTm n) :
    Syn.subst σ (leadingDenominator B E) = leadingDenominator (Syn.subst σ B) (Syn.subst σ E) := by simp [leadingDenominator]
@[simp] theorem subst_observationCost {m : ℕ} (σ : Fin n → PTm m) (F G H K : PR 2) (x y u v M R : PTm n) :
    Syn.subst σ (observationCost F G H K x y u v M R) = observationCost F G H K (Syn.subst σ x) (Syn.subst σ y)
      (Syn.subst σ u) (Syn.subst σ v) (Syn.subst σ M) (Syn.subst σ R) := by simp [observationCost]
@[simp] theorem subst_input {m : ℕ} (σ : Fin n → PTm m) (F G H K : PR 2) (x y u v A B C E M R : PTm n) :
    (input F G H K x y u v A B C E M R).subst σ = input F G H K (Syn.subst σ x) (Syn.subst σ y)
      (Syn.subst σ u) (Syn.subst σ v) (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ C) (Syn.subst σ E)
      (Syn.subst σ M) (Syn.subst σ R) := by simp [input]

theorem sample_bound_at (F : PR 2) (x M t : PTm n) (h : Γ ⊢[PRAAx] sampleBound F x M) : Γ ⊢[PRAAx]
    bounded (ap2 F t x) M one := by
  simpa only [sampleBound,GaussianRationalMetric.subst_bounded,subst_ap2,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using h.allE t

theorem original_diagonal (F G H K : PR 2) (x y u v A B C E M R t : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hE : Γ ⊢[PRAAx] le one E)
    (hF : Γ ⊢[PRAAx] pointCN F x) (hG : Γ ⊢[PRAAx] pointCN G y)
    (hH : Γ ⊢[PRAAx] pointCN H u) (hK : Γ ⊢[PRAAx] pointCN K v)
    (hGM : Γ ⊢[PRAAx] sampleBound G y M) (hHR : Γ ⊢[PRAAx] sampleBound H u R)
    (hFH : Γ ⊢[PRAAx] independentRate F H x u A B) (hGK : Γ ⊢[PRAAx] independentRate G K y v C E) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (multiplyF F G) t (multiplyData F G x y)) (ap2 (multiplyF H K) t (multiplyData H K u v))
      (diagonalNumerator (leadingNumerator A B C E M R) (leadingDenominator B E) (observationCost F G H K x y u v M R) t)
      (diagonalDenominator (leadingDenominator B E) t) := by
  let D := B*E*unit t
  have be := positive_product _ _ hB hE
  have dt : Γ ⊢[PRAAx] le one D := positive_product _ _ be (unit_positive t)
  have leftRate : Γ ⊢[PRAAx] distanceBounded (ap2 F t x) (ap2 H t u) ((A*unit t+two*B)*E) D :=
    distance_radius_mono _ _ _ _ _ _ (denominator_positive B t t hB) dt
      (le_of_eq_add (d := zero) (by dsimp [D,rateNumerator,rateDenominator]; ipra_ring)) (rate_at F H x u A B t t hFH)
  have rightRate : Γ ⊢[PRAAx] distanceBounded (ap2 G t y) (ap2 K t v) ((C*unit t+two*E)*B) D :=
    distance_radius_mono _ _ _ _ _ _ (denominator_positive E t t hE) dt
      (le_of_eq_add (d := zero) (by dsimp [D,rateNumerator,rateDenominator]; ipra_ring)) (rate_at G K y v C E t t hGK)
  have raw := GaussianNameArithmetic.product_distance _ _ _ _ _ _ D M R dt leftRate rightRate
    (sample_bound_at G y M t hGM) (sample_bound_at H u R t hHR)
  have before : Γ ⊢[PRAAx]
      distanceBounded (ap2 (multiplyF F G) t (multiplyData F G x y)) (qmul (ap2 F t x) (ap2 G t y))
        ((multiplyModulus F G x y+one)*(B*E)) D :=
    distance_radius_mono _ _ _ _ _ _ (unit_positive t) dt
      (le_of_eq_add (d := zero) (by dsimp [D]; ipra_ring)) (GaussianNameRingLaws.multiply_sample_error F G x y t hF hG)
  have after : Γ ⊢[PRAAx]
      distanceBounded (qmul (ap2 H t u) (ap2 K t v)) (ap2 (multiplyF H K) t (multiplyData H K u v))
        ((multiplyModulus H K u v+one)*(B*E)) D :=
    distance_radius_mono _ _ _ _ _ _ (unit_positive t) dt
      (le_of_eq_add (d := zero) (by dsimp [D]; ipra_ring))
      (distance_symmetric _ _ _ _ (unit_positive t) (GaussianNameRingLaws.multiply_sample_error H K u v t hH hK))
  exact distance_congr (.eqRefl _) (.eqRefl _)
    (by dsimp [diagonalNumerator,leadingNumerator,leadingDenominator,observationCost]; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ dt (distance_triangle_same _ _ _ _ _ _ dt before raw) after)

theorem original_envelope (F G H K : PR 2) (x y u v A B C E M R : PTm n)
    (hs : Γ ⊢[PRAAx] input F G H K x y u v A B C E M R) : Γ ⊢[PRAAx]
    diagonalEnvelope (multiplyF F G) (multiplyF H K) (multiplyData F G x y) (multiplyData H K u v)
      (leadingNumerator A B C E M R) (leadingDenominator B E) (observationCost F G H K x y u v M R) := by
  have hh : Γ.map Fm.shift ⊢[PRAAx] input F G H K (Syn.shift x) (Syn.shift y) (Syn.shift u) (Syn.shift v)
      (Syn.shift A) (Syn.shift B) (Syn.shift C) (Syn.shift E) (Syn.shift M) (Syn.shift R) :=
    by simpa only [Fm.shift,subst_input,Syn.shift] using hs.shift
  refine .allI ?_
  simpa only [diagonalEnvelope,GaussianNameArithmetic.subst_multiplyData,subst_leadingNumerator,subst_leadingDenominator,
    subst_observationCost,Syn.shift] using
    original_diagonal F G H K (Syn.shift x) (Syn.shift y) (Syn.shift u) (Syn.shift v) (Syn.shift A) (Syn.shift B)
      (Syn.shift C) (Syn.shift E) (Syn.shift M) (Syn.shift R) (var 0) hh.andE₁ hh.andE₂.andE₁
      hh.andE₂.andE₂.andE₁ hh.andE₂.andE₂.andE₂.andE₁ hh.andE₂.andE₂.andE₂.andE₂.andE₁
      hh.andE₂.andE₂.andE₂.andE₂.andE₂.andE₁ hh.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂.andE₁
      hh.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂.andE₁
      hh.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂.andE₁
      hh.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂

theorem rate_of_input (F G H K : PR 2) (x y u v A B C E M R : PTm n)
    (hs : Γ ⊢[PRAAx] input F G H K x y u v A B C E M R) : Γ ⊢[PRAAx]
    independentRate (multiplyF F G) (multiplyF H K) (multiplyData F G x y) (multiplyData H K u v)
      (leadingNumerator A B C E M R) (leadingDenominator B E) :=
  GaussianNamedLipschitzRate.independent_rate _ _ _ _ _ _ _ (positive_product _ _ hs.andE₁ hs.andE₂.andE₁)
    (multiply_fast _ _ _ _ hs.andE₂.andE₂.andE₁ hs.andE₂.andE₂.andE₂.andE₁)
    (multiply_fast _ _ _ _ hs.andE₂.andE₂.andE₂.andE₂.andE₁ hs.andE₂.andE₂.andE₂.andE₂.andE₂.andE₁)
    (original_envelope F G H K x y u v A B C E M R hs)

theorem independent_rate (F G H K : PR 2) (x y u v A B C E M R : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hE : Γ ⊢[PRAAx] le one E)
    (hF : Γ ⊢[PRAAx] pointCN F x) (hG : Γ ⊢[PRAAx] pointCN G y)
    (hH : Γ ⊢[PRAAx] pointCN H u) (hK : Γ ⊢[PRAAx] pointCN K v)
    (hGM : Γ ⊢[PRAAx] sampleBound G y M) (hHR : Γ ⊢[PRAAx] sampleBound H u R)
    (hFH : Γ ⊢[PRAAx] independentRate F H x u A B) (hGK : Γ ⊢[PRAAx] independentRate G K y v C E) : Γ ⊢[PRAAx]
    independentRate (multiplyF F G) (multiplyF H K) (multiplyData F G x y) (multiplyData H K u v)
      (leadingNumerator A B C E M R) (leadingDenominator B E) :=
  rate_of_input F G H K x y u v A B C E M R
    (.andI hB (.andI hE (.andI hF (.andI hG (.andI hH (.andI hK (.andI hGM (.andI hHR (.andI hFH hGK)))))))))

theorem independent_at (F G H K : PR 2) (x y u v A B C E M R p q : PTm n)
    (hs : Γ ⊢[PRAAx] input F G H K x y u v A B C E M R) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (multiplyF F G) p (multiplyData F G x y)) (ap2 (multiplyF H K) q (multiplyData H K u v))
      (rateNumerator (leadingNumerator A B C E M R) (leadingDenominator B E) p q)
      (rateDenominator (leadingDenominator B E) p q) :=
  rate_at _ _ _ _ _ _ p q (rate_of_input F G H K x y u v A B C E M R hs)

theorem actual_normalized_product_independent_rate_closed (F G H K : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
    (input F G H K (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) ⟶
      independentRate (multiplyF F G) (multiplyF H K)
        (multiplyData F G (var 0) (var 1)) (multiplyData H K (var 2) (var 3))
        (leadingNumerator (var 4) (var 5) (var 6) (var 7) (var 8) (var 9)) (leadingDenominator (var 5) (var 7))) :=
  closeUniv 10 (.impI (rate_of_input F G H K _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianNamedMultiplyRate
