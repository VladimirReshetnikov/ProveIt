import IPRADerivations.Analysis.RationalArithmetic.GaussianRationalNormClearing
import IPRADerivations.Analysis.Inequalities.RationalNonnegativePowers
import IPRADerivations.Analysis.RationalArithmetic.FiniteProducts.GaussianRationalProductWitness

/-!
# Exact arithmetic for relative Gaussian-rational norm budgets

The statement relative u W L b is L^2*normSq(u)<=W^2*normSq(b),
using the actual normalized scalar operations. The numerical weights
may vanish. Transitivity and rescaling clear the independently decoded
denominators and cancel only a proved positive decoded denominator.
An actual natural rational multiple of an original raw Gaussian point
has its exact relative bound, with no input norm or representation law.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalRelativeNormAlgebra

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (represents positive_product ofGaussian)
open LeanProofs.IPRA.Analysis.GaussianRationalNormClearing (weightedNorm weighted_norm_represents)
open LeanProofs.IPRA.Analysis.GaussianRationalL1 (rawGaussian rawDen raw_represents raw_den_positive)
open LeanProofs.IPRA.Analysis.ComplexLogarithmRemainder (normSq scale normSq_scale)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def relative (u W L b : PTm n) : Fm PTm n :=
  RationalArgmin.rationalLE (weightedNorm (L*L) u) (weightedNorm (W*W) b)
def scaledPoint (A B b : PTm n) : PTm n := ofGaussian (scale A (rawGaussian b)) (B*rawDen b)

@[simp] theorem subst_relative {m : ℕ} (σ : Fin n → PTm m) (u W L b : PTm n) :
    (relative u W L b).subst σ = relative (Syn.subst σ u) (Syn.subst σ W) (Syn.subst σ L) (Syn.subst σ b) := by simp [relative]
@[simp] theorem subst_scaledPoint {m : ℕ} (σ : Fin n → PTm m) (A B b : PTm n) :
    Syn.subst σ (scaledPoint A B b) = scaledPoint (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ b) := by simp [scaledPoint]

theorem from_representations (u b gu gb D E W L : PTm n)
    (hD : Γ ⊢[PRAAx] le one D) (hE : Γ ⊢[PRAAx] le one E)
    (hu : Γ ⊢[PRAAx] represents u gu D) (hb : Γ ⊢[PRAAx] represents b gb E)
    (h : Γ ⊢[PRAAx] le (L*L*normSq gu*(E*E)) (W*W*normSq gb*(D*D))) : Γ ⊢[PRAAx]
    relative u W L b := GaussianRationalMetric.comparison_of_cleared _ _ _ _ _ _
      (positive_product _ _ hD hD) (positive_product _ _ hE hE)
      (weighted_norm_represents _ _ _ _ hD hu) (weighted_norm_represents _ _ _ _ hE hb)
      (le_congr (by ipra_ring) (.eqRefl _) h)

theorem to_cleared (u W L b : PTm n) (h : Γ ⊢[PRAAx] relative u W L b) : Γ ⊢[PRAAx]
    le (L*L*normSq (rawGaussian u)*(rawDen b*rawDen b))
      (W*W*normSq (rawGaussian b)*(rawDen u*rawDen u)) :=
  le_congr (by ipra_ring) (.eqRefl _) (GaussianRationalMetric.comparison_to_cleared _ _ _ _ _ _
    (weighted_norm_represents (L*L) u (rawGaussian u) (rawDen u) (raw_den_positive u) (raw_represents u))
    (weighted_norm_represents (W*W) b (rawGaussian b) (rawDen b) (raw_den_positive b) (raw_represents b)) h)

theorem of_cleared (u W L b : PTm n)
    (h : Γ ⊢[PRAAx] le (L*L*normSq (rawGaussian u)*(rawDen b*rawDen b))
      (W*W*normSq (rawGaussian b)*(rawDen u*rawDen u))) : Γ ⊢[PRAAx] relative u W L b :=
  from_representations u b _ _ _ _ W L (raw_den_positive u) (raw_den_positive b) (raw_represents u) (raw_represents b) h

/-- Only the common positive denominator is cancelled; the point and
all natural weights may be zero. -/
theorem relative_to_cleared (u b gu gb D W L : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (hu : Γ ⊢[PRAAx] represents u gu D) (hb : Γ ⊢[PRAAx] represents b gb D)
    (h : Γ ⊢[PRAAx] relative u W L b) : Γ ⊢[PRAAx] le (L*L*normSq gu) (W*W*normSq gb) := by
  have raw := GaussianRationalMetric.comparison_to_cleared _ _ _ _ _ _
    (weighted_norm_represents _ _ _ _ hD hu) (weighted_norm_represents _ _ _ _ hD hb) h
  exact RationalValueBounds.positive_cancel (positive_product D D hD hD)
    (le_congr (.eqRefl _) (by ipra_ring) raw)

theorem relative_refl (b W : PTm n) : Γ ⊢[PRAAx] relative b W W b := RationalArgmin.reflexive _

theorem relative_scale (u W L b C : PTm n) (h : Γ ⊢[PRAAx] relative u W L b) : Γ ⊢[PRAAx]
    relative u (C*W) (C*L) b :=
  of_cleared u (C*W) (C*L) b (le_congr (by ipra_ring) (by ipra_ring)
    (mul_le_mul_right (C*C) (to_cleared u W L b h)))

/-- Genuine composition of independently denominated relative estimates. -/
theorem relative_trans (u x b W L V M : PTm n)
    (hu : Γ ⊢[PRAAx] relative u W L x) (hx : Γ ⊢[PRAAx] relative x V M b) : Γ ⊢[PRAAx]
    relative u (W*V) (L*M) b := by
  have first := mul_le_mul_right (M*M*(rawDen b*rawDen b)) (to_cleared u W L x hu)
  have second := mul_le_mul_right (W*W*(rawDen u*rawDen u)) (to_cleared x V M b hx)
  have start : Γ ⊢[PRAAx]
      le ((rawDen x*rawDen x)*((L*M)*(L*M)*normSq (rawGaussian u)*(rawDen b*rawDen b)))
        (W*W*normSq (rawGaussian x)*(rawDen u*rawDen u)*(M*M*(rawDen b*rawDen b))) :=
    le_congr (by ipra_ring) (.eqRefl _) first
  have finish : Γ ⊢[PRAAx]
      le (W*W*normSq (rawGaussian x)*(rawDen u*rawDen u)*(M*M*(rawDen b*rawDen b)))
        ((rawDen x*rawDen x)*((W*V)*(W*V)*normSq (rawGaussian b)*(rawDen u*rawDen u))) :=
    le_congr (by ipra_ring) (by ipra_ring) second
  have joined : Γ ⊢[PRAAx]
      le ((rawDen x*rawDen x)*((L*M)*(L*M)*normSq (rawGaussian u)*(rawDen b*rawDen b)))
        ((rawDen x*rawDen x)*((W*V)*(W*V)*normSq (rawGaussian b)*(rawDen u*rawDen u))) :=
    le_trans start finish
  exact of_cleared u (W*V) (L*M) b
    (RationalValueBounds.positive_cancel (positive_product _ _ (raw_den_positive x) (raw_den_positive x)) joined)

theorem relative_weight_mono (u W V L b : PTm n) (hWV : Γ ⊢[PRAAx] le W V)
    (h : Γ ⊢[PRAAx] relative u W L b) : Γ ⊢[PRAAx] relative u V L b :=
  of_cleared u V L b (le_trans (to_cleared u W L b h)
    (le_congr (by ipra_ring) (by ipra_ring)
      (mul_le_mul_right (normSq (rawGaussian b)*(rawDen u*rawDen u)) (sq_le_sq hWV))))

theorem weighted_congr {u v A B : PTm n} (hu : Γ ⊢[PRAAx] u ≐ v) (hAB : Γ ⊢[PRAAx] A ≐ B) :
    Γ ⊢[PRAAx] weightedNorm A u ≐ weightedNorm B v :=
  RationalAlgebra.multiply_congr (RationalNonnegativePowers.fraction_congr hAB (.eqRefl _))
    (GaussianRationalProductWitness.qnormSq_congr hu)

theorem relative_congr {u u' W W' L L' b b' : PTm n}
    (hu : Γ ⊢[PRAAx] u ≐ u') (hW : Γ ⊢[PRAAx] W ≐ W')
    (hL : Γ ⊢[PRAAx] L ≐ L') (hb : Γ ⊢[PRAAx] b ≐ b')
    (h : Γ ⊢[PRAAx] relative u W L b) : Γ ⊢[PRAAx] relative u' W' L' b' :=
  RationalArgmin.rationalLE_congr (weighted_congr hu (congrMul hL hL))
    (weighted_congr hb (congrMul hW hW)) h

/-- This is an actual output point, not an assumed multiplication law. -/
theorem scaled_point_relative (A B b : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    relative (scaledPoint A B b) A B b := by
  have hD := raw_den_positive (Γ := Γ) b
  have hBD := positive_product B (rawDen b) hB hD
  exact from_representations _ _ _ _ _ _ _ _ hBD hD
    (GaussianRationalHorner.ofGaussian_represents _ _ hBD) (raw_represents b)
    (le_congr ((congrMul (congrMul (.eqRefl _) (normSq_scale A (rawGaussian b))) (.eqRefl _)).eqTrans
      (by ipra_ring)).eqSymm (.eqRefl _) (le_refl _))

/-- Multiplication by an actual point in the A/B disk gives the exact
same relative bound against the original other factor. -/
theorem product_relative (q r A B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hr : Γ ⊢[PRAAx] GaussianRationalMetric.bounded r A B) : Γ ⊢[PRAAx]
    relative (GaussianRationalHorner.qmul q r) A B q := by
  have hD := raw_den_positive (Γ := Γ) q
  have hE := raw_den_positive (Γ := Γ) r
  have hDE := positive_product _ _ hD hE
  have bound := GaussianRationalMetric.bounded_to_cleared r (rawGaussian r) (rawDen r) A B hE hB (raw_represents r) hr
  have scaled := mul_le_mul_right (normSq (rawGaussian q)*(rawDen q*rawDen q)) bound
  exact from_representations _ _ _ _ _ _ _ _ hDE hD
    (GaussianRationalHorner.qmul_represents _ _ _ _ _ _ hD hE (raw_represents q) (raw_represents r)) (raw_represents q)
    (le_congr ((congrMul (congrMul (.eqRefl _) (ComplexLogarithmRemainder.normSq_mul _ _)) (.eqRefl _)).eqTrans
      (by ipra_ring)).eqSymm (by ipra_ring) scaled)

theorem relative_composition_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (relative (var 0) (var 3) (var 4) (var 1) ⟶ relative (var 1) (var 5) (var 6) (var 2) ⟶
      relative (var 0) (var 3*var 5) (var 4*var 6) (var 2)) :=
  closeUniv 7 (.impI (.impI (relative_trans _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem relative_rescaling_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (relative (var 0) (var 1) (var 2) (var 3) ⟶ relative (var 0) (var 4*var 1) (var 4*var 2) (var 3)) :=
  closeUniv 5 (.impI (relative_scale _ _ _ _ _ Prf.hyp0))

theorem actual_scaled_point_relative_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶ relative (scaledPoint (var 0) (var 1) (var 2)) (var 0) (var 1) (var 2)) :=
  closeUniv 3 (.impI (scaled_point_relative _ _ _ Prf.hyp0))

theorem actual_product_relative_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 3) ⟶ GaussianRationalMetric.bounded (var 1) (var 2) (var 3) ⟶
      relative (GaussianRationalHorner.qmul (var 0) (var 1)) (var 2) (var 3) (var 0)) :=
  closeUniv 4 (.impI (.impI (product_relative _ _ _ _ Prf.hyp1 Prf.hyp0)))

def output (u W L b : PTm n) : PTm n := pairT (weightedNorm (L*L) u) (weightedNorm (W*W) b)
def outputF : PR 4 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3))
def run (u W L b : PTm n) : PTm n := PTm.app outputF ![u,W,L,b]

@[simp] theorem subst_output {m : ℕ} (σ : Fin n → PTm m) (u W L b : PTm n) :
    Syn.subst σ (output u W L b) = output (Syn.subst σ u) (Syn.subst σ W) (Syn.subst σ L) (Syn.subst σ b) := by simp [output]
@[simp] theorem subst_run {m : ℕ} (σ : Fin n → PTm m) (u W L b : PTm n) :
    Syn.subst σ (run u W L b) = run (Syn.subst σ u) (Syn.subst σ W) (Syn.subst σ L) (Syn.subst σ b) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem program_at (u W L b : PTm n) : Γ ⊢[PRAAx] run u W L b ≐ output u W L b := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) : PTm 4) ![u,W,L,b]
theorem returned_left (u W L b : PTm n) : Γ ⊢[PRAAx] fstT (run u W L b) ≐ weightedNorm (L*L) u :=
  (congrFst (program_at u W L b)).eqTrans (fst_pair _ _)
theorem returned_right (u W L b : PTm n) : Γ ⊢[PRAAx] sndT (run u W L b) ≐ weightedNorm (W*W) b :=
  (congrSnd (program_at u W L b)).eqTrans (snd_pair _ _)

theorem relative_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((run (var 0) (var 1) (var 2) (var 3) ≐ output (var 0) (var 1) (var 2) (var 3)) ⋏
      (fstT (run (var 0) (var 1) (var 2) (var 3)) ≐ weightedNorm (var 2*var 2) (var 0) ⋏
        sndT (run (var 0) (var 1) (var 2) (var 3)) ≐ weightedNorm (var 1*var 1) (var 3))) :=
  closeUniv 4 (.andI (program_at _ _ _ _) (.andI (returned_left _ _ _ _) (returned_right _ _ _ _)))

theorem returned_relative_comparison_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (relative (var 0) (var 1) (var 2) (var 3) ⟶ RationalArgmin.rationalLE
      (fstT (run (var 0) (var 1) (var 2) (var 3))) (sndT (run (var 0) (var 1) (var 2) (var 3)))) :=
  closeUniv 4 (.impI (RationalArgmin.rationalLE_congr (returned_left _ _ _ _).eqSymm
    (returned_right _ _ _ _).eqSymm Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianRationalRelativeNormAlgebra
