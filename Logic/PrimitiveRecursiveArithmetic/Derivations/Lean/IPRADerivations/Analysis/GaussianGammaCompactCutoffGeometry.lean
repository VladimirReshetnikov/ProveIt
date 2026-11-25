import IPRADerivations.Analysis.GaussianGammaCompactQuadratureBoundary
import IPRADerivations.Core.LinearCombination

/-!
# Exact original Euler cutoffs on a common later denominator

All cutoffs and the refinement factor are original numerical programs.
Power addition proves the exact positive dyadic denominator refinement.
The actual later interval splits into lower, rescaled old, and upper
widths, with true original endpoints and guarded positivity. No analytic
tail or quadrature/additivity law is supplied or asserted here.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaCompactCutoffGeometry

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaIntegralCutoffs (etaDen top height)
open GaussianGammaCompactQuadratureBoundary (width exact_right_endpoint)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (positive_product)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def delta (p q : PTm n) : PTm n := monus q p
def ratio (p q A : PTm n) : PTm n := unit (A*delta p q)
def lowerWidth (p q A : PTm n) : PTm n := monus (ratio p q A) one
def middleWidth (p q A R : PTm n) : PTm n := ratio p q A*width p A R
def upperWidth (p q A R : PTm n) : PTm n := etaDen q A R*(two*delta p q)
@[simp] theorem subst_delta {m : ℕ} (σ : Fin n → PTm m) (p q : PTm n) :
    Syn.subst σ (delta p q) = delta (Syn.subst σ p) (Syn.subst σ q) := by simp [delta]
@[simp] theorem subst_ratio {m : ℕ} (σ : Fin n → PTm m) (p q A : PTm n) :
    Syn.subst σ (ratio p q A) = ratio (Syn.subst σ p) (Syn.subst σ q) (Syn.subst σ A) := by simp [ratio]
@[simp] theorem subst_lowerWidth {m : ℕ} (σ : Fin n → PTm m) (p q A : PTm n) :
    Syn.subst σ (lowerWidth p q A) = lowerWidth (Syn.subst σ p) (Syn.subst σ q) (Syn.subst σ A) := by simp [lowerWidth]
@[simp] theorem subst_middleWidth {m : ℕ} (σ : Fin n → PTm m) (p q A R : PTm n) :
    Syn.subst σ (middleWidth p q A R) = middleWidth (Syn.subst σ p) (Syn.subst σ q) (Syn.subst σ A) (Syn.subst σ R) := by simp [middleWidth]
@[simp] theorem subst_upperWidth {m : ℕ} (σ : Fin n → PTm m) (p q A R : PTm n) :
    Syn.subst σ (upperWidth p q A R) = upperWidth (Syn.subst σ p) (Syn.subst σ q) (Syn.subst σ A) (Syn.subst σ R) := by
  simp [upperWidth,etaDen,height,GaussianGammaIntegralCutoffs.tailCoefficient]

theorem ratio_positive (p q A : PTm n) : Γ ⊢[PRAAx] le one (ratio p q A) := unit_positive _
theorem height_refinement (p q A R : PTm n) (h : Γ ⊢[PRAAx] le p q) : Γ ⊢[PRAAx]
    height q A R ≐ height p A R+delta p q := by
  have e := natEq (eq_add_of_le h)
  apply deriveNat
  unfold height delta
  ipra_simps
  rw [e]
  ring

theorem eta_den_refinement (p q A R : PTm n) (h : Γ ⊢[PRAAx] le p q) : Γ ⊢[PRAAx]
    etaDen q A R ≐ ratio p q A*etaDen p A R := by
  have exponent : Γ ⊢[PRAAx] A*height q A R ≐ A*height p A R+A*delta p q :=
    (congrMul (.eqRefl A) (height_refinement p q A R h)).eqTrans (by ipra_ring)
  exact (congrAp2 powF exponent (.eqRefl two)).eqTrans ((pw_add two _ _).eqTrans (mul_comm _ _))

theorem top_refinement (p q A R : PTm n) (h : Γ ⊢[PRAAx] le p q) : Γ ⊢[PRAAx]
    top q A R ≐ top p A R+two*delta p q :=
  (congrMul (.eqRefl two) (height_refinement p q A R h)).eqTrans (by unfold top; ipra_ring)
theorem top_monotone (p q A R : PTm n) (h : Γ ⊢[PRAAx] le p q) : Γ ⊢[PRAAx] le (top p A R) (top q A R) :=
  le_of_eq_add (top_refinement p q A R h)

theorem lower_endpoint (p q A : PTm n) : Γ ⊢[PRAAx] one+lowerWidth p q A ≐ ratio p q A :=
  (eq_add_of_le (ratio_positive p q A)).eqSymm

theorem middle_endpoint (p q A R : PTm n) (h : Γ ⊢[PRAAx] le p q) : Γ ⊢[PRAAx]
    ratio p q A+middleWidth p q A R ≐ etaDen q A R*top p A R :=
  (by unfold middleWidth; ipra_ring : Γ ⊢[PRAAx] ratio p q A+middleWidth p q A R ≐ ratio p q A*(one+width p A R)).eqTrans
    ((congrMul (.eqRefl _) (exact_right_endpoint p A R)).eqTrans
      ((by ipra_ring : Γ ⊢[PRAAx] ratio p q A*(etaDen p A R*top p A R) ≐ (ratio p q A*etaDen p A R)*top p A R).eqTrans
        (congrMul (eta_den_refinement p q A R h).eqSymm (.eqRefl _))))

theorem three_endpoint (p q A R : PTm n) (h : Γ ⊢[PRAAx] le p q) : Γ ⊢[PRAAx]
    one+(lowerWidth p q A+middleWidth p q A R+upperWidth p q A R) ≐ etaDen q A R*top q A R :=
  (by ipra_ring : Γ ⊢[PRAAx] one+(lowerWidth p q A+middleWidth p q A R+upperWidth p q A R) ≐
      ((one+lowerWidth p q A)+middleWidth p q A R)+upperWidth p q A R).eqTrans
    ((congrAdd (congrAdd (lower_endpoint p q A) (.eqRefl _)) (.eqRefl _)).eqTrans
      ((congrAdd (middle_endpoint p q A R h) (.eqRefl _)).eqTrans
        ((by unfold upperWidth; ipra_ring : Γ ⊢[PRAAx] etaDen q A R*top p A R+upperWidth p q A R ≐ etaDen q A R*(top p A R+two*delta p q)).eqTrans
          (congrMul (.eqRefl _) (top_refinement p q A R h).eqSymm))))

theorem widths_total (p q A R : PTm n) (h : Γ ⊢[PRAAx] le p q) : Γ ⊢[PRAAx]
    lowerWidth p q A+middleWidth p q A R+upperWidth p q A R ≐ width q A R := by
  ipra_lc natEq ((three_endpoint p q A R h).eqTrans (exact_right_endpoint q A R).eqSymm)

theorem gap_positive (p q : PTm n) (h : Γ ⊢[PRAAx] lt p q) : Γ ⊢[PRAAx] le one (delta p q) := by
  have e : Γ ⊢[PRAAx] q ≐ p+succ (monus q (succ p)) := (eq_add_of_le h).eqTrans (by ipra_ring)
  have g := (congrMonus e (.eqRefl p)).eqTrans (add_monus' (succ (monus q (succ p))) p)
  exact le_congr (.eqRefl _) g.eqSymm (zero_lt_succ _)

theorem width_positive (p A R : PTm n) : Γ ⊢[PRAAx] le one (width p A R) := by
  have tp : Γ ⊢[PRAAx] le two (top p A R) :=
    le_congr (by ipra_ring) (.eqRefl _) (AnalyticNumberTheory.PhiLower.le_mul_mono (le_refl two) (GaussianGammaIntegralCutoffs.height_positive p A R))
  have product : Γ ⊢[PRAAx] lt one (etaDen p A R*top p A R) :=
    le_congr (by ipra_ring) (.eqRefl _) (AnalyticNumberTheory.PhiLower.le_mul_mono (GaussianGammaIntegralCutoffs.eta_den_positive p A R) tp)
  exact gap_positive one (etaDen p A R*top p A R) product

theorem middle_positive (p q A R : PTm n) : Γ ⊢[PRAAx] le one (middleWidth p q A R) :=
  positive_product _ _ (ratio_positive p q A) (width_positive p A R)

theorem lower_positive (p q A : PTm n) (hA : Γ ⊢[PRAAx] le one A) (h : Γ ⊢[PRAAx] lt p q) : Γ ⊢[PRAAx]
    le one (lowerWidth p q A) := by
  have exponent := positive_product (Γ := Γ) _ _ hA (gap_positive p q h)
  have grow := GaussianFactorBudget.power_monotone_length (Γ := Γ) two one (A*delta p q) (le_succ_self one) exponent
  exact gap_positive one (ratio p q A) (le_congr (pw_one two) (.eqRefl _) grow)

theorem upper_positive (p q A R : PTm n) (h : Γ ⊢[PRAAx] lt p q) : Γ ⊢[PRAAx] le one (upperWidth p q A R) :=
  positive_product _ _ (GaussianGammaIntegralCutoffs.eta_den_positive q A R)
    (positive_product _ _ (zero_lt_succ one) (gap_positive p q h))

theorem same_ratio (p A : PTm n) : Γ ⊢[PRAAx] ratio p p A ≐ one :=
  (congrAp2 powF ((congrMul (.eqRefl A) (monus_self p)).eqTrans (mul_zero A)) (.eqRefl two)).eqTrans (pw_zero two)
theorem same_lower (p A : PTm n) : Γ ⊢[PRAAx] lowerWidth p p A ≐ zero :=
  (congrMonus (same_ratio p A) (.eqRefl one)).eqTrans (monus_self one)
theorem same_middle (p A R : PTm n) : Γ ⊢[PRAAx] middleWidth p p A R ≐ width p A R :=
  (congrMul (same_ratio p A) (.eqRefl _)).eqTrans (one_mul _)
theorem same_upper (p A R : PTm n) : Γ ⊢[PRAAx] upperWidth p p A R ≐ zero :=
  (congrMul (.eqRefl _) (congrMul (.eqRefl two) (monus_self p))).eqTrans (by ipra_ring)

def output (p q A R : PTm n) : PTm n := pairT (ratio p q A) (pairT (lowerWidth p q A) (pairT (middleWidth p q A R) (upperWidth p q A R)))
def outputF : PR 4 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3))
def run (p q A R : PTm n) : PTm n := PTm.app outputF ![p,q,A,R]
@[simp] theorem subst_output {m : ℕ} (σ : Fin n → PTm m) (p q A R : PTm n) :
    Syn.subst σ (output p q A R) = output (Syn.subst σ p) (Syn.subst σ q) (Syn.subst σ A) (Syn.subst σ R) := by simp [output]
theorem program_at (p q A R : PTm n) : Γ ⊢[PRAAx] run p q A R ≐ output p q A R := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) : PTm 4) ![p,q,A,R]
theorem returned_ratio (p q A R : PTm n) : Γ ⊢[PRAAx] fstT (run p q A R) ≐ ratio p q A :=
  (congrFst (program_at p q A R)).eqTrans (fst_pair _ _)
theorem returned_tail (p q A R : PTm n) : Γ ⊢[PRAAx]
    sndT (run p q A R) ≐ pairT (lowerWidth p q A) (pairT (middleWidth p q A R) (upperWidth p q A R)) :=
  (congrSnd (program_at p q A R)).eqTrans (snd_pair _ _)
theorem returned_lower (p q A R : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run p q A R)) ≐ lowerWidth p q A :=
  (congrFst (returned_tail p q A R)).eqTrans (fst_pair _ _)
theorem returned_last (p q A R : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run p q A R)) ≐ pairT (middleWidth p q A R) (upperWidth p q A R) :=
  (congrSnd (returned_tail p q A R)).eqTrans (snd_pair _ _)
theorem returned_middle (p q A R : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run p q A R))) ≐ middleWidth p q A R :=
  (congrFst (returned_last p q A R)).eqTrans (fst_pair _ _)
theorem returned_upper (p q A R : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (run p q A R))) ≐ upperWidth p q A R :=
  (congrSnd (returned_last p q A R)).eqTrans (snd_pair _ _)
theorem returned_total (p q A R : PTm n) (h : Γ ⊢[PRAAx] le p q) : Γ ⊢[PRAAx]
    fstT (sndT (run p q A R))+fstT (sndT (sndT (run p q A R)))+sndT (sndT (sndT (run p q A R))) ≐ width q A R :=
  (congrAdd (congrAdd (returned_lower p q A R) (returned_middle p q A R)) (returned_upper p q A R)).eqTrans (widths_total p q A R h)

theorem original_eta_denominator_refinement_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le (var 0) (var 1) ⟶ etaDen (var 1) (var 2) (var 3) ≐ ratio (var 0) (var 1) (var 2)*etaDen (var 0) (var 2) (var 3)) :=
  closeUniv 4 (.impI (eta_den_refinement _ _ _ _ Prf.hyp0))
theorem original_compact_cutoff_widths_and_middle_endpoint_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le (var 0) (var 1) ⟶
      ((lowerWidth (var 0) (var 1) (var 2)+middleWidth (var 0) (var 1) (var 2) (var 3)+upperWidth (var 0) (var 1) (var 2) (var 3) ≐ width (var 1) (var 2) (var 3)) ⋏
       (ratio (var 0) (var 1) (var 2)+middleWidth (var 0) (var 1) (var 2) (var 3) ≐ etaDen (var 1) (var 2) (var 3)*top (var 0) (var 2) (var 3)))) :=
  closeUniv 4 (.impI (.andI (widths_total _ _ _ _ Prf.hyp0) (middle_endpoint _ _ _ _ Prf.hyp0)))
theorem original_strict_cutoff_pieces_positive_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((le one (var 2) ⋏ lt (var 0) (var 1)) ⟶
      (le one (lowerWidth (var 0) (var 1) (var 2)) ⋏ (le one (middleWidth (var 0) (var 1) (var 2) (var 3)) ⋏ le one (upperWidth (var 0) (var 1) (var 2) (var 3))))) :=
  closeUniv 4 (.impI (.andI (lower_positive _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂)
    (.andI (middle_positive _ _ _ _) (upper_positive _ _ _ _ Prf.hyp0.andE₂))))
theorem original_equal_cutoff_pieces_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((lowerWidth (var 0) (var 0) (var 1) ≐ zero) ⋏
      ((middleWidth (var 0) (var 0) (var 1) (var 2) ≐ width (var 0) (var 1) (var 2)) ⋏ (upperWidth (var 0) (var 0) (var 1) (var 2) ≐ zero))) :=
  closeUniv 3 (.andI (same_lower _ _) (.andI (same_middle _ _ _) (same_upper _ _ _)))
theorem actual_original_cutoff_geometry_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (run (var 0) (var 1) (var 2) (var 3) ≐ output (var 0) (var 1) (var 2) (var 3)) := closeUniv 4 (program_at _ _ _ _)
theorem actual_returned_original_cutoff_partition_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le (var 0) (var 1) ⟶
      fstT (sndT (run (var 0) (var 1) (var 2) (var 3)))+fstT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3))))+
        sndT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3)))) ≐ width (var 1) (var 2) (var 3)) :=
  closeUniv 4 (.impI (returned_total _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaCompactCutoffGeometry
