import IPRADerivations.Analysis.Polynomials.RootFinding.GaussianDominantPlateau
import IPRADerivations.Analysis.Polynomials.RootFinding.GaussianDominantRadiusValues

/-!
# The same actual coefficient dominates at three consecutive radii

The checked bounded odd-center search returns a center and coefficient
index. Its two endpoint equalities transfer actual selector maximality
to this same coefficient at the preceding, central and following scales.
The winning coefficient has a genuinely positive decoded squared norm,
derived from the balanced-radius search's actual positive candidate.

The three actual normalized radii are positive and consecutive ones
differ by a factor of four. All numerical data and indices are internal;
the only input is the original positive-constant balanced-radius input.
No dominance, plateau, search-success or monotonicity law is supplied.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianDominantPlateauValues

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianBalancedRadiusSyntax (input subst_input)
open LeanProofs.IPRA.Analysis.GaussianDominantPlateau (center winner)
open LeanProofs.IPRA.Analysis.GaussianDominantRadiusValues (radius dominates)
open LeanProofs.IPRA.Analysis.GaussianEuclideanDistanceName (fraction)
open LeanProofs.IPRA.Analysis.GaussianDominantSyntax (four)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def rawNumerator (C N : PTm n) : PTm n :=
  GaussianBalancedRadiusSyntax.numerator C N (winner C N)
def scaledNumerator (C N : PTm n) : PTm n :=
  GaussianDominantSyntax.numerator C N (GaussianBalancedRadiusSearch.radiusIndex C N) (winner C N)

@[simp] theorem subst_rawNumerator {m : ℕ} (σ : Fin n → PTm m) (C N : PTm n) :
    Syn.subst σ (rawNumerator C N) = rawNumerator (Syn.subst σ C) (Syn.subst σ N) := by simp [rawNumerator]
@[simp] theorem subst_scaledNumerator {m : ℕ} (σ : Fin n → PTm m) (C N : PTm n) :
    Syn.subst σ (scaledNumerator C N) = scaledNumerator (Syn.subst σ C) (Syn.subst σ N) := by simp [scaledNumerator]

theorem left_selected_eq (C N : PTm n) (hInput : Γ ⊢[PRAAx] input C N) : Γ ⊢[PRAAx]
    GaussianDominantSelector.index C N (pred (center C N)) ≐ winner C N :=
  (GaussianDominantSelector.index_congr C N (GaussianDominantPlateau.before_center C N)).eqTrans
    (Prf.andE₁ (GaussianDominantPlateau.triple_indices C N hInput))

theorem right_selected_eq (C N : PTm n) (hInput : Γ ⊢[PRAAx] input C N) : Γ ⊢[PRAAx]
    GaussianDominantSelector.index C N (succ (center C N)) ≐ winner C N :=
  (Prf.andE₂ (GaussianDominantPlateau.triple_indices C N hInput)).eqSymm

theorem winner_raw_positive (C N : PTm n) (hInput : Γ ⊢[PRAAx] input C N) : Γ ⊢[PRAAx]
    le one (rawNumerator C N) :=
  GaussianDominantSelector.index_positive C N (center C N) hInput

theorem winner_scaled_positive (C N : PTm n) (hInput : Γ ⊢[PRAAx] input C N) : Γ ⊢[PRAAx]
    le one (scaledNumerator C N) :=
  GaussianDominantSyntax.numerator_positive C N (GaussianBalancedRadiusSearch.radiusIndex C N) (winner C N)
    (winner_raw_positive C N hInput)

theorem left_dominates (C N : PTm n) (hInput : Γ ⊢[PRAAx] input C N) : Γ ⊢[PRAAx]
    dominates C N (pred (center C N)) (winner C N) :=
  GaussianDominantRadiusValues.dominates_congr C N (pred (center C N)) (left_selected_eq C N hInput)
    (GaussianDominantRadiusValues.selected_dominates C N (pred (center C N)) hInput)

theorem center_dominates (C N : PTm n) (hInput : Γ ⊢[PRAAx] input C N) : Γ ⊢[PRAAx]
    dominates C N (center C N) (winner C N) :=
  GaussianDominantRadiusValues.selected_dominates C N (center C N) hInput

theorem right_dominates (C N : PTm n) (hInput : Γ ⊢[PRAAx] input C N) : Γ ⊢[PRAAx]
    dominates C N (succ (center C N)) (winner C N) :=
  GaussianDominantRadiusValues.dominates_congr C N (succ (center C N)) (right_selected_eq C N hInput)
    (GaussianDominantRadiusValues.selected_dominates C N (succ (center C N)) hInput)

def three_scale (C N : PTm n) : Fm PTm n :=
  dominates C N (pred (center C N)) (winner C N) ⋏
    (dominates C N (center C N) (winner C N) ⋏ dominates C N (succ (center C N)) (winner C N))

@[simp] theorem subst_three_scale {m : ℕ} (σ : Fin n → PTm m) (C N : PTm n) :
    (three_scale C N).subst σ = three_scale (Syn.subst σ C) (Syn.subst σ N) := by simp [three_scale]

theorem three_scale_dominance (C N : PTm n) (hInput : Γ ⊢[PRAAx] input C N) : Γ ⊢[PRAAx]
    three_scale C N := .andI (left_dominates C N hInput)
      (.andI (center_dominates C N hInput) (right_dominates C N hInput))

/-- Structural radius congruence preserves the actual normalized fraction
and avoids expanding the reified radius program. -/
theorem radius_congr (C N : PTm n) {h l : PTm n} (hh : Γ ⊢[PRAAx] h ≐ l) : Γ ⊢[PRAAx]
    radius C N h ≐ radius C N l :=
  RationalNonnegativePowers.fraction_congr (.eqRefl _)
    (congrAp2 powF (congrAdd (.eqRefl _) (congrMul (.eqRefl two) hh)) (.eqRefl two))

theorem center_succ_pred (C N : PTm n) : Γ ⊢[PRAAx] succ (pred (center C N)) ≐ center C N :=
  congrSucc (GaussianDominantPlateau.before_center C N)

theorem left_quarter_radius (C N : PTm n) : Γ ⊢[PRAAx]
    RationalArithmetic.multiply (radius C N (center C N)) (fraction four one) ≐ radius C N (pred (center C N)) :=
  (RationalAlgebra.multiply_congr (radius_congr C N (center_succ_pred C N)).eqSymm (.eqRefl _)).eqTrans
    (GaussianDominantRadiusValues.quarter_radius C N (pred (center C N)))

theorem right_quarter_radius (C N : PTm n) : Γ ⊢[PRAAx]
    RationalArithmetic.multiply (radius C N (succ (center C N))) (fraction four one) ≐ radius C N (center C N) :=
  GaussianDominantRadiusValues.quarter_radius C N (center C N)

def radiusFacts (C N : PTm n) : Fm PTm n :=
  neg (RationalArgmin.rationalLE (radius C N (pred (center C N))) (fraction zero one)) ⋏
    (neg (RationalArgmin.rationalLE (radius C N (center C N)) (fraction zero one)) ⋏
      (neg (RationalArgmin.rationalLE (radius C N (succ (center C N))) (fraction zero one)) ⋏
        ((RationalArithmetic.multiply (radius C N (center C N)) (fraction four one) ≐ radius C N (pred (center C N))) ⋏
          (RationalArithmetic.multiply (radius C N (succ (center C N))) (fraction four one) ≐ radius C N (center C N)))))

@[simp] theorem subst_radiusFacts {m : ℕ} (σ : Fin n → PTm m) (C N : PTm n) :
    (radiusFacts C N).subst σ = radiusFacts (Syn.subst σ C) (Syn.subst σ N) := by simp [radiusFacts]

theorem radius_facts (C N : PTm n) : Γ ⊢[PRAAx] radiusFacts C N :=
  .andI (GaussianDominantRadiusValues.radius_positive C N (pred (center C N)))
    (.andI (GaussianDominantRadiusValues.radius_positive C N (center C N))
      (.andI (GaussianDominantRadiusValues.radius_positive C N (succ (center C N)))
        (.andI (left_quarter_radius C N) (right_quarter_radius C N))))

def certificate (C N : PTm n) : Fm PTm n :=
  GaussianDominantPlateau.certificate C N ⋏
    (le one (rawNumerator C N) ⋏ (le one (scaledNumerator C N) ⋏ (three_scale C N ⋏ radiusFacts C N)))

@[simp] theorem subst_certificate {m : ℕ} (σ : Fin n → PTm m) (C N : PTm n) :
    (certificate C N).subst σ = certificate (Syn.subst σ C) (Syn.subst σ N) := by simp [certificate]

theorem plateau_correct (C N : PTm n) (hInput : Γ ⊢[PRAAx] input C N) : Γ ⊢[PRAAx] certificate C N :=
  .andI (GaussianDominantPlateau.plateau_correct C N hInput)
    (.andI (winner_raw_positive C N hInput) (.andI (winner_scaled_positive C N hInput)
      (.andI (three_scale_dominance C N hInput) (radius_facts C N))))

/-! Actual PR2 output: center, winning coefficient, preceding radius,
central radius, and following radius. -/
def output (C N : PTm n) : PTm n := pairT (center C N) (pairT (winner C N)
  (pairT (radius C N (pred (center C N)))
    (pairT (radius C N (center C N)) (radius C N (succ (center C N))))))
def outputF : PR 2 := PTm.toPR (output (var 0) (var 1))
def run (C N : PTm n) : PTm n := ap2 outputF C N

@[simp] theorem subst_output {m : ℕ} (σ : Fin n → PTm m) (C N : PTm n) :
    Syn.subst σ (output C N) = output (Syn.subst σ C) (Syn.subst σ N) := by simp [output]
@[simp] theorem subst_run {m : ℕ} (σ : Fin n → PTm m) (C N : PTm n) :
    Syn.subst σ (run C N) = run (Syn.subst σ C) (Syn.subst σ N) := by simp [run]

theorem program_at (C N : PTm n) : Γ ⊢[PRAAx] run C N ≐ output C N := by
  simpa [run,outputF,ap2] using toPR_eq (Γ := Γ) (output (var 0) (var 1) : PTm 2) ![C,N]

theorem returned_center (C N : PTm n) : Γ ⊢[PRAAx] fstT (run C N) ≐ center C N :=
  (congrFst (program_at C N)).eqTrans (fst_pair _ _)
theorem returned_winner (C N : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run C N)) ≐ winner C N :=
  (congrFst ((congrSnd (program_at C N)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_left_radius (C N : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run C N))) ≐ radius C N (pred (center C N)) :=
  (congrFst ((congrSnd ((congrSnd (program_at C N)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_center_radius (C N : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (sndT (run C N)))) ≐ radius C N (center C N) :=
  (congrFst ((congrSnd ((congrSnd ((congrSnd (program_at C N)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_right_radius (C N : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (sndT (run C N)))) ≐ radius C N (succ (center C N)) :=
  (congrSnd ((congrSnd ((congrSnd ((congrSnd (program_at C N)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _)

theorem actual_three_scale_dominance_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (input (var 0) (var 1) ⟶ three_scale (var 0) (var 1)) :=
  closeUniv 2 (.impI (three_scale_dominance _ _ Prf.hyp0))

theorem positive_dominant_winner_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (input (var 0) (var 1) ⟶ (le one (rawNumerator (var 0) (var 1)) ⋏ le one (scaledNumerator (var 0) (var 1)))) :=
  closeUniv 2 (.impI (.andI (winner_raw_positive _ _ Prf.hyp0) (winner_scaled_positive _ _ Prf.hyp0)))

theorem actual_three_radii_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 (radiusFacts (var 0) (var 1)) :=
  closeUniv 2 (radius_facts _ _)

theorem dominant_plateau_values_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (input (var 0) (var 1) ⟶ certificate (var 0) (var 1)) :=
  closeUniv 2 (.impI (plateau_correct _ _ Prf.hyp0))

theorem actual_plateau_values_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    ((run (var 0) (var 1) ≐ output (var 0) (var 1)) ⋏
      ((fstT (run (var 0) (var 1)) ≐ center (var 0) (var 1)) ⋏
        ((fstT (sndT (run (var 0) (var 1))) ≐ winner (var 0) (var 1)) ⋏
          ((fstT (sndT (sndT (run (var 0) (var 1)))) ≐ radius (var 0) (var 1) (pred (center (var 0) (var 1)))) ⋏
            ((fstT (sndT (sndT (sndT (run (var 0) (var 1))))) ≐ radius (var 0) (var 1) (center (var 0) (var 1))) ⋏
              sndT (sndT (sndT (sndT (run (var 0) (var 1))))) ≐ radius (var 0) (var 1) (succ (center (var 0) (var 1)))))))) :=
  closeUniv 2 (.andI (program_at _ _) (.andI (returned_center _ _) (.andI (returned_winner _ _)
    (.andI (returned_left_radius _ _) (.andI (returned_center_radius _ _) (returned_right_radius _ _))))))

end LeanProofs.IPRA.Analysis.GaussianDominantPlateauValues
