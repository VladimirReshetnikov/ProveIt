import IPRADerivations.Analysis.Polynomials.RootFinding.BalancedRadius.GaussianTranslatedBalancedRadius
import IPRADerivations.Analysis.Polynomials.RootFinding.DominantTerms.DominantBounds.GaussianDominantPlateauValues

/-!
# Actual dominant plateau from the original monic polynomial and point

The original descending coefficient list, numerical degree and original
Gaussian-rational point determine the translated list and its three-scale
dominant term. Monicity derives nonconstancy. A positive original residual
then derives every input condition for the actual plateau program; the
zero branch retains the already proved literal zero starting radius.
No translated list, height, maxima, monotonicity, positive count, successful
search or plateau certificate is supplied. Every numerical input remains
internal. Direction selection and the full contraction are separate.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianTranslatedDominantPlateau

open_ipra
open LeanProofs.IPRA.Analysis.GaussianRationalTranslation (translated subst_translated)
open LeanProofs.IPRA.Analysis.GaussianTranslatedBalancedRadius (inputContract residual subst_inputContract subst_residual)
open LeanProofs.IPRA.Analysis.GaussianEuclideanDistanceName (fraction)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- The positive constant-norm guard for the actual translated polynomial
is derived from the original evaluated residual. -/
theorem positive_input (C N z : PTm n) (h : Γ ⊢[PRAAx] inputContract C N)
    (hPositive : Γ ⊢[PRAAx] le one (residual C z)) : Γ ⊢[PRAAx]
    GaussianBalancedRadiusSyntax.input (translated C N z) N :=
  GaussianBalancedRadius.positive_input _ _ (GaussianTranslatedBalancedRadius.radius_input C N z h)
    (le_congr (.eqRefl _) (GaussianTranslatedBalancedRadius.residual_identity C N z).eqSymm hPositive)

theorem positive_plateau (C N z : PTm n) (h : Γ ⊢[PRAAx] inputContract C N)
    (hPositive : Γ ⊢[PRAAx] le one (residual C z)) : Γ ⊢[PRAAx]
    GaussianDominantPlateauValues.certificate (translated C N z) N :=
  GaussianDominantPlateauValues.plateau_correct _ _ (positive_input C N z h hPositive)

theorem zero_radius (C N z : PTm n) (hZero : Γ ⊢[PRAAx] residual C z ≐ zero) : Γ ⊢[PRAAx]
    GaussianTranslatedBalancedRadius.radius C N z ≐ fraction zero one :=
  GaussianTranslatedBalancedRadius.zero_radius C N z hZero

def certificate (C N z : PTm n) : Fm PTm n :=
  GaussianTranslatedBalancedRadius.certificate C N z ⋏
    ((residual C z ≐ zero ⟶ GaussianTranslatedBalancedRadius.radius C N z ≐ fraction zero one) ⋏
      (le one (residual C z) ⟶ GaussianDominantPlateauValues.certificate (translated C N z) N))

ipra_subst certificate

theorem translated_dominant_plateau (C N z : PTm n) (h : Γ ⊢[PRAAx] inputContract C N) : Γ ⊢[PRAAx]
    certificate C N z :=
  .andI (GaussianTranslatedBalancedRadius.translated_balanced_radius C N z h)
    (.andI (.impI (zero_radius C N z Prf.hyp0)) (.impI (positive_plateau C N z h.wk Prf.hyp0)))

/-! The actual PR3 output contains the constructed translated polynomial
and the literal five-field plateau/radius output for that polynomial. -/
def output (C N z : PTm n) : PTm n :=
  pairT (translated C N z) (GaussianDominantPlateauValues.run (translated C N z) N)
def outputF : PR 3 := PTm.toPR (output (var 0) (var 1) (var 2))
def run (C N z : PTm n) : PTm n := ap3 outputF C N z

ipra_subst output
ipra_subst run

theorem program_at (C N z : PTm n) : Γ ⊢[PRAAx] run C N z ≐ output C N z := by
  simpa [run,outputF,ap3] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) : PTm 3) ![C,N,z]

theorem returned_polynomial (C N z : PTm n) : Γ ⊢[PRAAx] fstT (run C N z) ≐ translated C N z :=
  (program_at C N z).fstE

theorem returned_values (C N z : PTm n) : Γ ⊢[PRAAx]
    sndT (run C N z) ≐ GaussianDominantPlateauValues.run (translated C N z) N :=
  (program_at C N z).sndE

theorem returned_center (C N z : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (run C N z)) ≐ GaussianDominantPlateau.center (translated C N z) N :=
  (congrFst (returned_values C N z)).eqTrans (GaussianDominantPlateauValues.returned_center _ _)

theorem returned_winner (C N z : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (sndT (run C N z))) ≐ GaussianDominantPlateau.winner (translated C N z) N :=
  (congrFst (congrSnd (returned_values C N z))).eqTrans (GaussianDominantPlateauValues.returned_winner _ _)

theorem returned_left_radius (C N z : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (sndT (sndT (run C N z)))) ≐ GaussianDominantRadiusValues.radius (translated C N z) N
      (PTm.pred (GaussianDominantPlateau.center (translated C N z) N)) :=
  (congrFst (congrSnd (congrSnd (returned_values C N z)))).eqTrans
    (GaussianDominantPlateauValues.returned_left_radius _ _)

theorem returned_center_radius (C N z : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (sndT (sndT (sndT (run C N z))))) ≐ GaussianDominantRadiusValues.radius (translated C N z) N
      (GaussianDominantPlateau.center (translated C N z) N) :=
  (congrFst (congrSnd (congrSnd (congrSnd (returned_values C N z))))).eqTrans
    (GaussianDominantPlateauValues.returned_center_radius _ _)

theorem returned_right_radius (C N z : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (sndT (sndT (sndT (run C N z))))) ≐ GaussianDominantRadiusValues.radius (translated C N z) N
      (succ (GaussianDominantPlateau.center (translated C N z) N)) :=
  (congrSnd (congrSnd (congrSnd (congrSnd (returned_values C N z))))).eqTrans
    (GaussianDominantPlateauValues.returned_right_radius _ _)

theorem returned_positive_certificate (C N z : PTm n) (h : Γ ⊢[PRAAx] inputContract C N)
    (hPositive : Γ ⊢[PRAAx] le one (residual C z)) : Γ ⊢[PRAAx]
    GaussianDominantPlateauValues.certificate (fstT (run C N z)) N := by
  have p := Prf.eqSubst (Ax := PRAAx) (Γ := Γ)
    (GaussianDominantPlateauValues.certificate (var 0) (var 1) : Fm PTm 2)
    ![translated C N z,N] ![fstT (run C N z),N]
    (fun i => by fin_cases i; exact (returned_polynomial C N z).eqSymm; exact .eqRefl _)
    (by simpa using positive_plateau C N z h hPositive)
  simpa using p

theorem translated_positive_input_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (inputContract (var 0) (var 1) ⟶ le one (residual (var 0) (var 2)) ⟶
      GaussianBalancedRadiusSyntax.input (translated (var 0) (var 1) (var 2)) (var 1)) :=
  closeUniv 3 (.impI (.impI (positive_input _ _ _ Prf.hyp1 Prf.hyp0)))

theorem translated_dominant_plateau_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (inputContract (var 0) (var 1) ⟶ certificate (var 0) (var 1) (var 2)) :=
  closeUniv 3 (.impI (translated_dominant_plateau _ _ _ Prf.hyp0))

theorem translated_plateau_zero_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (residual (var 0) (var 2) ≐ zero ⟶
      GaussianTranslatedBalancedRadius.radius (var 0) (var 1) (var 2) ≐ fraction zero one) :=
  closeUniv 3 (.impI (zero_radius _ _ _ Prf.hyp0))

theorem translated_plateau_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((run (var 0) (var 1) (var 2) ≐ output (var 0) (var 1) (var 2)) ⋏
      ((fstT (run (var 0) (var 1) (var 2)) ≐ translated (var 0) (var 1) (var 2)) ⋏
        sndT (run (var 0) (var 1) (var 2)) ≐ GaussianDominantPlateauValues.run
          (translated (var 0) (var 1) (var 2)) (var 1))) :=
  closeUniv 3 (.andI (program_at _ _ _) (.andI (returned_polynomial _ _ _) (returned_values _ _ _)))

theorem translated_returned_plateau_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (inputContract (var 0) (var 1) ⟶ le one (residual (var 0) (var 2)) ⟶
      GaussianDominantPlateauValues.certificate (fstT (run (var 0) (var 1) (var 2))) (var 1)) :=
  closeUniv 3 (.impI (.impI (returned_positive_certificate _ _ _ Prf.hyp1 Prf.hyp0)))

theorem translated_plateau_fields_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((fstT (sndT (run (var 0) (var 1) (var 2))) ≐
        GaussianDominantPlateau.center (translated (var 0) (var 1) (var 2)) (var 1)) ⋏
      ((fstT (sndT (sndT (run (var 0) (var 1) (var 2)))) ≐
        GaussianDominantPlateau.winner (translated (var 0) (var 1) (var 2)) (var 1)) ⋏
      ((fstT (sndT (sndT (sndT (run (var 0) (var 1) (var 2))))) ≐
        GaussianDominantRadiusValues.radius (translated (var 0) (var 1) (var 2)) (var 1)
          (PTm.pred (GaussianDominantPlateau.center (translated (var 0) (var 1) (var 2)) (var 1)))) ⋏
      ((fstT (sndT (sndT (sndT (sndT (run (var 0) (var 1) (var 2)))))) ≐
        GaussianDominantRadiusValues.radius (translated (var 0) (var 1) (var 2)) (var 1)
          (GaussianDominantPlateau.center (translated (var 0) (var 1) (var 2)) (var 1))) ⋏
       sndT (sndT (sndT (sndT (sndT (run (var 0) (var 1) (var 2)))))) ≐
        GaussianDominantRadiusValues.radius (translated (var 0) (var 1) (var 2)) (var 1)
          (succ (GaussianDominantPlateau.center (translated (var 0) (var 1) (var 2)) (var 1))))))) :=
  closeUniv 3 (.andI (returned_center _ _ _) (.andI (returned_winner _ _ _)
    (.andI (returned_left_radius _ _ _) (.andI (returned_center_radius _ _ _) (returned_right_radius _ _ _)))))

end LeanProofs.IPRA.Analysis.GaussianTranslatedDominantPlateau
