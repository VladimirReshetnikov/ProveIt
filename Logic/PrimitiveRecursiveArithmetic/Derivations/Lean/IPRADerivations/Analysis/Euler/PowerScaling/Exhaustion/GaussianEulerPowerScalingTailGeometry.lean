import IPRADerivations.Analysis.Euler.PowerScaling.Observations.GaussianEulerPowerScalingArbitraryObservation

/-!
# Positive affine panel geometry outside enclosing cutoffs

For a tail above the upper cutoff, prepend an interval beginning below
the lower cutoff. For a tail below the lower cutoff, append an interval
ending at the upper cutoff. The enlarged interval and its known piece
both enclose the same prescribed core.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerPowerScalingTailGeometry

open_ipra
open GaussianEulerPowerChartCofinalEndpoints (lowerDenominator upperNumerator)
open GaussianEulerPowerChartCofinalSchedule (cutoffSize cutoff_guards)
open GaussianRationalHorner (positive_product)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def upperPrefix (a D : PTm n) : PTm n := monus (D*a) one
def lowerSuffix (a W E β : PTm n) : PTm n := monus (E*β) (a+W)
def upperPrepared (a W E T D β : PTm n) : Fm PTm n :=
  let C := upperPrefix a D
  le one C ⋏ ((one+C ≐ D*a) ⋏ (le D (D*E) ⋏
    (le (D*E*β) (one+C) ⋏ le (one+(C+D*W)) (T*(D*E)))))
def lowerPrepared (a W E T D β : PTm n) : Fm PTm n :=
  let C := lowerSuffix a W E β
  le one C ⋏ (((a+W)+C ≐ E*β) ⋏ (le (a*D) E ⋏
    le (a+(W+C)) ((T+β)*E)))

private theorem power_from_base (a V L : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hV : Γ ⊢[PRAAx] le two V)
    (hL : Γ ⊢[PRAAx] le one L) : Γ ⊢[PRAAx] le two (pw (a*V) L) := by
  have grow : Γ ⊢[PRAAx] le V (a*V) := le_congr (one_mul V) (.eqRefl _) (mul_le_mul_right V ha)
  have lo := le_trans hV grow
  exact le_trans lo (le_congr (pw_one _) (.eqRefl _)
    (GaussianFactorBudget.power_monotone_length (a*V) one L (le_trans (le_succ_self one) lo) hL))

theorem physical_cutoffs_positive (j A R L S U : PTm n)
    (hL : Γ ⊢[PRAAx] le one L) (hS : Γ ⊢[PRAAx] le one S) (hU : Γ ⊢[PRAAx] le one U) :
    let V := cutoffSize j A R
    Γ ⊢[PRAAx] le two (lowerDenominator S V L) ⋏ le two (upperNumerator U V L) := by
  let V := cutoffSize j A R
  have hV : Γ ⊢[PRAAx] le two V := (cutoff_guards j A R).andE₁
  exact .andI (power_from_base S V L hS hV hL) (power_from_base U V L hU hV hL)

theorem upper_geometry (a W E T D β : PTm n)
    (ha : Γ ⊢[PRAAx] le one a) (he : Γ ⊢[PRAAx] le one E) (hd : Γ ⊢[PRAAx] le two D)
    (hβ : Γ ⊢[PRAAx] le (E*β) a) (hW : Γ ⊢[PRAAx] le (a+W) (T*E)) :
    Γ ⊢[PRAAx] upperPrepared a W E T D β := by
  let C := upperPrefix a D
  have twoA : Γ ⊢[PRAAx] le two (D*a) := le_congr (by ipra_ring) (.eqRefl _)
    (AnalyticNumberTheory.PhiLower.le_mul_mono hd ha)
  have da : Γ ⊢[PRAAx] le one (D*a) := le_trans (le_succ_self one) twoA
  have split : Γ ⊢[PRAAx] one+C ≐ D*a := (eq_add_of_le da).eqSymm
  have pos : Γ ⊢[PRAAx] le one C := GaussianGammaCompactCutoffGeometry.gap_positive one (D*a) twoA
  have begin : Γ ⊢[PRAAx] le D (D*E) := le_congr (one_mul D) (mul_comm E D) (mul_le_mul_right D he)
  have end₁ : Γ ⊢[PRAAx] le (D*E*β) (one+C) := le_congr (by ipra_ring) ((mul_comm a D).eqTrans split.eqSymm)
    (mul_le_mul_right D hβ)
  have end₂ : Γ ⊢[PRAAx] le (one+(C+D*W)) (T*(D*E)) := by
    have eq := natEq split
    have c : Γ ⊢[PRAAx] (a+W)*D ≐ one+(C+D*W) := by
      apply deriveNat
      ipra_simps
      linear_combination -eq
    exact le_congr c (by ipra_ring) (mul_le_mul_right D hW)
  exact .andI pos (.andI split (.andI begin (.andI end₁ end₂)))

theorem lower_geometry (a W E T D β : PTm n)
    (he : Γ ⊢[PRAAx] le one E) (hd : Γ ⊢[PRAAx] le one D) (hβ : Γ ⊢[PRAAx] le two β)
    (hW : Γ ⊢[PRAAx] le ((a+W)*D) E) : Γ ⊢[PRAAx] lowerPrepared a W E T D β := by
  let C := lowerSuffix a W E β
  have pre : Γ ⊢[PRAAx] le (a+W) E := le_trans
    (le_congr (one_mul (a+W)) (mul_comm D (a+W)) (mul_le_mul_right (a+W) hd)) hW
  have suc : Γ ⊢[PRAAx] lt E (E*β) := by
    have row : Γ ⊢[PRAAx] le (E+E) (E*β) :=
      le_congr (by ipra_ring) (mul_comm β E) (mul_le_mul_right E hβ)
    have h : Γ ⊢[PRAAx] one+E ≐ ConciseIPRA.PTm.succ E :=
      (succ_add zero E).eqTrans (congrSucc (zero_add E))
    exact le_congr h (.eqRefl _) (le_trans (add_le_add_right E he) row)
  have widened : Γ ⊢[PRAAx] lt (a+W) (E*β) := lt_of_le_of_lt pre suc
  have finish := (eq_add_of_le (le_of_lt widened)).eqSymm
  have pos : Γ ⊢[PRAAx] le one C := GaussianGammaCompactCutoffGeometry.gap_positive (a+W) (E*β) widened
  have left : Γ ⊢[PRAAx] le (a*D) E := le_trans (mul_le_mul_right D (le_add_right a W)) hW
  have eq : Γ ⊢[PRAAx] a+(W+C) ≐ E*β := (by ipra_ring : Γ ⊢[PRAAx] a+(W+C) ≐ (a+W)+C).eqTrans finish
  have right := le_congr eq.eqSymm (.eqRefl _) (le_congr (mul_comm β E) (.eqRefl _) (mul_le_mul_right E (le_add_left β T)))
  exact .andI pos (.andI finish (.andI left right))

end LeanProofs.IPRA.Analysis.GaussianEulerPowerScalingTailGeometry
