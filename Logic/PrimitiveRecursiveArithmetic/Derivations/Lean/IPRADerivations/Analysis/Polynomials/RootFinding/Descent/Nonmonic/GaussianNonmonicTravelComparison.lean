import IPRADerivations.Analysis.Polynomials.RootFinding.Descent.Nonmonic.GaussianNonmonicTravelCoefficientBound

/-!
# Normalized rational certificate for the actual travel coefficient bound

The native coefficient/radius theorem is transported to the literal
normalized scalar operations. Its original coefficient lower bound also
supplies nonconstancy. A fixed PR7 returns the actual selected index,
starting radius and both rational comparison codes. All numerical data
remain internal, including the original
positive-degree apartness witness. No desired comparison is an input.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianNonmonicTravelComparison

open_ipra
open LeanProofs.IPRA.Analysis.GaussianNonmonicTravelCoefficientBound
  (selectedIndex weight radius radiusNumerator radiusDenominator lowerBound combined)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (positive_product evaluate)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (qnormSq squaredTolerance)
open LeanProofs.IPRA.Analysis.GaussianDescentClock (residualNumerator residualDenominator)
open LeanProofs.IPRA.Analysis.GaussianEuclideanDistanceName (fraction fraction_represents)
open LeanProofs.IPRA.Analysis.RationalArithmetic (multiply)
open LeanProofs.IPRA.Analysis.RationalArgmin (rationalLE)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def input (C N z A B k L M : PTm n) : Fm PTm n := GaussianTranslationCoefficientBound.input C N z A B ⋏
  (le one k ⋏ (le k N ⋏ (le one L ⋏ (le one M ⋏ lowerBound C N k L M))))
def left (C N z A B L M : PTm n) : PTm n := multiply (squaredTolerance L M)
  (RationalNonnegativePowers.power (radiusNumerator C N z) (radiusDenominator C N z) (two*selectedIndex C N z A B))
def right (C N z A B : PTm n) : PTm n := multiply (fraction (weight N*weight N) one)
  (multiply (qnormSq (evaluate C z)) (RationalNonnegativePowers.power A B (two*selectedIndex C N z A B)))
def comparison (C N z A B L M : PTm n) : Fm PTm n := rationalLE (left C N z A B L M) (right C N z A B)

ipra_subst input
ipra_subst left
ipra_subst right
ipra_subst comparison

theorem native_bound (C N z A B k L M : PTm n) (h : Γ ⊢[PRAAx] input C N z A B k L M) :
    Γ ⊢[PRAAx] combined C N z A B L M :=
  GaussianNonmonicTravelCoefficientBound.coefficient_radius_bound C N z A B k L M (Prf.andE₁ h)
    (Prf.andE₁ (Prf.andE₂ h)) (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ h)))
    (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ h))))
    (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ h)))))
    (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ h)))))

theorem original_nonconstant (C N z A B k L M : PTm n) (h : Γ ⊢[PRAAx] input C N z A B k L M) :
    Γ ⊢[PRAAx] GaussianBalancedRadiusSyntax.nonconstant C N :=
  GaussianNonmonicTravelCoefficientBound.original_nonconstant C N k L M
    (Prf.andE₁ (Prf.andE₂ h)) (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ h)))
    (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ h))))
    (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ h)))))
    (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ h)))))

theorem left_represents (C N z A B L M : PTm n) (hM : Γ ⊢[PRAAx] le one M) : Γ ⊢[PRAAx]
    RationalArithmetic.represents (left C N z A B L M)
      (ZT.ofNat (L*L*pw (radiusNumerator C N z) (two*selectedIndex C N z A B)))
      (M*M*pw (radiusDenominator C N z) (two*selectedIndex C N z A B)) := by
  have rep := RationalRepresentations.represents_multiply (Γ := Γ) _ _ _ _ _ _
    (GaussianRationalMetric.squared_tolerance_represents L M hM)
    (RationalNonnegativePowers.power_represents (radiusNumerator C N z) (radiusDenominator C N z)
      (two*selectedIndex C N z A B) (GaussianNonmonicTravelCoefficientBound.radius_denominator_positive C N z))
  apply GaussianRationalHorner.scalar_congr (.eqRefl _) (hAB := .eqRefl _) (h := rep)
  apply ZT.derive
  simp only [ZT.toZ_mul,ZT.toZ_ofNat]
  ipra_simps

theorem right_represents (C N z A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    RationalArithmetic.represents (right C N z A B)
      (ZT.ofNat (weight N*weight N*residualNumerator C z*pw A (two*selectedIndex C N z A B)))
      ((residualDenominator C z*residualDenominator C z)*pw B (two*selectedIndex C N z A B)) := by
  have value := GaussianRationalMetric.qnormSq_represents (Γ := Γ) _ _ _
    (GaussianDescentClock.residual_denominator_positive C z) (GaussianDescentClock.value_represents (evaluate C z))
  have powerValue := RationalNonnegativePowers.power_represents (Γ := Γ) A B (two*selectedIndex C N z A B) hB
  have rep := RationalRepresentations.represents_multiply (Γ := Γ) _ _ _ _ _ _
    (fraction_represents (weight N*weight N) one (le_refl one))
    (RationalRepresentations.represents_multiply _ _ _ _ _ _ value powerValue)
  apply GaussianRationalHorner.scalar_congr (.eqRefl _) (hAB := one_mul _) (h := rep)
  apply ZT.derive
  simp only [ZT.toZ_mul,ZT.toZ_ofNat]
  unfold GaussianDescentClock.residualNumerator
  ipra_simps
  ring

theorem comparison_of_native (C N z A B L M : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hM : Γ ⊢[PRAAx] le one M) (h : Γ ⊢[PRAAx] combined C N z A B L M) : Γ ⊢[PRAAx]
    comparison C N z A B L M := by
  apply GaussianRationalMetric.comparison_of_cleared _ _ _ _ _ _
    (positive_product _ _ (positive_product M M hM hM)
      (RationalNonnegativePowers.denominator_positive _ _ (GaussianNonmonicTravelCoefficientBound.radius_denominator_positive C N z)))
    (positive_product _ _ (positive_product _ _ (GaussianDescentClock.residual_denominator_positive C z)
      (GaussianDescentClock.residual_denominator_positive C z)) (RationalNonnegativePowers.denominator_positive B _ hB))
    (left_represents C N z A B L M hM) (right_represents C N z A B hB)
  apply le_congr (h := h)
  · apply deriveNat
    have e := natEq (GaussianProductStability.power_product (Γ := Γ) (radiusNumerator C N z) B (two*selectedIndex C N z A B))
    ipra_simps
    rw [e]
    ring
  · apply deriveNat
    have e := natEq (GaussianProductStability.power_product (Γ := Γ) (radiusDenominator C N z) A (two*selectedIndex C N z A B))
    ipra_simps
    rw [e]
    ring

theorem normalized_bound (C N z A B k L M : PTm n) (h : Γ ⊢[PRAAx] input C N z A B k L M) :
    Γ ⊢[PRAAx] comparison C N z A B L M :=
  comparison_of_native C N z A B L M (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ (Prf.andE₁ h))))
    (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ h))))) (native_bound C N z A B k L M h)

def output (C N z A B L M : PTm n) : PTm n := pairT (selectedIndex C N z A B)
  (pairT (radius C N z) (pairT (left C N z A B L M) (right C N z A B)))
def outputF : PR 7 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))
def run (C N z A B L M : PTm n) : PTm n := PTm.app outputF ![C,N,z,A,B,L,M]
ipra_subst output
ipra_subst run

theorem program_at (C N z A B L M : PTm n) : Γ ⊢[PRAAx] run C N z A B L M ≐ output C N z A B L M := by
  simpa [run,outputF] using toPR_eq (Γ := Γ)
    (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) : PTm 7) ![C,N,z,A,B,L,M]
theorem returned_index (C N z A B L M : PTm n) : Γ ⊢[PRAAx] fstT (run C N z A B L M) ≐ selectedIndex C N z A B :=
  (program_at C N z A B L M).fstE
theorem returned_radius (C N z A B L M : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run C N z A B L M)) ≐ radius C N z :=
  ((congrFst (congrSnd (program_at C N z A B L M))).eqTrans (congrFst (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_left (C N z A B L M : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (sndT (run C N z A B L M))) ≐ left C N z A B L M :=
  ((congrFst (congrSnd (congrSnd (program_at C N z A B L M)))).eqTrans
    ((congrFst (congrSnd (snd_pair _ _))).eqTrans (congrFst (snd_pair _ _)))).eqTrans (fst_pair _ _)
theorem returned_right (C N z A B L M : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (sndT (run C N z A B L M))) ≐ right C N z A B :=
  ((congrSnd (congrSnd (congrSnd (program_at C N z A B L M)))).eqTrans
    ((congrSnd (congrSnd (snd_pair _ _))).eqTrans (congrSnd (snd_pair _ _)))).eqTrans (snd_pair _ _)

theorem returned_bound (C N z A B k L M : PTm n) (h : Γ ⊢[PRAAx] input C N z A B k L M) : Γ ⊢[PRAAx]
    rationalLE (fstT (sndT (sndT (run C N z A B L M)))) (sndT (sndT (sndT (run C N z A B L M)))) :=
  RationalArgmin.rationalLE_congr (returned_left C N z A B L M).eqSymm (returned_right C N z A B L M).eqSymm
    (normalized_bound C N z A B k L M h)

theorem native_coefficient_radius_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ⟶
      combined (var 0) (var 1) (var 2) (var 3) (var 4) (var 6) (var 7)) :=
  closeUniv 8 (.impI (native_bound _ _ _ _ _ _ _ _ Prf.hyp0))
theorem normalized_coefficient_radius_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ⟶
      comparison (var 0) (var 1) (var 2) (var 3) (var 4) (var 6) (var 7)) :=
  closeUniv 8 (.impI (normalized_bound _ _ _ _ _ _ _ _ Prf.hyp0))
theorem original_coefficient_nonconstant_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ⟶
      GaussianBalancedRadiusSyntax.nonconstant (var 0) (var 1)) :=
  closeUniv 8 (.impI (original_nonconstant _ _ _ _ _ _ _ _ Prf.hyp0))
theorem actual_travel_comparison_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ≐
      output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)) :=
  closeUniv 7 (program_at _ _ _ _ _ _ _)
theorem returned_travel_comparison_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ⟶
      rationalLE (fstT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 6) (var 7)))))
        (sndT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 6) (var 7)))))) :=
  closeUniv 8 (.impI (returned_bound _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianNonmonicTravelComparison
