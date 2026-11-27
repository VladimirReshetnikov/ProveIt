import IPRADerivations.Analysis.Barnes.FunctionalEquations.Duplication.GaussianBarnesCanonicalDuplicationNormalizerCoefficients
import IPRADerivations.Analysis.Barnes.FunctionalEquations.Hyperfactorial.Recurrence.GaussianBarnesCanonicalHyperfactorialRecurrence

/-!
# The actual Barnes duplication normalizer absorbs the Gauss factor

The two exponential names in the normalizer use the original positive
rational logarithm of one half and the original real logarithm of Gamma
at one half. At a half step the normalizer absorbs the actual scale
factor from the original Gamma duplication theorem.
-/

set_option autoImplicit false
set_option maxHeartbeats 1300000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalDuplicationNormalizer

open_ipra
open GaussianBarnesCanonicalDuplicationNormalizerCoefficients
  (quadraticWeight linearWeight quadratic_weight_step linear_weight_step)
open GaussianBarnesCanonicalHyperfactorialRecurrence (regroup)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaFiniteApproximantName (exponentialInputData exponential_input)
open GaussianGaussMultiplicationHalfPower (ratioPowerF ratioPowerData ratio_power_regular ratio_power_sum coefficient_congr)
open GaussianGaussMultiplicationPowerPerturbation (limitData)
open GaussianGaussMultiplicationPowerRate (powerF multiplier)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNameRingLaws (oneF one_fast one_at multiply_commutative)
open GaussianNamedGammaHalfShift (add_cross constant_sum)
open GaussianRationalHorner (positive_product)
open GaussianRationalSyntheticDivision (qone)
open GaussianStirlingGammaLogarithm (source arg gammaData gamma_regular native_disk)
open GaussianStirlingNames (logGammaF logGammaData log_gamma_regular)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "G" => GaussianGammaReciprocalInverse.gammaF
local notation "E" => GaussianRadiusExponentialName.nameF
local notation "Ed" => exponentialInputData
local notation "C" => constantF
local notation "M" => multiplyF
local notation "Md" => multiplyData
local notation "L" => logGammaF

abbrev quadraticF : PR 2 := ratioPowerF
def quadraticData (A B : PTm n) : PTm n := ratioPowerData (quadraticWeight A B) two
abbrev linearExponentF : PR 2 := M C L
def logHalfData : PTm n := logGammaData one two
def linearExponentData (w : PTm n) : PTm n := Md C L w logHalfData
abbrev linearF : PR 2 := E linearExponentF
def linearData (A B : PTm n) : PTm n := Ed linearExponentF (linearExponentData (linearWeight A B))
abbrev nameF : PR 2 := M quadraticF linearF
def data (A B : PTm n) : PTm n := Md quadraticF linearF (quadraticData A B) (linearData A B)

abbrev factorF : PR 2 := M powerF G
def factorData (A B : PTm n) : PTm n :=
  Md powerF G (limitData (arg A) A (two*B) two) (gammaData one two)

private theorem half_source : Γ ⊢[PRAAx] source (one : PTm n) two :=
  .andI (le_refl one) (le_succ_self one)

private theorem log_half_regular : Γ ⊢[PRAAx] pointCN L (logHalfData : PTm n) :=
  log_gamma_regular one two half_source

theorem regular (A B : PTm n) : Γ ⊢[PRAAx] pointCN nameF (data A B) :=
  multiply_fast _ _ _ _
    (ratio_power_regular (quadraticWeight A B) two (le_succ_self one))
    (GaussianStirlingLogDuplication.exponential_regular linearExponentF _
      (multiply_fast C L _ _ (constant_regular _) log_half_regular))

private theorem unit_constant (x : PTm n) : Γ ⊢[PRAAx] crossEquivalent C oneF qone x :=
  GaussianNameRingLaws.constant_one_cross x

theorem linear_step (A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] crossEquivalent (M G linearF) linearF
      (Md G linearF (gammaData one two) (linearData (A+B) B)) (linearData A B) := by
  let x : PTm n := logHalfData
  let a := linearWeight (A+B) B
  let b := linearWeight A B
  let u := linearExponentData a
  let v := linearExponentData b
  have hx : Γ ⊢[PRAAx] pointCN L x := log_half_regular
  have ha := constant_regular (Γ := Γ) a
  have hb := constant_regular (Γ := Γ) b
  have h1 := constant_regular (Γ := Γ) (qone : PTm n)
  have hu := multiply_fast C L a x ha hx
  have hv := multiply_fast C L b x hb hx
  have unit := multiply_cross C oneF L L qone x x x h1 (one_fast x) hx hx
    (unit_constant x) (cross_refl _ _ hx)
  have unit' := cross_trans _ _ _ _ _ _ unit (GaussianNameRingLaws.multiply_one_left L x hx)
  have insert := add_cross linearExponentF linearExponentF L linearExponentF u u x (Md C L qone x)
    hu hu hx (multiply_fast C L _ _ h1 hx) (cross_refl _ _ hu) (cross_symm _ _ _ _ unit')
  have collect := cross_symm _ _ _ _ (GaussianNameRingLaws.right_distributive C C L a qone x ha h1 hx)
  have combine := multiply_cross (addF C C) C L L (addData a qone) b x x
    (add_fast _ _ _ _ ha h1) hb hx hx
    (constant_sum a qone b (linear_weight_step A B hB)) (cross_refl _ _ hx)
  have sum := cross_trans _ _ _ _ _ _ insert (cross_trans _ _ _ _ _ _ collect combine)
  have last := GaussianGammaFoldedApproximantBalance.exponential_product_equivalent linearExponentF L linearExponentF
    _ _ _ u x v (exponential_input _ _ hu) (exponential_input _ _ hx) (exponential_input _ _ hv) sum
  have hGamma := gamma_regular (Γ := Γ) one two half_source
  have hExp := GaussianStirlingLogDuplication.exponential_regular L x hx
  have hLin := GaussianStirlingLogDuplication.exponential_regular linearExponentF u hu
  have swap := multiply_commutative G linearF (gammaData one two) (linearData (A+B) B) hGamma hLin
  have replace := multiply_cross linearF linearF G (E L) (linearData (A+B) B) (linearData (A+B) B)
    (gammaData one two) (Ed L x) hLin hLin hGamma hExp (cross_refl _ _ hLin)
    (cross_symm _ _ _ _ (GaussianStirlingLogDuplication.exponential_gamma one two half_source))
  exact cross_trans _ _ _ _ _ _ swap (cross_trans _ _ _ _ _ _ replace last)

theorem factor_regular (A B : PTm n) (h : Γ ⊢[PRAAx] source A B) :
    Γ ⊢[PRAAx] pointCN factorF (factorData A B) := by
  have hd := positive_product two B (le_succ_self one) h.andE₂
  have hs : Γ ⊢[PRAAx] source A (two*B) := .andI h.andE₁ hd
  have hp := GaussianGaussMultiplicationHalfPower.original_limit_power (arg A) A (two*B) two
    (le_succ_self one) hd (native_disk A (two*B) hs)
  have reg := cross_trans _ _ _ _ _ _ hp (cross_symm _ _ _ _ hp)
  exact multiply_fast _ _ _ _ reg (gamma_regular one two half_source)

theorem correction_step (A B : PTm n) (h : Γ ⊢[PRAAx] source A B) :
    Γ ⊢[PRAAx] crossEquivalent (M nameF factorF) nameF
      (Md nameF factorF (data (A+B) B) (factorData A B)) (data A B) := by
  let D := two*B
  let a := quadraticData (A+B) B
  let b := linearData (A+B) B
  let u := limitData (arg A) A D two
  let v : PTm n := gammaData one two
  let c := multiplier (arg A) D two
  let w := ratioPowerData c two
  have hTwo := le_succ_self (Γ := Γ) (one : PTm n)
  have hd : Γ ⊢[PRAAx] le one D := positive_product two B hTwo h.andE₂
  have hs : Γ ⊢[PRAAx] source A D := .andI h.andE₁ hd
  have bind := GaussianGaussMultiplicationHalfPower.original_limit_power (arg A) A D two hTwo hd (native_disk A D hs)
  have hu : Γ ⊢[PRAAx] pointCN powerF u := cross_trans _ _ _ _ _ _ bind (cross_symm _ _ _ _ bind)
  have ha := ratio_power_regular (Γ := Γ) (quadraticWeight (A+B) B) two hTwo
  have hb := GaussianStirlingLogDuplication.exponential_regular (Γ := Γ) linearExponentF (linearExponentData (linearWeight (A+B) B))
    (multiply_fast C L _ _ (constant_regular _) log_half_regular)
  have hv := gamma_regular (Γ := Γ) one two half_source
  have hw := ratio_power_regular c two hTwo
  have turn := regroup quadraticF linearF powerF G a b u v ha hb hu hv
  have replace := multiply_cross quadraticF quadraticF powerF quadraticF a a u w ha ha hu hw
    (cross_refl _ _ ha) bind
  have merged := ratio_power_sum (quadraticWeight (A+B) B) c two hTwo
  have eq := quadratic_weight_step A B h.andE₂
  have target := coefficient_congr _ _ two hTwo eq
  have left := cross_trans _ _ _ _ _ _ replace (cross_trans _ _ _ _ _ _ merged target)
  have rA := ratio_power_regular (quadraticWeight A B) two hTwo
  have rB := GaussianStirlingLogDuplication.exponential_regular (Γ := Γ) linearExponentF (linearExponentData (linearWeight A B))
    (multiply_fast C L _ _ (constant_regular _) log_half_regular)
  have simplify := multiply_cross (M quadraticF powerF) quadraticF (M G linearF) linearF
    (Md quadraticF powerF a u) (quadraticData A B) (Md G linearF v b) (linearData A B)
    (multiply_fast _ _ _ _ ha hu) rA (multiply_fast _ _ _ _ hv hb) rB left (linear_step A B h.andE₂)
  exact cross_trans _ _ _ _ _ _ turn simplify

theorem actual_Barnes_duplication_normalizer_half_step_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (let A := var 0; let B := var 1
       source A B ⟶ crossEquivalent (M nameF factorF) nameF
         (Md nameF factorF (data (A+B) B) (factorData A B)) (data A B)) :=
  closeUniv 2 (.impI (correction_step _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalDuplicationNormalizer
