import DiophantineConsistency.Mixed121.Mixed121KernelResidue
import DiophantineConsistency.Mixed121.Mixed121ConstructionUnit
import DiophantineConsistency.Mixed121.Mixed121ControllerChoice

/-! # Rank calibration for the 121x8801 kernel at the chosen dimensions

This module collapses Compact44's seven thin wrappers into one: `KernelAliasExplicit`,
`AliasResidueNumeral`, `AliasUnitGivenResidue`, `AliasUnitDischarged`,
`AliasRankCalibration`, `ActualRankCalibration` and
`ChosenControllerCalibration`. Their theorem names are kept.

* `kernelAlias` is an irreducible name for `paramKernel rho`, so the
  kernel is never unfolded downstream; `kernelAlias_mod` is
  `Mixed121KernelResidue.kernel_mod`.
* `alias_unit`: `Γ` is a unit modulo `d·λ^(m+1)`, unconditionally.
* `symbolic_rank_calibration`: for any target `R0` there is a Boolean,
  `𝚺₁`-definable dummy set `δ` with `Γ·bsum δ + d·λ^e ≡ R0 (mod d·λ^(m+1))`,
  given `2·C0 < λ^m` and `λ^e ≤ λ^m`. This is recipe §4.
* `chosen_bounds` and `chosen_calibration`: the same at
  `N = λ^(2T+4)` and `w = λ^(T+1)`. `2·C0 = 4985960122 < λ³ = 12829337821`. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Mixed121Calibration
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.ArithmeticPow
open DiophantineConsistency.ArithmeticPackingBlocks
open DiophantineConsistency.Mixed121ConstructionUnit
open DiophantineConsistency.Mixed121ControllerChoice
open Mixed121Kernel Mixed121KernelResidue
attribute [local irreducible] paramKernel rho

@[irreducible] def kernelAlias : ℕ := paramKernel rho

theorem kernelAlias_eq : kernelAlias = paramKernel rho := by
  unfold kernelAlias
  rfl

/- Both transports keep every term under `%` syntactically identical on the two
sides. Comparing `Modulus` with its literal *under* `%` would make the kernel
evaluate the million-bit `paramKernel rho`. -/
theorem kernelAlias_mod_abbrev : kernelAlias % Modulus = 510020909 :=
  (congrArg (fun k : ℕ => k % Modulus = 510020909) kernelAlias_eq).mpr kernel_mod

theorem kernelAlias_mod : kernelAlias % 2492980061 = 510020909 :=
  (congrArg (fun m : ℕ => kernelAlias % m = 510020909)
    (show Modulus = 2492980061 from rfl)).mp kernelAlias_mod_abbrev

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem alias_unit (m e : V) :
    ∃ Γi, (Gamma (kernelAlias : V) (power 2341 (m + 1)) (power 2341 e) * Γi) %
        (1064921 * power 2341 (m + 1)) = 1 % (1064921 * power 2341 (m + 1)) :=
  gamma_unit_nat kernelAlias kernelAlias_mod m e

theorem alias_rank_calibration (m e R0 : V)
    (hP2 : 2 * (1064921 * 2341) < power 2341 m)
    (hw : power 2341 e ≤ power 2341 m) :
    ∃ δ : V → V, (𝚺₁-Function₁ δ) ∧ (∀ j, δ j ≤ 1) ∧
      (∀ j, δ j ≠ 0 → 0 < j ∧ j + 1 < power 2341 (m + 1) ∧
        j + power 2341 e < power 2341 (m + 1)) ∧
      (Gamma (kernelAlias : V) (power 2341 (m + 1)) (power 2341 e) *
        bsum 1064921 δ (power 2341 (m + 1)) + 1064921 * power 2341 e) %
          (1064921 * power 2341 (m + 1)) = R0 % (1064921 * power 2341 (m + 1)) := by
  obtain ⟨Γi, hΓ⟩ := alias_unit m e
  exact rank_calibration m (power 2341 e) R0
    (Gamma (kernelAlias : V) (power 2341 (m + 1)) (power 2341 e)) Γi hP2 hw hΓ

theorem symbolic_rank_calibration (m e R0 : V)
    (hP2 : 2 * (1064921 * 2341) < power 2341 m)
    (hw : power 2341 e ≤ power 2341 m) :
    ∃ δ : V → V, (𝚺₁-Function₁ δ) ∧ (∀ j, δ j ≤ 1) ∧
      (∀ j, δ j ≠ 0 → 0 < j ∧ j + 1 < power 2341 (m + 1) ∧
        j + power 2341 e < power 2341 (m + 1)) ∧
      (Gamma (paramKernel rho : V) (power 2341 (m + 1)) (power 2341 e) *
        bsum 1064921 δ (power 2341 (m + 1)) + 1064921 * power 2341 e) %
          (1064921 * power 2341 (m + 1)) = R0 % (1064921 * power 2341 (m + 1)) := by
  exact (congrArg (fun k : ℕ => ∃ δ : V → V, (𝚺₁-Function₁ δ) ∧ (∀ j, δ j ≤ 1) ∧
    (∀ j, δ j ≠ 0 → 0 < j ∧ j + 1 < power 2341 (m + 1) ∧
      j + power 2341 e < power 2341 (m + 1)) ∧
    (Gamma (k : V) (power 2341 (m + 1)) (power 2341 e) *
      bsum 1064921 δ (power 2341 (m + 1)) + 1064921 * power 2341 e) %
        (1064921 * power 2341 (m + 1)) = R0 % (1064921 * power 2341 (m + 1)))
    kernelAlias_eq).mp (alias_rank_calibration m e R0 hP2 hw)

/-- Exact numerical bounds for the selected width and total period. -/
theorem chosen_bounds (T : V) :
    power 2341 (T+1) ≤ power 2341 (2*T+3) ∧
    2*(1064921*2341) < power 2341 (2*T+3) ∧
    power 2341 (T+1)*power 2341 (T+3) = power 2341 ((2*T+3)+1) := by
  have hp : (1:V) ≤ 2341 := by norm_num
  have hexp : T+1 ≤ 2*T+3 := by
    calc T+1 ≤ (T+1)+(T+2) := le_add_of_nonneg_right (show (0:V) ≤ T+2 by positivity)
      _ = 2*T+3 := by ring
  have hm : (3:V) ≤ 2*T+3 := by
    simpa only [zero_add] using le_add_of_nonneg_left (show (0:V)≤2*T by positivity)
  have hw := power_mono_exponent 2341 (T+1) (2*T+3) hp hexp
  have h3 : power (2341:V) 3 = 2341*(2341*2341) := by
    rw [show (3:V)=(2:V)+1 by norm_num, power_succ,
      show (2:V)=(1:V)+1 by norm_num, power_succ, power_one]
  have hsize : 2*(1064921*2341) < power 2341 (2*T+3) := by
    calc 2*(1064921*2341) < power (2341:V) 3 := by rw [h3]; norm_num
      _ ≤ power 2341 (2*T+3) := power_mono_exponent 2341 3 (2*T+3) hp hm
  refine ⟨hw, hsize, ?_⟩
  rw [← power_add]
  congr 1
  ring

/-- Abstract selection for the chosen powers, with no size premise. -/
theorem chosen_calibration (T R0 : V) :
    ∃ δ : V → V, (𝚺₁-Function₁ δ) ∧ (∀ j, δ j ≤ 1) ∧
      (∀ j, δ j ≠ 0 → 0 < j ∧ j + 1 < power 2341 ((2*T+3)+1) ∧
        j + power 2341 (T+1) < power 2341 ((2*T+3)+1)) ∧
      (Gamma (paramKernel rho : V) (power 2341 ((2*T+3)+1)) (power 2341 (T+1)) *
        bsum 1064921 δ (power 2341 ((2*T+3)+1)) + 1064921 * power 2341 (T+1)) %
          (1064921 * power 2341 ((2*T+3)+1)) = R0 % (1064921 * power 2341 ((2*T+3)+1)) := by
  have h := chosen_bounds T
  exact symbolic_rank_calibration (2*T+3) (T+1) R0 h.2.1 h.1

#print axioms kernelAlias_mod
#print axioms alias_unit
#print axioms symbolic_rank_calibration
#print axioms chosen_calibration
end Mixed121Calibration
