import DiophantineConsistency.ArithmeticControllerChoice
import DiophantineConsistency.ArithmeticControllerStride

/-! **K5 — the rank controller** (construction spec §7 Stage K, §8, with
simplification S7: Hensel induction instead of the pigeonhole principle), in
every model of IΣ1, at internal (possibly nonstandard) level `m`.

Constants: `d = 94517`, `p = 120199`, `N = p^(m+1)` cells, `M = d·N`,
`B = 2^d`; `ArithmeticPow.power` is the represented power.

Helper modules:
* `ArithmeticControllerLift` — generic `expand`, `lte` (lifting the
  exponent), `coordinates_surj` (Hensel) and `coordinates_inj`;
* `ArithmeticControllerData` — `g = B^(p-1) = 1 + d·p·v`, `v·66027 ≡ 1
  (mod p)` (one modular exponentiation in ℕ, transported by `Nat.cast`), the
  coordinate `zc`, dummy positions `2 + 120198·e`, one-bit block sums;
* `ArithmeticControllerChoice` — `controller_choice`, `rank_calibration`,
  `calibrated`;
* `ArithmeticControllerStride` — `stride` (derived stride and multiplier).

**Interface for the assembly K7** (`controller`, and `controller_tiling` at the K2
dimensions `N = w·H`, `s = w`, `w = p^(T+1)`, `H = p^(T+3)`, `m = 2T+3`). Inputs: the level `m`
with `2·d·p < p^m` (`large_level`: any `m ≥ 3`, e.g. K2's `m = 2T+3`), the
tiling stride `s` with `0 < s ≤ p^m` (K2's `s = p^(T+1)`), the rank `R0` of
the dummy-free packing and a unit `Γ` modulo `M` with inverse `Γi` (spec K2).
Output: a Σ1 Boolean dummy map `δ` (to be fed to
`ArithmeticPackingCells.cellWord a δ N s`) whose support is safe
(`0 < j`, `j+1 < N`, `j+s < N`) and, for the rank `R` of the packing with
these dummies, as soon as the exact rank variation `R + Γ·Σ_{j<N} B^j δ_j = R0`
(spec K1) and rank forcing `2·d·N < R` (K4) are supplied:

* `d·t + d·N = R`, `N < t`, `t mod N = s`, where `t = R/d − N`;
* `w·2^(d·N) = 2^R`, where `w = 2^(R − d·N)` (coordinate `v8`);
* `w ≡ 2^(d·s) (mod 2^(d·N) − 1)` — the hypothesis `hW` of
  `ArithmeticPacking.packing_transport`.

The block sum is `ArithmeticPackingBlocks.bsum 94517 δ N`, the same library
as the packing scalars. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.ArithmeticController
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPow ArithmeticControllerLift ArithmeticControllerData ArithmeticControllerChoice
  ArithmeticControllerStride ArithmeticPackingBlocks

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The size condition holds from level `3` on. -/
theorem large_level (m : V) (hm : 3 ≤ m) : 2 * (94517 * 120199) < power (120199 : V) m := by
  have h3 : power (120199 : V) 3 = 120199 * (120199 * (120199 * 1)) := by
    rw [show (3 : V) = 0 + 1 + 1 + 1 by norm_num, power_succ, power_succ, power_succ, power_zero]
  calc 2 * (94517 * 120199) < power (120199 : V) 3 := by rw [h3]; norm_num
    _ ≤ power 120199 m := power_mono_exponent _ _ _ (by norm_num) hm

/-- **The controller.** -/
theorem controller (m s R0 Γ Γi : V) (hP2 : 2 * (94517 * 120199) < power 120199 m)
    (hs0 : 0 < s) (hs : s ≤ power 120199 m)
    (hΓ : (Γ * Γi) % (94517 * power 120199 (m + 1)) = 1 % (94517 * power 120199 (m + 1))) :
    ∃ δ : V → V, (𝚺₁-Function₁ δ) ∧ (∀ j, δ j ≤ 1) ∧
      (∀ j, δ j ≠ 0 → 0 < j ∧ j + 1 < power 120199 (m + 1) ∧ j + s < power 120199 (m + 1)) ∧
      ∀ R, R + Γ * bsum 94517 δ (power 120199 (m + 1)) = R0 →
        2 * (94517 * power 120199 (m + 1)) < R →
        94517 * (R / 94517 - power 120199 (m + 1)) + 94517 * power 120199 (m + 1) = R ∧
        power 120199 (m + 1) < R / 94517 - power 120199 (m + 1) ∧
        (R / 94517 - power 120199 (m + 1)) % power 120199 (m + 1) = s ∧
        Exp.exp (R - 94517 * power 120199 (m + 1)) * Exp.exp (94517 * power 120199 (m + 1)) =
          Exp.exp R ∧
        Exp.exp (R - 94517 * power 120199 (m + 1)) % (Exp.exp (94517 * power 120199 (m + 1)) - 1) =
          Exp.exp (94517 * s) % (Exp.exp (94517 * power 120199 (m + 1)) - 1) := by
  obtain ⟨δ, hδd, hδb, hδs, hcal⟩ := rank_calibration m s R0 Γ Γi hP2 hs hΓ
  refine ⟨δ, hδd, hδb, hδs, fun R hvar hbig => ?_⟩
  have hN : (0 : V) < power 120199 (m + 1) := power_pos _ _ p_pos
  have hM : (0 : V) < 94517 * power 120199 (m + 1) := mul_pos (by norm_num) hN
  have hsN : s < power 120199 (m + 1) := by
    rw [power_succ]
    calc s ≤ power 120199 m := hs
      _ < 120199 * power 120199 m := lt_mul_of_one_lt_left (power_pos _ _ p_pos) (by norm_num)
  have hR := calibrated hM hvar hcal
  exact stride 94517 (power 120199 (m + 1)) s R (by norm_num) hs0 hsN hR hbig

/-- **The controller at the K2 tiling dimensions** `w = p^(T+1)`, `H = p^(T+3)`:
cells `N = w·H` and stride `s = w`, exactly as `ArithmeticTilingWord.dimensions`,
`ArithmeticPackingCells.packing_of_marked` and `ArithmeticPacking.packing_transport`
use them. -/
theorem controller_tiling (T R0 Γ Γi : V)
    (hΓ : (Γ * Γi) % (94517 * (power 120199 (T + 1) * power 120199 (T + 3))) =
      1 % (94517 * (power 120199 (T + 1) * power 120199 (T + 3)))) :
    ∃ δ : V → V, (𝚺₁-Function₁ δ) ∧ (∀ j, δ j ≤ 1) ∧
      (∀ j, δ j ≠ 0 → 0 < j ∧ j + 1 < power 120199 (T + 1) * power 120199 (T + 3) ∧
        j + power 120199 (T + 1) < power 120199 (T + 1) * power 120199 (T + 3)) ∧
      ∀ R, R + Γ * bsum 94517 δ (power 120199 (T + 1) * power 120199 (T + 3)) = R0 →
        2 * (94517 * (power 120199 (T + 1) * power 120199 (T + 3))) < R →
        94517 * (R / 94517 - power 120199 (T + 1) * power 120199 (T + 3)) +
            94517 * (power 120199 (T + 1) * power 120199 (T + 3)) = R ∧
        power 120199 (T + 1) * power 120199 (T + 3) <
            R / 94517 - power 120199 (T + 1) * power 120199 (T + 3) ∧
        (R / 94517 - power 120199 (T + 1) * power 120199 (T + 3)) %
            (power 120199 (T + 1) * power 120199 (T + 3)) = power 120199 (T + 1) ∧
        Exp.exp (R - 94517 * (power 120199 (T + 1) * power 120199 (T + 3))) *
            Exp.exp (94517 * (power 120199 (T + 1) * power 120199 (T + 3))) = Exp.exp R ∧
        Exp.exp (R - 94517 * (power 120199 (T + 1) * power 120199 (T + 3))) %
            (Exp.exp (94517 * (power 120199 (T + 1) * power 120199 (T + 3))) - 1) =
          Exp.exp (94517 * power 120199 (T + 1)) %
            (Exp.exp (94517 * (power 120199 (T + 1) * power 120199 (T + 3))) - 1) := by
  have hN : power (120199 : V) (T + 1) * power 120199 (T + 3) = power 120199 (2 * T + 3 + 1) := by
    rw [← power_add]; congr 1; ring
  rw [hN] at hΓ ⊢
  have hm : (3 : V) ≤ 2 * T + 3 := le_add_of_nonneg_left (Arithmetic.zero_le _)
  have hs : power (120199 : V) (T + 1) ≤ power 120199 (2 * T + 3) :=
    power_mono_exponent _ _ _ (by norm_num) (by
      calc T + 1 ≤ T + 1 + (T + 2) := le_add_of_nonneg_right (Arithmetic.zero_le _)
        _ = 2 * T + 3 := by ring)
  exact controller (2 * T + 3) _ R0 Γ Γi (large_level _ hm) (power_pos _ _ p_pos) hs hΓ

end DiophantineConsistency.ArithmeticController
