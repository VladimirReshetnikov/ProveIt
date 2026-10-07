import GowersSzemeredi.Proofs16BalancedProgressionWord
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! The finite union-bound budget tends to zero at any positive power
length scale. Hence balanced words exist on all long proper progressions
at sufficiently large moduli. -/
set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology
namespace LeanProofs.GowersSzemeredi

theorem alphabet_polynomial_exponential_decay {delta epsilon : Real}
    (hδ : 0 < delta) (hε : 0 < epsilon) :
    Tendsto (fun n : Nat => (n : Real) ^ (3 : Nat) *
      Real.exp (-2 * epsilon ^ 2 * (n : Real) ^ delta)) atTop (𝓝 0) := by
  have hscale : Tendsto (fun n : Nat => (n : Real) ^ delta) atTop atTop :=
    (tendsto_rpow_atTop hδ).comp tendsto_natCast_atTop_atTop
  have hlim := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (3 / delta)
    (2 * epsilon ^ 2) (by positivity)).comp hscale
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (1 : Nat)] with n hn
  have hn0 : (0 : Real) ≤ n := Nat.cast_nonneg _
  have hexp : delta * (3 / delta) = 3 := by field_simp
  simp only [Function.comp_apply]
  rw [← Real.rpow_mul hn0, hexp]
  rw [Real.rpow_ofNat]
  congr 2
  ring

theorem alphabet_progression_budget_eventually (R : Nat) {delta epsilon : Real}
    (hδ : 0 < delta) (hε : 0 < epsilon) :
    ∃ N₀ : Nat, ∀ N : Nat, N₀ ≤ N →
      (N : Real) ^ 2 * (N + 1) * R * Real.exp (-2 * epsilon ^ 2 * (N : Real) ^ delta) < 1 := by
  have hlim := (alphabet_polynomial_exponential_decay hδ hε).const_mul (2 * (R : Real))
  simp only [mul_zero] at hlim
  have hevent : ∀ᶠ N : Nat in atTop,
      2 * (R : Real) * ((N : Real) ^ (3 : Nat) *
        Real.exp (-2 * epsilon ^ 2 * (N : Real) ^ delta)) < 1 :=
    hlim.eventually (gt_mem_nhds (by norm_num : (0 : Real) < 1))
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hevent
  refine ⟨max N₀ 1, fun N hN => ?_⟩
  have hN1 : (1 : Real) ≤ N := by exact_mod_cast (le_max_right N₀ 1).trans hN
  have hn : (0 : Real) ≤ N := Nat.cast_nonneg _
  have hpoly : (N : Real) ^ 2 * (N + 1) * R ≤ 2 * R * (N : Real) ^ (3 : Nat) := by
    have h := mul_le_mul_of_nonneg_left (by linarith only [hN1] : (N : Real) + 1 ≤ 2 * N)
      (sq_nonneg (N : Real))
    have hh := mul_le_mul_of_nonneg_right h (Nat.cast_nonneg R)
    nlinarith only [hh]
  have ht := mul_le_mul_of_nonneg_right hpoly
    (Real.exp_pos (-2 * epsilon ^ 2 * (N : Real) ^ delta)).le
  have hb := hN₀ N ((le_max_left _ _).trans hN)
  apply lt_of_le_of_lt _ hb
  simpa only [mul_assoc] using ht

theorem exists_balanced_progression_word_large_N (R : Nat) (hR : 0 < R)
    {delta epsilon : Real} (hδ : 0 < delta) (hδone : delta ≤ 1) (hε : 0 < epsilon) :
    ∃ N₀ : Nat, ∀ (N : Nat) [NeZero N], N₀ ≤ N →
      ∃ w : ZMod N → Fin R, ∀ P : ModAP N, P.IsProper → (N : Real) ^ delta ≤ P.length →
        ∀ c : Fin R, ((P.carrier.filter (fun x => w x = c)).card : Real) ≤
          (1 / (R : Real) + epsilon) * P.length := by
  obtain ⟨N₀, hN₀⟩ := alphabet_progression_budget_eventually R hδ hε
  refine ⟨N₀, fun N _ hN => ?_⟩
  have hN1 : (1 : Real) ≤ N := by exact_mod_cast NeZero.pos N
  have hscale : (N : Real) ^ delta ≤ N := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hN1 hδone
  exact exists_balanced_progression_word hR ((N : Real) ^ delta) epsilon hscale hε.le (hN₀ N hN)

end LeanProofs.GowersSzemeredi
