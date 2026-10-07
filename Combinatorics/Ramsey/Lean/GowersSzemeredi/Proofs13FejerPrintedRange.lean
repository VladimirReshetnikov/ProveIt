import GowersSzemeredi.Proofs13FejerExplicitExponent
import Mathlib.Algebra.Order.Ring.Pow

/-! The improved explicit bound reaches the printed length throughout
0 < alpha <= 1023/1024. A Bernoulli estimate gives the comparison without
logarithms. The remaining near-maximal range requires a separate argument. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem section13_fejer_printed_top_comparison {alpha : Real}
    (hα : 0 < alpha) (hαupper : alpha ≤ 1023 / 1024) :
    (2 / alpha) ^ ((2 : Nat) ^ 53) ≤ (1 / alpha) ^ ((2 : Nat) ^ 70) := by
  let t : Real := 1 / alpha
  have ht : 1 + 1 / 1024 ≤ t := by
    apply (le_div_iff₀ hα).mpr
    nlinarith only [hαupper]
  have ht1 : 1 ≤ t := by linarith only [ht]
  have ht0 : 0 ≤ t := zero_le_one.trans ht1
  have hb := one_add_mul_sub_le_pow (by linarith only [ht1] : -1 ≤ t) 1024
  have htwo : 2 ≤ t ^ (1024 : Nat) := by norm_num only [Nat.cast_ofNat] at hb; nlinarith only [ht, hb]
  have hstep : 2 * t ≤ t ^ ((2 : Nat) ^ 17) := by
    calc
      _ ≤ t ^ (1024 : Nat) * t := mul_le_mul_of_nonneg_right htwo ht0
      _ = t ^ (1025 : Nat) := (pow_succ _ _).symm
      _ ≤ _ := pow_le_pow_right₀ ht1 (by norm_num)
  calc
    _ = (2 * t) ^ ((2 : Nat) ^ 53) := by congr 1; dsimp [t]; ring
    _ ≤ (t ^ ((2 : Nat) ^ 17)) ^ ((2 : Nat) ^ 53) := pow_le_pow_left₀ (by positivity) hstep _
    _ = t ^ ((2 : Nat) ^ 70) := by rw [← pow_mul]; congr 1

theorem section13_fejer_printed_exponent_comparison {alpha : Real}
    (hα : 0 < alpha) (hαupper : alpha ≤ 1023 / 1024) :
    (1 / 2 : Real) ^ ((1 / alpha) ^ ((2 : Nat) ^ 70)) ≤
      (1 / 2 : Real) ^ ((2 / alpha) ^ ((2 : Nat) ^ 53)) :=
  Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num)
    (section13_fejer_printed_top_comparison hα hαupper)

theorem theorem_13_12_away_from_one :
    ∀ alpha : Real, 0 < alpha → alpha ≤ 1023 / 1024 → ∃ N₀ : Nat,
      ∀ (N : Nat) [NeZero N] [Fact N.Prime], N₀ ≤ N →
        ∀ f : ZMod N → Complex, DiscValued f → ¬ UniformOfDegree f alpha 3 →
        ∃ P Q : ModAP N, ∃ B : Finset (Pair N), ∃ phi : Pair N → ZMod N,
          P.step != 0 ∧ P.step = Q.step ∧ P.IsProper ∧ Q.IsProper ∧ P.length = Q.length ∧
          (N : Real) ^ ((1 / 2 : Real) ^ ((1 / alpha) ^ ((2 : Nat) ^ 70))) ≤ P.length ∧
          B ⊆ P.carrier.product Q.carrier ∧
          (alpha / 2) ^ ((2 : Nat) ^ 76) * P.length * Q.length ≤ B.card ∧
          BilinearOn (P.carrier.product Q.carrier) phi ∧
          ∀ z, z ∈ B → alpha * N / 2 ≤ ‖secondDifferenceFourier f z.1 z.2 (phi z)‖ := by
  intro alpha hα hαupper
  have hαone : alpha ≤ 1 := hαupper.trans (by norm_num)
  obtain ⟨N₀, hN₀⟩ := theorem_13_12_with_fejer_explicit_bound alpha hα hαone
  refine ⟨N₀, fun N _ _ hN f hf hnot => ?_⟩
  obtain ⟨P, Q, B, phi, hs, hs', hP, hQ, hlen, hsize, hbox, hmass, hbil, hfourier⟩ :=
    hN₀ N hN f hf hnot
  refine ⟨P, Q, B, phi, hs, hs', hP, hQ, hlen, ?_, hbox, ?_, hbil, hfourier⟩
  · have hNreal : (1 : Real) ≤ N := by exact_mod_cast NeZero.pos N
    exact (Real.rpow_le_rpow_of_exponent_le hNreal
      (section13_fejer_printed_exponent_comparison hα hαupper)).trans hsize
  · have hd : (alpha / 2) ^ ((2 : Nat) ^ 76) ≤ (alpha / 2) ^ ((2 : Nat) ^ 42) :=
      pow_le_pow_of_le_one (by positivity) (by linarith only [hαone]) (by norm_num)
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hd
      (Nat.cast_nonneg P.length)) (Nat.cast_nonneg Q.length)).trans hmass

end LeanProofs.GowersSzemeredi
