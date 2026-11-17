import IPRADerivations.Probability.ExpectationCorollaries
import IPRADerivations.DiophantineNumberTheory.SquareArea

/-!
# Finite Minkowski for `p = 1` and `p = 2`

Packet: `probability/expected_value_ipra_2026-11-16`, Theorem `thm:minkowski`, in the two exact cases
the packet singles out ("for `p = 1` the theorem is exact rational algebra; for `p = 2` it follows
from Cauchy–Schwarz"). Expectations are the weighted numerators `Ew(·) = ∑_{i<M} w_i (·)_i`, `W = ∑ w`.

* `monus_le_of_le_add`, `ad_triangle`: the pointwise triangle inequality
  `|(a + a') − (b + b')| ≤ |a − b| + |a' − b'|` for differences of naturals;
* `minkowski_one` (`p = 1`): for signed observables `X = P − N`, `Y = P' − N'`,
  `E|X + Y| ≤ E|X| + E|Y|`;
* `minkowski_two` (`p = 2`, roots by certificate): for natural observables and naturals `A`, `B`
  with `E X² ≤ A²` and `E Y² ≤ B²` (cleared: `Ew(X²) ≤ A² W`, `Ew(Y²) ≤ B² W`),
  `E (X + Y)² ≤ (A + B)²`, i.e. `‖X + Y‖₂ ≤ A + B`; with `A = ‖X‖₂`, `B = ‖Y‖₂` exact this is
  `‖X + Y‖₂ ≤ ‖X‖₂ + ‖Y‖₂`. The cross term is bounded by Cauchy–Schwarz and `le_of_sq_le`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Probability.Minkowski

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Probability.Expectation (Ew Wt inst2_mul' inst2_add' exp_add exp_mono cauchy_schwarz)
open LeanProofs.IPRA.Probability.Variance (ad second_moment_add)
open LeanProofs.IPRA.Probability.ExpectationCorollaries (adB inst2_adB)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (le_of_sq_le)
open LeanProofs.IPRA.DiophantineNumberTheory.SquareArea (le_add_mono)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## The pointwise triangle inequality -/

/-- `x ≤ y + z` gives `x ∸ y ≤ z`. -/
theorem monus_le_of_le_add {x y z : PTm n} (h : Γ ⊢[PRAAx] le x (y + z)) : Γ ⊢[PRAAx] le (monus x y) z := by
  refine .orE (le_total x y) ?_ ?_
  · exact le_congr (show (le x y :: Γ) ⊢[PRAAx] monus x y ≐ zero from Prf.hyp0).eqSymm (.eqRefl _) (zero_le _)
  · let C := le y x :: Γ
    have e1 := natEq (eq_add_of_le (Prf.hyp0 : C ⊢[PRAAx] le y x))
    have e2 := natEq (eq_add_of_le (h.wk : C ⊢[PRAAx] le x (y + z)))
    refine le_of_eq_add (d := monus (y + z) x) ?_
    apply deriveNat; ipra_simps
    linear_combination e2 + e1

/-- `a ≤ b + (a ∸ b)`. -/
theorem le_add_monus (a b : PTm n) : Γ ⊢[PRAAx] le a (b + monus a b) := by
  have m := natEq (monus_max (Γ := Γ) a b)
  refine le_of_eq_add (d := monus b a) ?_
  apply deriveNat; ipra_simps
  linear_combination m

/-- `(a + a') ∸ (b + b') ≤ (a ∸ b) + (a' ∸ b')`. -/
theorem monus_add_le (a a' b b' : PTm n) : Γ ⊢[PRAAx] le (monus (a + a') (b + b')) (monus a b + monus a' b') := by
  refine monus_le_of_le_add (le_congr (.eqRefl _) ?_ (le_add_mono (le_add_monus a b) (le_add_monus a' b')))
  apply deriveNat; ipra_simps; ring

/-- `|(a + a') − (b + b')| ≤ |a − b| + |a' − b'|`. -/
theorem ad_triangle (a a' b b' : PTm n) : Γ ⊢[PRAAx] le (ad (a + a') (b + b')) (ad a b + ad a' b') := by
  refine le_congr (.eqRefl _) ?_ (le_add_mono (monus_add_le a a' b b') (monus_add_le b b' a a'))
  apply deriveNat; ipra_simps; ring

/-! ## Minkowski -/

theorem inst2_monus'' (f g : PTm 2) (i x : PTm n) :
    inst2 (monus f g) i x = monus (inst2 f i x) (inst2 g i x) := by simp [inst2]

/-- `thm:minkowski`, `p = 1`: `E|X + Y| ≤ E|X| + E|Y|` for `X = P − N`, `Y = P' − N'`. -/
theorem minkowski_one (w P N P' N' : PTm 2) (M x : PTm n) :
    Γ ⊢[PRAAx] le (Ew w (adB (P + P') (N + N')) M x) (Ew w (adB P N) M x + Ew w (adB P' N') M x) := by
  refine le_congr (.eqRefl _) (exp_add _ _ _ _ _) (exp_mono _ _ _ _ _ (.allI (.impI ?_)))
  simp only [inst2_monus'', inst2_add']
  exact ad_triangle _ _ _ _

/-- `thm:minkowski`, `p = 2`: with root certificates `Ew(X²) ≤ A² W` and `Ew(Y²) ≤ B² W`,
`Ew((X + Y)²) ≤ (A + B)² W`, i.e. `‖X + Y‖₂ ≤ A + B`. -/
theorem minkowski_two (w X Y : PTm 2) {M x A B : PTm n}
    (hA : Γ ⊢[PRAAx] le (Ew w (X * X) M x) (A * A * Wt w M x))
    (hB : Γ ⊢[PRAAx] le (Ew w (Y * Y) M x) (B * B * Wt w M x)) :
    Γ ⊢[PRAAx] le (Ew w ((X + Y) * (X + Y)) M x) ((A + B) * (A + B) * Wt w M x) := by
  have cs := cauchy_schwarz (Γ := Γ) w X Y M x
  have hx : Γ ⊢[PRAAx] le (Ew w (X * Y) M x * Ew w (X * Y) M x) (A * B * Wt w M x * (A * B * Wt w M x)) := by
    refine le_trans cs (le_congr (.eqRefl _) ?_ (le_mul_mono hA hB))
    apply deriveNat; ipra_simps; ring
  have xy := le_of_sq_le hx
  refine le_congr (second_moment_add w X Y M x).eqSymm (.eqRefl _) ?_
  refine le_congr (.eqRefl _) ?_ (le_add_mono (le_add_mono hA (le_add_mono xy xy)) hB)
  apply deriveNat; ipra_simps; ring

end LeanProofs.IPRA.Probability.Minkowski
