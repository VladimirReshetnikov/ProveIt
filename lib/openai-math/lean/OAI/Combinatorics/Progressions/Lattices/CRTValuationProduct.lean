import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.NumberTheory.Padics.PadicVal.Basic

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem crtValuationProduct_finset_dvd {L : Type*} (p : L → ℕ)
    (hp : ∀ l, (p l).Prime) (hinj : Function.Injective p)
    (step : ℕ) (s : Finset L) :
    (∏ l ∈ s, p l ^ padicValNat (p l) step) ∣ step := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert l s hls ih =>
      rw [Finset.prod_insert hls]
      apply Nat.Coprime.mul_dvd_of_dvd_of_dvd _ pow_padicValNat_dvd ih
      apply Nat.coprime_prod_right_iff.mpr
      intro k hk
      exact Nat.coprime_pow_primes _ _ (hp l) (hp k)
        (fun h => hls (hinj h ▸ hk))

theorem crtValuationProduct_dvd {L : Type*} [Fintype L] (p : L → ℕ)
    (hp : ∀ l, (p l).Prime) (hinj : Function.Injective p) (step : ℕ) :
    (∏ l, p l ^ padicValNat (p l) step) ∣ step :=
  crtValuationProduct_finset_dvd p hp hinj step Finset.univ

theorem crtValuationProduct_le {L : Type*} [Fintype L] (p : L → ℕ)
    (hp : ∀ l, (p l).Prime) (hinj : Function.Injective p)
    {step : ℕ} (hstep : step ≠ 0) :
    (∏ l, p l ^ padicValNat (p l) step) ≤ step :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero hstep) (crtValuationProduct_dvd p hp hinj step)

end Erdos3

end

end OAI
