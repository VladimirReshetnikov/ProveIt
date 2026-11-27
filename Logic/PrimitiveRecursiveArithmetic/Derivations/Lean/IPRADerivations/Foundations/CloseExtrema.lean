import IPRADerivations.Probability.EventAlgebraMetric
import IPRADerivations.Probability.Minkowski

/-!
# Closeness of finite observations through maxima, minima and complements

Packet: `foundations/ipra_continuous_framework_2026-11-20_2`, `lean/FiniteExtrema.lean` (host-level Lean there):
`Close e a b` (`a ≤ b + e ∧ b ≤ a + e`) with `close_refl`, `close_symm`, `close_mono`, `close_trans`,
`close_max`, `close_min`, `close_complement`. Here `close e a b` is the object formula, for natural terms (the
values of finite observations on a common scale), with maximum `larger` and minimum `meet`:

* `close_refl`, `close_symm`, `close_mono`, `close_trans` (errors add);
* `close_max`, `close_min`: componentwise closeness passes to the maximum and the minimum with the same error;
* `close_complement`: `close e a b` gives `close e (B ∸ a) (B ∸ b)`.
-/

namespace LeanProofs.IPRA.Foundations.CloseExtrema

open_ipra exports
open LeanProofs.IPRA.Probability.Minkowski (monus_le_of_le_add)
open LeanProofs.IPRA.Analysis.Observation.PrefixObject (larger larger_le le_larger_left le_larger_right)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `a` and `b` are within `e`. -/
def close (e a b : PTm n) : Fm PTm n := le a (b + e) ⋏ le b (a + e)

theorem close_refl (e a : PTm n) : Γ ⊢[PRAAx] close e a a :=
  .andI (by ipra_le 𝔟 e) (by ipra_le 𝔟 e)

theorem close_symm {e a b : PTm n} (h : Γ ⊢[PRAAx] close e a b) : Γ ⊢[PRAAx] close e b a :=
  .andI h.andE₂ h.andE₁

theorem close_mono {e e' a b : PTm n} (h : Γ ⊢[PRAAx] close e a b) (he : Γ ⊢[PRAAx] le e e') :
    Γ ⊢[PRAAx] close e' a b := by
  have h1 := h.andE₁
  have h2 := h.andE₂
  exact .andI (by ipra_le sl h1 + sl he) (by ipra_le sl h2 + sl he)

theorem close_trans {e d a b c : PTm n} (h : Γ ⊢[PRAAx] close e a b) (k : Γ ⊢[PRAAx] close d b c) :
    Γ ⊢[PRAAx] close (e + d) a c := by
  have h1 := h.andE₁
  have h2 := h.andE₂
  have k1 := k.andE₁
  have k2 := k.andE₂
  exact .andI (by ipra_le sl h1 + sl k1) (by ipra_le sl h2 + sl k2)

private theorem max_up {e a b c d : PTm n} (h : Γ ⊢[PRAAx] le a (b + e)) (k : Γ ⊢[PRAAx] le c (d + e)) :
    Γ ⊢[PRAAx] le (larger a c) (larger b d + e) := by
  have l1 := le_larger_left (Γ := Γ) b d
  have l2 := le_larger_right (Γ := Γ) b d
  exact larger_le (by ipra_le sl h + sl l1) (by ipra_le sl k + sl l2)

theorem close_max {e a b c d : PTm n} (h : Γ ⊢[PRAAx] close e a b) (k : Γ ⊢[PRAAx] close e c d) :
    Γ ⊢[PRAAx] close e (larger a c) (larger b d) :=
  .andI (max_up h.andE₁ k.andE₁) (max_up h.andE₂ k.andE₂)

private theorem min_up {e a b c d : PTm n} (h : Γ ⊢[PRAAx] le a (b + e)) (k : Γ ⊢[PRAAx] le c (d + e)) :
    Γ ⊢[PRAAx] le (meet a c) (meet b d + e) := by
  refine .orE (le_total b d) ?_ ?_
  · have m := meet_le_left (Γ := le b d :: Γ) a c
    have e1 := natEq (meet_left (Γ := le b d :: Γ) Prf.hyp0)
    have h' : (le b d :: Γ) ⊢[PRAAx] le a (b + e) := h.wk
    ipra_le sl m + sl h' with e1
  · have m := meet_le_right (Γ := le d b :: Γ) a c
    have e1 := natEq (meet_right (Γ := le d b :: Γ) Prf.hyp0)
    have k' : (le d b :: Γ) ⊢[PRAAx] le c (d + e) := k.wk
    ipra_le sl m + sl k' with e1

theorem close_min {e a b c d : PTm n} (h : Γ ⊢[PRAAx] close e a b) (k : Γ ⊢[PRAAx] close e c d) :
    Γ ⊢[PRAAx] close e (meet a c) (meet b d) :=
  .andI (min_up h.andE₁ k.andE₁) (min_up h.andE₂ k.andE₂)

/-- `B ≤ b + (B ∸ b)`. -/
private theorem le_add_monus' (B b : PTm n) : Γ ⊢[PRAAx] le B (b + monus B b) := by
  refine .orE (le_total b B) ?_ ?_
  · have e := natEq (eq_add_of_le (Prf.hyp0 : (le b B :: Γ) ⊢[PRAAx] le b B))
    ipra_le 0 with e
  · have h : (le B b :: Γ) ⊢[PRAAx] le B b := Prf.hyp0
    ipra_le sl h + 𝔟 (monus B b)

private theorem compl_up {e a b B : PTm n} (h : Γ ⊢[PRAAx] le b (a + e)) :
    Γ ⊢[PRAAx] le (monus B a) (monus B b + e) := by
  refine monus_le_of_le_add ?_
  have p := le_add_monus' (Γ := Γ) B b
  ipra_le sl p + sl h

theorem close_complement {e a b : PTm n} (B : PTm n) (h : Γ ⊢[PRAAx] close e a b) :
    Γ ⊢[PRAAx] close e (monus B a) (monus B b) :=
  .andI (compl_up h.andE₂) (compl_up h.andE₁)

end LeanProofs.IPRA.Foundations.CloseExtrema
