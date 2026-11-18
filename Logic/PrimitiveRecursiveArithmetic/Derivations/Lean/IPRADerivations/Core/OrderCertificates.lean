import IPRADerivations.Core.Order
import IPRADerivations.Core.Tactic

/-!
# Certificates for inequalities

`Core/Order` reduces `a ≤ b` to an equation `b = a + d` with an explicit slack term `d`
(`le_of_eq_add`, `eq_add_of_le`), and `Core/Tactic` moves equations to the commutative ring
`Groth (Q Γ)`, where `ring` and `linear_combination` decide them. Used directly, this makes every
derived inequality name its slack, usually a long `monus (…) (…)` built from the slacks of the
hypotheses.

This module removes the slack terms from the proofs. An element of `Groth (Q Γ)` is `Nonneg` when it
is the value of a term. For a derived inequality `h : Γ ⊢ a ≤ b` its slack is the ring element
`sl h = ι b − ι a`, which is `Nonneg` (`nn_sl`). Values of terms, numerals, sums and products of
`Nonneg` elements are `Nonneg`. Conversely `le_of_comb`: if `ι b − ι a = z` and `z` is `Nonneg`, then
`Γ ⊢ a ≤ b`. So an inequality follows from a *certificate* `z`: a combination of slacks of known
inequalities whose coefficients are values of terms (possibly products of slacks), such that
`ι b − ι a = z` is a ring identity. This is the inequality analogue of `linear_combination`.

* `ipra_le z` derives `Γ ⊢ le a b` from the certificate `z`, checking `ι b − ι a = z` by `ring`;
* `ipra_le z with e` checks `ι b − ι a = z` by `linear_combination e`, for certificates that also use
  derived equations (`natEq`);
* `ipra_nonneg` proves `Nonneg Γ z` for a `z` built from slacks, values of terms and numerals by
  `+`, `*` and natural powers.

For example, transitivity is `ipra_le sl h₁ + sl h₂`, and monotonicity of multiplication is
`ipra_le sl h₁ * sl h₂ + ι a * sl h₂ + ι c * sl h₁`.
-/

namespace LeanProofs.IPRA

open LeanProofs.ConciseIPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open PTm (pred monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- An element of the ring of differences that is the value of a term. -/
def Nonneg (Γ : List (Fm PTm n)) (z : Groth (Q Γ)) : Prop := ∃ t : PTm n, z = Groth.ι (Q.mk Γ t)

theorem nn_term (t : PTm n) : Nonneg Γ (Groth.ι (Q.mk Γ t)) := ⟨t, rfl⟩

theorem nn_zero : Nonneg Γ 0 := ⟨zero, by simp only [Q.mk_zero, map_zero]⟩

theorem nn_one : Nonneg Γ 1 := ⟨succ zero, by simp only [Q.mk_one, map_one]⟩

theorem nn_add {x y : Groth (Q Γ)} (hx : Nonneg Γ x) (hy : Nonneg Γ y) : Nonneg Γ (x + y) := by
  obtain ⟨s, rfl⟩ := hx; obtain ⟨t, rfl⟩ := hy
  exact ⟨s + t, by simp only [Q.mk_add, map_add]⟩

theorem nn_mul {x y : Groth (Q Γ)} (hx : Nonneg Γ x) (hy : Nonneg Γ y) : Nonneg Γ (x * y) := by
  obtain ⟨s, rfl⟩ := hx; obtain ⟨t, rfl⟩ := hy
  exact ⟨s * t, by simp only [Q.mk_mul, map_mul]⟩

theorem nn_natCast (k : ℕ) : Nonneg Γ (k : Groth (Q Γ)) :=
  ⟨PTm.num k, by simp only [Q.mk_num, map_natCast]⟩

theorem nn_ofNat (k : ℕ) [k.AtLeastTwo] : Nonneg Γ (OfNat.ofNat k : Groth (Q Γ)) := by
  have h : ((OfNat.ofNat k : ℕ) : Groth (Q Γ)) = OfNat.ofNat k := Nat.cast_ofNat
  rw [← h]
  exact nn_natCast _

theorem nn_pow {x : Groth (Q Γ)} (hx : Nonneg Γ x) (k : ℕ) : Nonneg Γ (x ^ k) := by
  induction k with
  | zero => rw [pow_zero]; exact nn_one
  | succ k ih => rw [pow_succ]; exact nn_mul ih hx

/-- The slack `b − a` of a derived inequality `a ≤ b`, in the ring of differences. -/
def sl {a b : PTm n} (_ : Γ ⊢[PRAAx] le a b) : Groth (Q Γ) := Groth.ι (Q.mk Γ b) - Groth.ι (Q.mk Γ a)

theorem sl_def {a b : PTm n} (h : Γ ⊢[PRAAx] le a b) :
    sl h = Groth.ι (Q.mk Γ b) - Groth.ι (Q.mk Γ a) := rfl

/-- The slack of a derived inequality is the value of the term `b ∸ a`. -/
theorem nn_sl {a b : PTm n} (h : Γ ⊢[PRAAx] le a b) : Nonneg Γ (sl h) := by
  refine ⟨monus b a, ?_⟩
  have e := natEq (eq_add_of_le h)
  simp only [Q.mk_add, map_add] at e
  rw [sl_def]
  linear_combination e

theorem le_of_nonneg {a b : PTm n} (h : Nonneg Γ (Groth.ι (Q.mk Γ b) - Groth.ι (Q.mk Γ a))) :
    Γ ⊢[PRAAx] le a b := by
  obtain ⟨d, hd⟩ := h
  refine le_of_eq_add (d := d) (deriveNat ?_)
  simp only [Q.mk_add, map_add]
  linear_combination hd

/-- An inequality from a certificate: `ι b − ι a` equals a `Nonneg` element `z`. -/
theorem le_of_comb {a b : PTm n} (z : Groth (Q Γ)) (hz : Groth.ι (Q.mk Γ b) - Groth.ι (Q.mk Γ a) = z)
    (h : Nonneg Γ z) : Γ ⊢[PRAAx] le a b :=
  le_of_nonneg (by rw [hz]; exact h)

end LeanProofs.IPRA

/-- Prove `Nonneg Γ z` for `z` built from slacks `sl h`, values of terms and numerals by `+`, `*` and
natural powers. -/
macro "ipra_nonneg" : tactic =>
  `(tactic| repeat (first
      | exact LeanProofs.IPRA.nn_sl _
      | exact LeanProofs.IPRA.nn_term _
      | exact LeanProofs.IPRA.nn_one
      | exact LeanProofs.IPRA.nn_zero
      | exact LeanProofs.IPRA.nn_ofNat _
      | exact LeanProofs.IPRA.nn_natCast _
      | assumption
      | apply LeanProofs.IPRA.nn_add
      | apply LeanProofs.IPRA.nn_mul
      | apply LeanProofs.IPRA.nn_pow))

/-- `ipra_le z` derives `Γ ⊢ le a b` from the certificate `z`, a combination of slacks `sl h` of derived
inequalities with coefficients that are values of terms, such that `ι b − ι a = z` is a ring identity.
`ipra_le z with e` checks that identity by `linear_combination e` instead, so that derived equations
can be used as well. -/
syntax "ipra_le " term (" with " term)? : tactic

/-- `ipra_le z using tac` checks `ι b − ι a = z` by the tactic `tac`, after the slacks have been unfolded
and `ipra_simps` has been applied. -/
syntax "ipra_le " term " using " tacticSeq : tactic

macro_rules
  | `(tactic| ipra_le $z) => `(tactic| (
      refine LeanProofs.IPRA.le_of_comb $z ?_ ?_
      · (try simp only [LeanProofs.IPRA.sl_def]); (try ipra_simps); ring
      · ipra_nonneg))
  | `(tactic| ipra_le $z with $e) => `(tactic| (
      refine LeanProofs.IPRA.le_of_comb $z ?_ ?_
      · (try simp only [LeanProofs.IPRA.sl_def]); (try ipra_simps)
        first | linear_combination ($e) | linear_combination -($e)
      · ipra_nonneg))
  | `(tactic| ipra_le $z using $tac) => `(tactic| (
      refine LeanProofs.IPRA.le_of_comb $z ?_ ?_
      · (try simp only [LeanProofs.IPRA.sl_def]); (try ipra_simps); ($tac)
      · ipra_nonneg))

namespace LeanProofs.IPRA

open LeanProofs.ConciseIPRA
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Checks of the certificate tactics -/

example {a b c : PTm n} (h₁ : Γ ⊢[PRAAx] le a b) (h₂ : Γ ⊢[PRAAx] le b c) : Γ ⊢[PRAAx] le a c := by
  ipra_le sl h₁ + sl h₂

example {a b c d : PTm n} (h₁ : Γ ⊢[PRAAx] le a b) (h₂ : Γ ⊢[PRAAx] le c d) :
    Γ ⊢[PRAAx] le (a * c) (b * d) := by
  ipra_le sl h₁ * sl h₂ + Groth.ι (Q.mk Γ a) * sl h₂ + Groth.ι (Q.mk Γ c) * sl h₁

example {a b c : PTm n} (h : Γ ⊢[PRAAx] le a b) (e : Γ ⊢[PRAAx] c ≐ b + b) :
    Γ ⊢[PRAAx] le (PTm.num 2 * a) c := by
  have e' := natEq e
  ipra_le 2 * sl h with e'

end LeanProofs.IPRA
