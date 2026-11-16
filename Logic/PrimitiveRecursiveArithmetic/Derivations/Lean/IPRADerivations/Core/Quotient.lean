import IPRADerivations.Core.Semiring

/-!
# Terms modulo provable equality form a commutative semiring

For a context `Γ`, the relation `Γ ⊢[PRAAx] s ≐ t` is a congruence on `PTm n`
(`Core.Basic`), and by `Core.Semiring` the quotient `Q Γ` is a commutative
semiring with additive cancellation.

This turns derivations of polynomial identities into algebra: to derive
`Γ ⊢[PRAAx] s ≐ t` it suffices to show `Q.mk Γ s = Q.mk Γ t`, and after
`simp only [Q.mk_add, Q.mk_mul, ...]` this is an identity in a commutative
semiring, which Mathlib's `ring` proves. Hypotheses `Γ ⊢[PRAAx] u ≐ v` become
equations `Q.mk Γ u = Q.mk Γ v` usable by `rw`.

The result is still a derivation in `Prf PRAAx`: `Q.exact` returns one.
-/

namespace LeanProofs.IPRA

open LeanProofs.ConciseIPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)

variable {n : ℕ}

/-- Provable equality under `Γ`, as a setoid on terms. -/
def provSetoid (Γ : List (Fm PTm n)) : Setoid (PTm n) where
  r s t := Γ ⊢[PRAAx] s ≐ t
  iseqv := ⟨Prf.eqRefl, Prf.eqSymm, Prf.eqTrans⟩

/-- Terms modulo provable equality under `Γ`. -/
def Q (Γ : List (Fm PTm n)) : Type := Quotient (provSetoid Γ)

namespace Q

variable {Γ : List (Fm PTm n)}

/-- The class of a term. -/
def mk (Γ : List (Fm PTm n)) (t : PTm n) : Q Γ := Quotient.mk (provSetoid Γ) t

theorem sound {s t : PTm n} (h : Γ ⊢[PRAAx] s ≐ t) : mk Γ s = mk Γ t := Quotient.sound h

theorem exact {s t : PTm n} (h : mk Γ s = mk Γ t) : Γ ⊢[PRAAx] s ≐ t := Quotient.exact h

theorem eq_iff {s t : PTm n} : mk Γ s = mk Γ t ↔ (Γ ⊢[PRAAx] s ≐ t) := ⟨exact, sound⟩

@[elab_as_elim] theorem ind {motive : Q Γ → Prop} (h : ∀ t, motive (mk Γ t)) (q : Q Γ) :
    motive q := Quotient.ind h q

instance : Zero (Q Γ) := ⟨mk Γ zero⟩
instance : One (Q Γ) := ⟨mk Γ (succ zero)⟩
instance : Add (Q Γ) :=
  ⟨Quotient.map₂ (· + ·) fun _ _ h₁ _ _ h₂ => congrAdd h₁ h₂⟩
instance : Mul (Q Γ) :=
  ⟨Quotient.map₂ (· * ·) fun _ _ h₁ _ _ h₂ => congrMul h₁ h₂⟩

@[simp] theorem mk_add (a b : PTm n) : mk Γ (a + b) = mk Γ a + mk Γ b := rfl
@[simp] theorem mk_mul (a b : PTm n) : mk Γ (a * b) = mk Γ a * mk Γ b := rfl
@[simp] theorem mk_zero : mk Γ (zero : PTm n) = 0 := rfl
@[simp] theorem mk_one : mk Γ (succ zero : PTm n) = 1 := rfl
@[simp] theorem mk_succ (a : PTm n) : mk Γ (succ a) = mk Γ a + 1 := sound (succ_eq_add_one a)

instance : CommSemiring (Q Γ) where
  add_assoc a b c := by
    induction a using Q.ind; induction b using Q.ind; induction c using Q.ind
    exact sound (add_assoc _ _ _)
  zero_add a := by induction a using Q.ind; exact sound (zero_add _)
  add_zero a := by induction a using Q.ind; exact sound (add_zero _)
  add_comm a b := by
    induction a using Q.ind; induction b using Q.ind; exact sound (add_comm _ _)
  mul_assoc a b c := by
    induction a using Q.ind; induction b using Q.ind; induction c using Q.ind
    exact sound (mul_assoc _ _ _)
  one_mul a := by induction a using Q.ind; exact sound (one_mul _)
  mul_one a := by induction a using Q.ind; exact sound ((mul_comm _ _).eqTrans (one_mul _))
  zero_mul a := by induction a using Q.ind; exact sound (zero_mul _)
  mul_zero a := by induction a using Q.ind; exact sound (mul_zero _)
  left_distrib a b c := by
    induction a using Q.ind; induction b using Q.ind; induction c using Q.ind
    exact sound (mul_add _ _ _)
  right_distrib a b c := by
    induction a using Q.ind; induction b using Q.ind; induction c using Q.ind
    exact sound (add_mul _ _ _)
  mul_comm a b := by
    induction a using Q.ind; induction b using Q.ind; exact sound (mul_comm _ _)
  nsmul := nsmulRec
  npow := npowRec

instance : IsCancelAdd (Q Γ) where
  add_left_cancel a b c h := by
    induction a using Q.ind; induction b using Q.ind; induction c using Q.ind
    exact sound (add_left_cancel (exact h))
  add_right_cancel a b c h := by
    induction a using Q.ind; induction b using Q.ind; induction c using Q.ind
    exact sound (add_right_cancel (exact h))

/-- Numerals go to the corresponding casts. -/
@[simp] theorem mk_num (k : ℕ) : mk Γ (PTm.num k : PTm n) = (k : Q Γ) := by
  induction k with
  | zero => rfl
  | succ k ih => simp [PTm.num, ih]

end Q

end LeanProofs.IPRA
