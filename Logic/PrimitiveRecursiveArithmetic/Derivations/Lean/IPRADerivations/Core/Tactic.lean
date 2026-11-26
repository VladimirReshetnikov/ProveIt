import IPRADerivations.Core.Integers
import IPRADerivations.Core.Header

/-!
# Conveniences for stating and deriving iPRA theorems

* `Fm.allN k φ` closes the last `k` free variables of `φ` by universal
  quantifiers, and `closeAll` turns an open theorem into the closed one.
* `ipra_simps` pushes `Q.mk`, `ZT.toZ` and `Groth.ι` through the term
  operations; `natEq` and `deriveNat` move natural-number equations between
  `Prf PRAAx` and the commutative ring `Groth (Q Γ)`.
* The tactic `ipra_ring` derives a natural-number or integer polynomial
  identity by `ring` in `Groth (Q Γ)`.
-/

namespace LeanProofs.IPRA

open LeanProofs.ConciseIPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)

/-- Universal closure over the last `k` free variables. -/
def allN {m : ℕ} : (k : ℕ) → Fm PTm (m + k) → Fm PTm m
  | 0, φ => φ
  | k + 1, φ => allN k (Fm.all φ)

/-- An open theorem gives its universal closure. -/
theorem closeAll {m : ℕ} (k : ℕ) {φ : Fm PTm (m + k)}
    (h : ([] : List (Fm PTm (m + k))) ⊢[PRAAx] φ) : ([] : List (Fm PTm m)) ⊢[PRAAx] allN k φ := by
  induction k with
  | zero => exact h
  | succ k ih => exact ih (.allI (by simpa using h))

/-- Universal closure of a formula over all its `k` free variables. -/
def univ : (k : ℕ) → Fm PTm k → Fm PTm 0
  | 0, φ => φ
  | k + 1, φ => univ k (Fm.all φ)

/-- An open theorem gives its universal closure. -/
theorem closeUniv (k : ℕ) {φ : Fm PTm k} (h : ([] : List (Fm PTm k)) ⊢[PRAAx] φ) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ k φ := by
  induction k with
  | zero => exact h
  | succ k ih => exact ih (.allI (by simpa using h))

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- A derived natural-number equation, as an equation in the ring `Groth (Q Γ)`. -/
theorem natEq {s t : PTm n} (h : Γ ⊢[PRAAx] s ≐ t) :
    Groth.ι (Q.mk Γ s) = Groth.ι (Q.mk Γ t) :=
  congrArg _ (Q.sound h)

/-- An equation in the ring `Groth (Q Γ)` gives a derivation. -/
theorem deriveNat {s t : PTm n} (h : Groth.ι (Q.mk Γ s) = Groth.ι (Q.mk Γ t)) :
    Γ ⊢[PRAAx] s ≐ t :=
  Q.exact (Groth.ι_injective h)

/-- Use a derived equation as a ring equation; the context is taken from the goal. -/
theorem withEq {s t : PTm n} {φ : Fm PTm n} (e : Γ ⊢[PRAAx] s ≐ t)
    (k : Groth.ι (Q.mk Γ s) = Groth.ι (Q.mk Γ t) → (Γ ⊢[PRAAx] φ)) : Γ ⊢[PRAAx] φ :=
  k (natEq e)

/-- `ι ∘ mk` applied to a variable. -/
abbrev V (Γ : List (Fm PTm n)) (i : Fin n) : Groth (Q Γ) := Groth.ι (Q.mk Γ (var i))

/-- The integer variable read from the natural-number variables `i` (positive
part) and `j` (negative part). -/
def ZT.var2 (i j : Fin n) : ZT n := ⟨var i, var j⟩

@[simp] theorem ZT.toZ_var2 (i j : Fin n) : ZT.toZ Γ (ZT.var2 i j) = V Γ i - V Γ j := rfl

end LeanProofs.IPRA

/-- Push `Q.mk`, `ZT.toZ` and `Groth.ι` through the term operations. -/
macro "ipra_simps" : tactic =>
  `(tactic| simp only [LeanProofs.IPRA.Q.mk_add, LeanProofs.IPRA.Q.mk_mul,
      LeanProofs.IPRA.Q.mk_succ, LeanProofs.IPRA.Q.mk_zero, LeanProofs.IPRA.Q.mk_one,
      LeanProofs.IPRA.Q.mk_num, map_add, map_mul, map_one, map_zero, map_natCast,
      LeanProofs.IPRA.ZT.toZ_add, LeanProofs.IPRA.ZT.toZ_mul, LeanProofs.IPRA.ZT.toZ_neg,
      LeanProofs.IPRA.ZT.toZ_sub, LeanProofs.IPRA.ZT.toZ_sq, LeanProofs.IPRA.ZT.toZ_ofNat,
      LeanProofs.IPRA.ZT.toZ_natLit, LeanProofs.IPRA.ZT.toZ_var2] at *)

/-- Derive a natural-number equation `s ≐ t` or an integer equation `ZT.eq u v`
that is a polynomial identity. -/
macro "ipra_ring" : tactic =>
  `(tactic| first
    | (apply LeanProofs.IPRA.ZT.derive; ipra_simps; ring)
    | (apply LeanProofs.IPRA.deriveNat; ipra_simps; ring))
