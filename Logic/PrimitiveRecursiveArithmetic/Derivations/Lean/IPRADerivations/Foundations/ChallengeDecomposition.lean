import IPRADerivations.Foundations.BoundedCover

/-!
# Finite challenge decomposition

Packet: `ipra_strategy_framework`, `report.tex`, Proposition `challenge`. For a contract

  `𝒞(a) ≡ ∀ q < Q(a) ∃ z < Z(a, q) ∀ e < E(a, q, z) R(a, q, z, e)`

with `R` bounded (a `BF`, parameters packed as `⟨e, ⟨z, ⟨q, a⟩⟩⟩`), iPRA proves that exactly one of
two certificates is produced by primitive-recursive constructors:

* (A) `challenge_A`: if `𝒞(a)`, then for each `q < Q(a)` the selected `z(a, q)` (the least witness of
  bounded choice) satisfies `z(a, q) < Z(a, q)` and every test `e < E(a, q, z(a, q))`;
* (B) `challenge_B_q`, `challenge_B_e`: if `¬𝒞(a)`, the least failing `q₀(a) < Q(a)` and, for every
  `z < Z(a, q₀)`, the least failing test `e₀(a, z) < E(a, q₀, z)` with `¬R(a, q₀, z, e₀(a, z))`;
* `challenge_dec`: `𝒞(a) ∨ ¬𝒞(a)`, so one of the cases applies, and they exclude each other.

All selections are bounded least-success searches; the case split is on the contract's bit.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.ChallengeDecomposition

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.BoundedFormulas
open LeanProofs.IPRA.Foundations.BoundedReflection (all_fail)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable (Q Z E : PTm 1) (R : BF)

/-- `∀ e < E R` at `⟨z, ⟨q, a⟩⟩`. -/
abbrev T : BF := .all E R
/-- `∃ z < Z ∀ e < E R` at `⟨q, a⟩`. -/
abbrev U : BF := .ex Z (T E R)
/-- The contract `𝒞` at `a`. -/
abbrev Ctr : BF := .all Q (U Z E R)

/-- `z(a, q)`. -/
abbrev zW {m : ℕ} (q a : PTm m) : PTm m := bfWit Z (T E R) (pairT q a)
/-- `q₀(a)`: the least `q < Q(a)` with no `z`. -/
abbrev q0 {m : ℕ} (a : PTm m) : PTm m := Search.mu (body (U Z E R)) (at1 Q a) a
/-- `e₀(a, z)`: the least failing test at `⟨z, ⟨q₀(a), a⟩⟩`. -/
abbrev e0 {m : ℕ} (z a : PTm m) : PTm m :=
  Search.mu (body R) (at1 E (pairT z (pairT (q0 Q Z E R a) a))) (pairT z (pairT (q0 Q Z E R a) a))

variable {m : ℕ} {Δ : List (Fm PTm m)}

theorem challenge_dec (a : PTm m) : Δ ⊢[PRAAx] fmAt (Ctr Q Z E R) m a ⋎ neg (fmAt (Ctr Q Z E R) m a) :=
  bf_dec _ a

/-- A false bounded formula has bit `0`. -/
theorem bit_zero_of_neg (A : BF) {y : PTm m} (h : Δ ⊢[PRAAx] neg (fmAt A m y)) : Δ ⊢[PRAAx] bitAt A m y ≐ zero :=
  .orE (bf_cases A y) Prf.hyp0 (.botE _ (.impE h.wk (.impE (reflect A y).2.1 Prf.hyp0)))

/-- A bit `0` makes the bounded formula false. -/
theorem neg_of_bit_zero (A : BF) {y : PTm m} (h : Δ ⊢[PRAAx] bitAt A m y ≐ zero) : Δ ⊢[PRAAx] neg (fmAt A m y) :=
  .impI (clash _ h.wk (.impE (reflect A y).1 Prf.hyp0))

/-- Case (A): every demanded precision `q < Q(a)` has its selected witness `z(a, q)`. -/
theorem challenge_A {a q : PTm m} (h : Δ ⊢[PRAAx] fmAt (Ctr Q Z E R) m a) (hq : Δ ⊢[PRAAx] lt q (at1 Q a)) :
    Δ ⊢[PRAAx] lt (zW Z E R q a) (at1 Z (pairT q a)) ⋏ fmAt (T E R) m (pairT (zW Z E R q a) (pairT q a)) := by
  have h' : Δ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift (at1 Q a)) ⟶
      fmAt (U Z E R) (m + 1) (pairT (var 0) (Syn.shift a))) := h
  have i := Prf.allE q h'
  simp only [Fm.subst_imp, subst_lt, Syn.subst_var, Syn.inst_zero, fmAt_subst, subst_pairT, Syn.subst_shift] at i
  simp only [Syn.inst, Fin.cases_succ, Syn.subst_id] at i
  exact bf_choice Z (T E R) (pairT q a) (.impE i hq)

/-- Case (B): the least failing precision `q₀(a) < Q(a)`, for which no `z` works. -/
theorem challenge_B_q {a : PTm m} (h : Δ ⊢[PRAAx] neg (fmAt (Ctr Q Z E R) m a)) :
    Δ ⊢[PRAAx] lt (q0 Q Z E R a) (at1 Q a) ⋏ neg (fmAt (U Z E R) m (pairT (q0 Q Z E R a) a)) := by
  have b : Δ ⊢[PRAAx] BoundedReflection.allB (body (U Z E R)) (at1 Q a) a ≐ zero := bit_zero_of_neg _ h
  have f := all_fail _ b
  have g := Prf.andE₂ f
  rw [inst2_body] at g
  exact .andI (Prf.andE₁ f) (neg_of_bit_zero _ g)

/-- Case (B): every candidate `z < Z(a, q₀)` fails the least test `e₀(a, z) < E(a, q₀, z)`. -/
theorem challenge_B_e {a z : PTm m} (h : Δ ⊢[PRAAx] neg (fmAt (Ctr Q Z E R) m a))
    (hz : Δ ⊢[PRAAx] lt z (at1 Z (pairT (q0 Q Z E R a) a))) :
    Δ ⊢[PRAAx] lt (e0 Q Z E R z a) (at1 E (pairT z (pairT (q0 Q Z E R a) a))) ⋏
      neg (fmAt R m (pairT (e0 Q Z E R z a) (pairT z (pairT (q0 Q Z E R a) a)))) := by
  have nU : Δ ⊢[PRAAx] neg (Fm.ex (lt (var 0) (Syn.shift (at1 Z (pairT (q0 Q Z E R a) a))) ⋏
      fmAt (T E R) (m + 1) (pairT (var 0) (Syn.shift (pairT (q0 Q Z E R a) a))))) :=
    Prf.andE₂ (challenge_B_q Q Z E R h)
  have nT : Δ ⊢[PRAAx] neg (fmAt (T E R) m (pairT z (pairT (q0 Q Z E R a) a))) := by
    refine .impI (.impE nU.wk (Prf.exI z ?_))
    simp only [Fm.subst_and, subst_lt, fmAt_subst, subst_pairT, Syn.subst_var, Syn.inst_zero, Syn.subst_shift,
      Syn.inst, Fin.cases_succ, Syn.subst_id]
    exact .andI hz.wk Prf.hyp0
  have b : Δ ⊢[PRAAx] BoundedReflection.allB (body R) (at1 E (pairT z (pairT (q0 Q Z E R a) a)))
      (pairT z (pairT (q0 Q Z E R a) a)) ≐ zero := bit_zero_of_neg _ nT
  have f := all_fail _ b
  have g := Prf.andE₂ f
  rw [inst2_body] at g
  exact .andI (Prf.andE₁ f) (neg_of_bit_zero _ g)

end LeanProofs.IPRA.Foundations.ChallengeDecomposition
