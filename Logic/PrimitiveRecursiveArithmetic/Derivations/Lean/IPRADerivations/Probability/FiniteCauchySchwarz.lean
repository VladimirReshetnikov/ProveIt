import IPRADerivations.DiophantineNumberTheory.KhinchinBadBound
import IPRADerivations.Core.OrderCertificates

/-!
# Finite weighted Cauchy–Schwarz (`hurwitz_khinchin_ipra`, (K11))

Packet: `diophantine-number-theory/hurwitz_khinchin_ipra`, `khinchin.tex`, §"A finite block covers a fixed
fraction of every interval": "finite weighted Cauchy–Schwarz says `(∫F)² ≤ |{F > 0}| ∫F²`. On the endpoint
partition this is the elementary identity that the difference between the right and left sides is
`Σ_{i<j} w_i w_j (v_i − v_j)² ≥ 0`, after omitting the cells with value zero."

For bodies `w` (the cell weights) and `v` (the values) and every `N`:

  `(Σ_{i<N} w_i v_i)² ≤ (Σ_{i<N} w_i) (Σ_{i<N} w_i v_i²)`                        (`cauchy_schwarz`),

by a quantifier-free induction on `N` (`cs_step`): adding a cell `(w, v)` adds
`w (Σ_j w_j v_j² + v² Σ_j w_j − 2v Σ_j w_j v_j) = w Σ_j w_j (v_j − v)²` to the difference
(`inner_le`, summed from `dist(a, b)² + 2ab = a² + b²`, `dist_sq`, by `KhinchinBadBound.sum_lin_le`).
With the weights `w_i [v_i > 0]` this is the packet's `(∫F)² ≤ |{F > 0}| ∫F²`.
-/

namespace LeanProofs.IPRA.Probability.FiniteCauchySchwarz

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.DiophantineNumberTheory.KhinchinBadBound (sum_lin_le)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `|a − b|`. -/
abbrev dist (a b : PTm n) : PTm n := monus a b + monus b a

/-- `|a − b|² + 2ab = a² + b²`. -/
theorem dist_sq (a b : PTm n) : Γ ⊢[PRAAx] dist a b * dist a b + two * a * b ≐ a * a + b * b := by
  refine .orE (lt_or_le a b) ?_ ?_
  · let Δ : List (Fm PTm n) := lt a b :: Γ
    have hab : Δ ⊢[PRAAx] le a b := le_trans (le_succ_self a) Prf.hyp0
    have e := natEq (eq_add_of_le hab)
    have ez := natEq (hab : Δ ⊢[PRAAx] monus a b ≐ zero)
    apply deriveNat; ipra_simps
    linear_combination (𝔞 (monus a b) + 2 * 𝔞 (monus b a)) * ez + (𝔞 a - 𝔞 b - 𝔞 (monus b a)) * e
  · let Δ : List (Fm PTm n) := le b a :: Γ
    have hba : Δ ⊢[PRAAx] le b a := Prf.hyp0
    have e := natEq (eq_add_of_le hba)
    have ez := natEq (hba : Δ ⊢[PRAAx] monus b a ≐ zero)
    apply deriveNat; ipra_simps
    linear_combination (𝔞 (monus b a) + 2 * 𝔞 (monus a b)) * ez + (𝔞 b - 𝔞 a - 𝔞 (monus a b)) * e

section CS

variable (w v : PTm 2)

/-- `w_i v_i`. -/
abbrev wvB : PTm 2 := w * v
/-- `w_i v_i²`. -/
abbrev wv2B : PTm 2 := w * (v * v)

theorem inst2_wvB (i x : PTm n) : inst2 (wvB w v) i x = inst2 w i x * inst2 v i x := by simp [inst2]
theorem inst2_wv2B (i x : PTm n) : inst2 (wv2B w v) i x = inst2 w i x * (inst2 v i x * inst2 v i x) := by
  simp [inst2]

/-- `2u Σ_{j<N} w_j v_j ≤ Σ_{j<N} w_j v_j² + u² Σ_{j<N} w_j`, i.e. `Σ_j w_j (v_j − u)² ≥ 0`. -/
theorem inner_le (u N x : PTm n) :
    Γ ⊢[PRAAx] le (two * u * ap2 (sumF (wvB w v)) N x)
      (one * ap2 (sumF (wv2B w v)) N x + u * u * ap2 (sumF w) N x) := by
  refine sum_lin_le (wvB w v) (wv2B w v) w (two * u) one (u * u) x N (.allI (.impI ?_))
  rw [inst2_wvB, inst2_wv2B, show Syn.shift (two * u) = two * Syn.shift u by simp [Syn.shift],
    show Syn.shift (one : PTm n) = one by simp [Syn.shift],
    show Syn.shift (u * u) = Syn.shift u * Syn.shift u by simp [Syn.shift]]
  have e := natEq (dist_sq (Γ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift)
    (inst2 v (var 0) (Syn.shift x)) (Syn.shift u))
  ipra_le 𝔞 (inst2 w (var 0) (Syn.shift x)) * 𝔞 (dist (inst2 v (var 0) (Syn.shift x)) (Syn.shift u)) *
      𝔞 (dist (inst2 v (var 0) (Syn.shift x)) (Syn.shift u))
    with 𝔞 (inst2 w (var 0) (Syn.shift x)) * e

/-- The invariant: `C(N)² ≤ A(N) B(N)`. -/
def csInv (N x : PTm n) : Fm PTm n :=
  le (ap2 (sumF (wvB w v)) N x * ap2 (sumF (wvB w v)) N x) (ap2 (sumF w) N x * ap2 (sumF (wv2B w v)) N x)

@[simp] theorem subst_csInv {k : ℕ} (σ : Fin n → PTm k) (N x : PTm n) :
    (csInv w v N x).subst σ = csInv w v (Syn.subst σ N) (Syn.subst σ x) := by
  simp [csInv, subst_ap2]

theorem cs_base (x : PTm n) : Γ ⊢[PRAAx] csInv w v zero x := by
  have a := natEq (sum_zero (Γ := Γ) (wvB w v) x)
  have b := natEq (sum_zero (Γ := Γ) w x)
  have c := natEq (sum_zero (Γ := Γ) (wv2B w v) x)
  show Γ ⊢[PRAAx] le (ap2 (sumF (wvB w v)) zero x * ap2 (sumF (wvB w v)) zero x)
    (ap2 (sumF w) zero x * ap2 (sumF (wv2B w v)) zero x)
  ipra_le 0 using linear_combination (𝔞 (ap2 (sumF (wv2B w v)) zero x)) * b - (𝔞 (ap2 (sumF (wvB w v)) zero x)) * a

theorem cs_step {N x : PTm n} (ih : Γ ⊢[PRAAx] csInv w v N x) : Γ ⊢[PRAAx] csInv w v (succ N) x := by
  have ih' : Γ ⊢[PRAAx] le (ap2 (sumF (wvB w v)) N x * ap2 (sumF (wvB w v)) N x)
      (ap2 (sumF w) N x * ap2 (sumF (wv2B w v)) N x) := ih
  have hi := inner_le (Γ := Γ) w v (inst2 v N x) N x
  have eA := natEq (sum_succ' (Γ := Γ) w N x)
  have eB := natEq (sum_succ' (Γ := Γ) (wv2B w v) N x)
  have eC := natEq (sum_succ' (Γ := Γ) (wvB w v) N x)
  rw [inst2_wv2B] at eB
  rw [inst2_wvB] at eC
  show Γ ⊢[PRAAx] le (ap2 (sumF (wvB w v)) (succ N) x * ap2 (sumF (wvB w v)) (succ N) x)
    (ap2 (sumF w) (succ N) x * ap2 (sumF (wv2B w v)) (succ N) x)
  ipra_le sl ih' + 𝔞 (inst2 w N x) * sl hi
    with 𝔞 (ap2 (sumF (wv2B w v)) (succ N) x) * eA +
      (𝔞 (ap2 (sumF w) N x) + 𝔞 (inst2 w N x)) * eB -
      (𝔞 (ap2 (sumF (wvB w v)) (succ N) x) + 𝔞 (ap2 (sumF (wvB w v)) N x) +
        𝔞 (inst2 w N x) * 𝔞 (inst2 v N x)) * eC

/-- Finite weighted Cauchy–Schwarz: `(Σ_{i<N} w_i v_i)² ≤ (Σ_{i<N} w_i)(Σ_{i<N} w_i v_i²)`. -/
theorem cauchy_schwarz (N x : PTm n) :
    Γ ⊢[PRAAx] le (ap2 (sumF (wvB w v)) N x * ap2 (sumF (wvB w v)) N x)
      (ap2 (sumF w) N x * ap2 (sumF (wv2B w v)) N x) := by
  have hall : Γ ⊢[PRAAx] Fm.all (csInv w v (var 0) (Syn.shift x)) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · rw [subst_csInv]
      simp only [Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
      exact cs_base w v _
    · rw [subst_csInv]
      simp only [Syn.subst_var, Syn.repl_zero, subst_repl_shift]
      exact cs_step w v Prf.hyp0
  have a := Prf.allE N hall
  rw [subst_csInv] at a
  simp only [Syn.subst_inst_shift] at a
  exact a

end CS

end LeanProofs.IPRA.Probability.FiniteCauchySchwarz
