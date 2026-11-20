import IPRADerivations.Core.Powers
import IPRADerivations.Core.Parity
import IPRADerivations.Core.SumLemmas
import IPRADerivations.Core.BoundedSums
import IPRADerivations.Core.OrderCertificates

/-!
# The finite sums of the Khinchin second moment (`hurwitz_khinchin_ipra`, (K10))

Packet: `diophantine-number-theory/hurwitz_khinchin_ipra`, `khinchin.tex`, (K10): "We used only
`2 Σ_{k<ℓ} t_k t_ℓ ≤ S²` and the finite geometric sum `Σ_{k<ℓ} 4^{k−ℓ} ≤ 1/3`."

* `sq_sum`: `(Σ_{ℓ<N} t_ℓ)² = Σ_{ℓ<N} t_ℓ² + 2 Σ_{ℓ<N} t_ℓ (Σ_{k<ℓ} t_k)`, the exact identity behind
  `2 Σ_{k<ℓ} t_k t_ℓ ≤ S²` (`cross_le`);
* `geo`: `3 Σ_{j<J} 4^j + 1 = 4^J`, so `Σ_{j=1}^{J} 4^{−j} = (1 − 4^{−J})/3 < 1/3` (`geo_lt`:
  `3 Σ_{j<J} 4^j < 4^J`).

Both are quantifier-free inductions on the number of terms.
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.KhinchinMoment

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## The square of a sum -/

section Square

variable (t : PTm 2)

/-- `t_ℓ²`. -/
abbrev t2B : PTm 2 := t * t
/-- `t_ℓ Σ_{k<ℓ} t_k`. -/
abbrev crB : PTm 2 := t * ap2 (sumF t) (var 0) (var 1)

theorem inst2_crB (l x : PTm n) : inst2 (crB t) l x = inst2 t l x * ap2 (sumF t) l x := by
  simp [inst2, subst_ap2]

theorem inst2_t2B (l x : PTm n) : inst2 (t2B t) l x = inst2 t l x * inst2 t l x := by simp [inst2]

/-- The invariant `(Σ t)² = Σ t² + 2 Σ t_ℓ S_ℓ`. -/
def sqInv (N x : PTm n) : Fm PTm n :=
  ap2 (sumF t) N x * ap2 (sumF t) N x ≐ ap2 (sumF (t2B t)) N x + two * ap2 (sumF (crB t)) N x

@[simp] theorem subst_sqInv {k : ℕ} (σ : Fin n → PTm k) (N x : PTm n) :
    (sqInv t N x).subst σ = sqInv t (Syn.subst σ N) (Syn.subst σ x) := by
  simp [sqInv, subst_ap2]

theorem sq_step {N x : PTm n} (ih : Γ ⊢[PRAAx] sqInv t N x) : Γ ⊢[PRAAx] sqInv t (succ N) x := by
  have e0 := natEq (ih : Γ ⊢[PRAAx] ap2 (sumF t) N x * ap2 (sumF t) N x ≐
    ap2 (sumF (t2B t)) N x + two * ap2 (sumF (crB t)) N x)
  have e1 := natEq (sum_succ' (Γ := Γ) t N x)
  have e2 := natEq (sum_succ' (Γ := Γ) (t2B t) N x)
  have e3 := natEq (sum_succ' (Γ := Γ) (crB t) N x)
  rw [inst2_t2B] at e2
  rw [inst2_crB] at e3
  show Γ ⊢[PRAAx] ap2 (sumF t) (succ N) x * ap2 (sumF t) (succ N) x ≐
    ap2 (sumF (t2B t)) (succ N) x + two * ap2 (sumF (crB t)) (succ N) x
  apply deriveNat; ipra_simps
  linear_combination e0 + (𝔞 (ap2 (sumF t) (succ N) x) + 𝔞 (ap2 (sumF t) N x) + 𝔞 (inst2 t N x)) * e1 - e2 - 2 * e3

/-- `(Σ_{ℓ<N} t_ℓ)² = Σ_{ℓ<N} t_ℓ² + 2 Σ_{ℓ<N} t_ℓ (Σ_{k<ℓ} t_k)`. -/
theorem sq_sum (N x : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF t) N x * ap2 (sumF t) N x ≐ ap2 (sumF (t2B t)) N x + two * ap2 (sumF (crB t)) N x := by
  have hall : Γ ⊢[PRAAx] Fm.all (sqInv t (var 0) (Syn.shift x)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · rw [subst_sqInv]
      simp only [Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
      have a := natEq (sum_zero (Γ := Γ) t x)
      have b := natEq (sum_zero (Γ := Γ) (t2B t) x)
      have c := natEq (sum_zero (Γ := Γ) (crB t) x)
      show Γ ⊢[PRAAx] ap2 (sumF t) zero x * ap2 (sumF t) zero x ≐ ap2 (sumF (t2B t)) zero x + two * ap2 (sumF (crB t)) zero x
      apply deriveNat; ipra_simps
      linear_combination (𝔞 (ap2 (sumF t) zero x)) * a - b - 2 * c
    · rw [subst_sqInv]
      simp only [Syn.subst_var, Syn.repl_zero, subst_repl_shift]
      exact sq_step t Prf.hyp0
  have a := Prf.allE N hall
  rw [subst_sqInv] at a
  simp only [Syn.subst_inst_shift] at a
  exact a

/-- `2 Σ_{k<ℓ<N} t_k t_ℓ ≤ (Σ_{ℓ<N} t_ℓ)²`. -/
theorem cross_le (N x : PTm n) :
    Γ ⊢[PRAAx] le (two * ap2 (sumF (crB t)) N x) (ap2 (sumF t) N x * ap2 (sumF t) N x) := by
  have e := natEq (sq_sum (Γ := Γ) t N x)
  ipra_le 𝔞 (ap2 (sumF (t2B t)) N x) with e

end Square

/-! ## The geometric sum -/

/-- `4^j` over `0 = j`. -/
abbrev g4B : PTm 2 := pw (num 4) (var 0)

/-- The invariant `3 Σ_{j<J} 4^j + 1 = 4^J`. -/
def geoInv (J x : PTm n) : Fm PTm n := num 3 * ap2 (sumF g4B) J x + one ≐ pw (num 4) J

@[simp] theorem subst_geoInv {k : ℕ} (σ : Fin n → PTm k) (J x : PTm n) :
    (geoInv J x).subst σ = geoInv (Syn.subst σ J) (Syn.subst σ x) := by
  simp [geoInv, subst_ap2]

/-- `3 Σ_{j<J} 4^j + 1 = 4^J`. -/
theorem geo (J x : PTm n) : Γ ⊢[PRAAx] num 3 * ap2 (sumF g4B) J x + one ≐ pw (num 4) J := by
  have hall : Γ ⊢[PRAAx] Fm.all (geoInv (var 0) (Syn.shift x)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · rw [subst_geoInv]
      simp only [Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
      have a := natEq (sum_zero (Γ := Γ) g4B x)
      have b := natEq (pw_zero (Γ := Γ) (num 4 : PTm n))
      show Γ ⊢[PRAAx] num 3 * ap2 (sumF g4B) zero x + one ≐ pw (num 4) zero
      apply deriveNat; ipra_simps
      linear_combination 3 * a - b
    · rw [subst_geoInv]
      simp only [Syn.subst_var, Syn.repl_zero, subst_repl_shift]
      let Δ : List (Fm PTm (n + 1)) := geoInv (var 0) (Syn.shift x) :: Γ.map Fm.shift
      have e0 := natEq (Prf.hyp0 : Δ ⊢[PRAAx] num 3 * ap2 (sumF g4B) (var 0) (Syn.shift x) + one ≐ pw (num 4) (var 0))
      have e1 := natEq (sum_succ' (Γ := Δ) g4B (var 0) (Syn.shift x))
      have e2 := natEq (pw_succ (Γ := Δ) (num 4 : PTm (n + 1)) (var 0))
      rw [show inst2 g4B (var 0 : PTm (n + 1)) (Syn.shift x) = pw (num 4) (var 0) by simp [inst2]] at e1
      show Δ ⊢[PRAAx] num 3 * ap2 (sumF g4B) (succ (var 0)) (Syn.shift x) + one ≐ pw (num 4) (succ (var 0))
      apply deriveNat; ipra_simps
      linear_combination 4 * e0 + 3 * e1 - e2 - 3 * e0
  have a := Prf.allE J hall
  rw [subst_geoInv] at a
  simp only [Syn.subst_inst_shift] at a
  exact a

/-- `3 Σ_{j<J} 4^j < 4^J`, i.e. `Σ_{j=1}^{J} 4^{−j} < 1/3`. -/
theorem geo_lt (J x : PTm n) : Γ ⊢[PRAAx] lt (num 3 * ap2 (sumF g4B) J x) (pw (num 4) J) := by
  have e := natEq (geo (Γ := Γ) J x)
  ipra_le 0 with e

end LeanProofs.IPRA.DiophantineNumberTheory.KhinchinMoment
