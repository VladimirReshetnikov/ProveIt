import IPRADerivations.Core.SumOrder
import IPRADerivations.Core.SumReflect
import IPRADerivations.Core.Pairing
import IPRADerivations.Core.LinearCombination

/-!
# Summing a pointwise linear relation (`ipra_coherent_methods_2026-11-15`, `prop:weighted-dimension`)

Packet: `foundations/ipra_coherent_methods_2026-11-15`, proposition `prop:weighted-dimension`:
"Write `L - d j = m q_j + r_j` ... Summing these `m` equations gives ... Every calculation is an
identity of finite sums".

The summation step, separated from the particular equations:

* `sum_linear`: if `A_j + λ + α B_j = κ + β E_j + F_j` for every `j < N`, then
  `∑ A + N λ + α ∑ B = N κ + β ∑ E + ∑ F` (sums over `j < N`). The hypothesis is a bounded
  universal statement; the proof is quantifier-free induction in a context containing it;
* `tri`: `2 ∑_{j<N} j + N = N²`;
* `bd X`, `bd_at`: a body reading three parameters `L`, `m`, `d` from a packed pair, with its
  evaluation, so that bodies can be written as terms in four variables.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.SumLinear

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {k : ℕ} {Γ : List (Fm PTm k)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## A pointwise linear relation, summed -/

/-- The induction formula; variable `0` is the upper limit of the sums. -/
abbrev linF (A B E F : PTm 2) (N lam al kap be x : PTm k) : Fm PTm (k + 1) :=
  le (var 0) (Syn.shift N) ⟶
    (ap2 (sumF A) (var 0) (Syn.shift x) + var 0 * Syn.shift lam +
        Syn.shift al * ap2 (sumF B) (var 0) (Syn.shift x) ≐
      var 0 * Syn.shift kap + Syn.shift be * ap2 (sumF E) (var 0) (Syn.shift x) +
        ap2 (sumF F) (var 0) (Syn.shift x))

/-- `∑ A + N λ + α ∑ B = N κ + β ∑ E + ∑ F` from the same relation at every `j < N`. -/
theorem sum_linear (A B E F : PTm 2) {N lam al kap be x : PTm k}
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      (inst2 A (var 0) (Syn.shift x) + Syn.shift lam +
          Syn.shift al * inst2 B (var 0) (Syn.shift x) ≐
        Syn.shift kap + Syn.shift be * inst2 E (var 0) (Syn.shift x) +
          inst2 F (var 0) (Syn.shift x)))) :
    Γ ⊢[PRAAx] ap2 (sumF A) N x + N * lam + al * ap2 (sumF B) N x ≐
      N * kap + be * ap2 (sumF E) N x + ap2 (sumF F) N x := by
  have hall : Γ ⊢[PRAAx] Fm.all (linF A B E F N lam al kap be x) := by
    refine PRA.qfInd _ ⟨le_QF _ _, trivial⟩ ?_ ?_
    · simp only [Fm.subst_imp, Fm.subst_eq, subst_le, subst_ap2, PTm.subst_add, PTm.subst_mul,
        Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero]
      refine .impI ?_
      ipra_lc natEq (sum_zero (Γ := le zero N :: Γ) A x) + 𝔞 al * natEq (sum_zero (Γ := le zero N :: Γ) B x) -
        𝔞 be * natEq (sum_zero (Γ := le zero N :: Γ) E x) - natEq (sum_zero (Γ := le zero N :: Γ) F x)
    · simp only [Fm.subst_imp, Fm.subst_eq, subst_le, subst_ap2, PTm.subst_add, PTm.subst_mul,
        Syn.subst_var, Syn.repl_zero, subst_repl_shift, ConciseIPRA.PTm.subst_zero,
        ConciseIPRA.PTm.subst_succ]
      refine .impI ?_
      have hm : (le (succ (var 0)) (Syn.shift N) :: linF A B E F N lam al kap be x ::
          Γ.map Fm.shift) ⊢[PRAAx] le (var 0) (Syn.shift N) :=
        le_trans (le_succ_self _) Prf.hyp0
      ipra_lc natEq (sum_succ' (Γ := le (succ (var 0)) (Syn.shift N) :: linF A B E F N lam al kap be x :: Γ.map Fm.shift) A (var 0) (Syn.shift x)) +
        𝔞 (Syn.shift al) * natEq (sum_succ' (Γ := le (succ (var 0)) (Syn.shift N) :: linF A B E F N lam al kap be x :: Γ.map Fm.shift) B (var 0) (Syn.shift x)) -
        𝔞 (Syn.shift be) * natEq (sum_succ' (Γ := le (succ (var 0)) (Syn.shift N) :: linF A B E F N lam al kap be x :: Γ.map Fm.shift) E (var 0) (Syn.shift x)) -
        natEq (sum_succ' (Γ := le (succ (var 0)) (Syn.shift N) :: linF A B E F N lam al kap be x :: Γ.map Fm.shift) F (var 0) (Syn.shift x)) +
        natEq (Prf.impE Prf.hyp1 hm) +
        natEq (Prf.impE h.allOpen.wk.wk (Prf.hyp0 (Γ := linF A B E F N lam al kap be x :: Γ.map Fm.shift) (φ := le (succ (var 0)) (Syn.shift N))))
  have h2 := Prf.allE N hall
  simp only [Fm.subst_imp, Fm.subst_eq, subst_le, subst_ap2, PTm.subst_add, PTm.subst_mul,
    Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero] at h2
  exact .impE h2 (le_refl N)

/-! ## The triangular sum -/

/-- The body `j`. -/
def idB : PTm 2 := var 0

theorem inst2_idB (j x : PTm k) : inst2 idB j x = j := by simp [inst2, idB]

/-- Variables: `0 = N`, `1 = x`. -/
private abbrev triF : Fm PTm 2 :=
  ap2 (sumF idB) (var 0) (var 1) + ap2 (sumF idB) (var 0) (var 1) + var 0 ≐ var 0 * var 0

private theorem tri₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] triF := by
  refine ind _ trivial ?_ ?_
  · ipra_lc [Fm.subst_eq, subst_ap2, PTm.subst_add, PTm.subst_mul, Syn.subst_var, Syn.inst_zero, Syn.inst_one, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ] 2 * natEq (sum_zero (Γ := ([] : List (Fm PTm 1))) idB (var 0))
  · simp only [Fm.subst_eq, subst_ap2, PTm.subst_add, PTm.subst_mul, Syn.subst_var,
      Syn.repl_zero, repl_one, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    have ih : [triF] ⊢[PRAAx]
        ap2 (sumF idB) (var 0) (var 1) + ap2 (sumF idB) (var 0) (var 1) + var 0 ≐
          var 0 * var 0 := Prf.hyp0
    have s₀ := sum_succ' (Γ := [triF]) idB (var 0) (var 1)
    rw [inst2_idB] at s₀
    ipra_lc 2 * natEq s₀ + natEq ih

/-- `2 ∑_{j<N} j + N = N²`. -/
theorem tri (N x : PTm k) :
    Γ ⊢[PRAAx] ap2 (sumF idB) N x + ap2 (sumF idB) N x + N ≐ N * N := by
  have i := inst (Γ := Γ) tri₀ (![N, x] : Fin 2 → PTm k)
  simpa using i

/-! ## Bodies with three packed parameters -/

/-- The body reading `1 = L`, `2 = m`, `3 = d` of a four-variable term from the packed
parameter `⟨L, ⟨m, d⟩⟩`. -/
def bd (X : PTm 4) : PTm 2 :=
  Syn.subst ![var 0, fstT (var 1), fstT (sndT (var 1)), sndT (sndT (var 1))] X

theorem bd_at (X : PTm 4) (j L m d : PTm k) :
    Γ ⊢[PRAAx] inst2 (bd X) j (pairT L (pairT m d)) ≐ Syn.subst ![j, L, m, d] X := by
  have e₁ : inst2 (bd X) j (pairT L (pairT m d)) =
      Syn.subst ![j, fstT (pairT L (pairT m d)), fstT (sndT (pairT L (pairT m d))),
        sndT (sndT (pairT L (pairT m d)))] X := by
    simp only [inst2, bd, Syn.subst_subst]
    congr 1; funext l; fin_cases l <;> simp
  rw [e₁]
  have s₁ : Γ ⊢[PRAAx] sndT (pairT L (pairT m d)) ≐ pairT m d := snd_pair _ _
  exact Prf.eqCongr _ fun l => by
    fin_cases l
    · exact .eqRefl _
    · exact fst_pair _ _
    · exact (congrFst s₁).eqTrans (fst_pair _ _)
    · exact (congrSnd s₁).eqTrans (snd_pair _ _)

end LeanProofs.IPRA.Foundations.SumLinear
