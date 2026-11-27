import IPRADerivations.Foundations.LeastBoundedWitness
import IPRADerivations.Core.OrderCertificates

/-!
# Bounded search driven by a decreasing rank

Packet: `foundations/ipra_finite_use_framework_2026-11-15`, Theorem `thm:rank-metastability`
("Rank-to-metastability"): given a ranked instability certificate, the iteration `n_0 = 0`,
`n_{t+1} = n_t + g(n_t) + 1` finds a stable window by some `t ≤ R(k, g)`; the selector and the bound are
primitive recursive.

Abstractly: a test `b(t, x)` (zero when the window examined at step `t` is stable) and a rank `ρ(t, x)` such
that an unstable step lowers the rank, `b(t, x) = 0 ∨ ρ(t + 1, x) < ρ(t, x)` for all `t`. Then the least
search over `t ≤ R`, with `R ≥ ρ(0, x)`, succeeds.

* `ranked_inv`: for every `t`, `μ_t < t ∨ ρ(t) + t ≤ R`, where `μ_t = Search.mu b t x`: either a stable step
  was already found, or the rank has dropped by at least the number of steps. A quantifier-free disjunction,
  proved by induction without contradiction;
* `ranked_search`: `μ = Search.mu b (R + 1) x` satisfies `μ ≤ R` and `b(μ, x) = 0`, and it is the least such
  step (`Search.search_minimal`).

The window iteration `n_t` and the instability certificate of the packet are data of the application; they
enter through the bodies `b` and `ρ`.
-/

namespace LeanProofs.IPRA.Foundations.RankedSearch

open_ipra exports
open LeanProofs.IPRA.Search (mu search_found)
open LeanProofs.IPRA.Foundations.LeastBoundedWitness (accepted_of_lt)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

section Search

variable {b ρ : PTm 2} {x R : PTm n}

theorem rs_base (hR : Γ ⊢[PRAAx] le (inst2 ρ zero x) R) :
    Γ ⊢[PRAAx] lt (mu b zero x) zero ⋎ le (inst2 ρ zero x + zero) R :=
  .orI₂ (by ipra_le sl hR)

theorem rs_step {t : PTm n}
    (hd : Γ ⊢[PRAAx] (inst2 b t x ≐ zero) ⋎ lt (inst2 ρ (succ t) x) (inst2 ρ t x))
    (ih : Γ ⊢[PRAAx] lt (mu b t x) t ⋎ le (inst2 ρ t x + t) R) :
    Γ ⊢[PRAAx] lt (mu b (succ t) x) (succ t) ⋎ le (inst2 ρ (succ t) x + succ t) R := by
  refine .orE ih ?_ ?_
  · have h0 : (lt (mu b t x) t :: Γ) ⊢[PRAAx] lt (mu b t x) t := Prf.hyp0
    have sf := search_found (accepted_of_lt h0) (lt_of_lt_of_le h0 (le_succ_self t))
    exact .orI₁ (Prf.andE₁ sf)
  · refine .orE hd.wk ?_ ?_
    · have hb : ((inst2 b t x ≐ zero) :: le (inst2 ρ t x + t) R :: Γ) ⊢[PRAAx] inst2 b t x ≐ zero :=
        Prf.hyp0
      exact .orI₁ (Prf.andE₁ (search_found hb (le_refl (succ t))))
    · have hl : (lt (inst2 ρ (succ t) x) (inst2 ρ t x) :: le (inst2 ρ t x + t) R :: Γ) ⊢[PRAAx]
          le (succ (inst2 ρ (succ t) x)) (inst2 ρ t x) := Prf.hyp0
      have hr : (lt (inst2 ρ (succ t) x) (inst2 ρ t x) :: le (inst2 ρ t x + t) R :: Γ) ⊢[PRAAx]
          le (inst2 ρ t x + t) R := Prf.hyp1
      exact .orI₂ (by ipra_le sl hl + sl hr)

/-- For every `t`: a stable step below `t` has been found, or `ρ(t) + t ≤ R`. -/
theorem ranked_inv (hR : Γ ⊢[PRAAx] le (inst2 ρ zero x) R)
    (hd : Γ ⊢[PRAAx] Fm.all ((inst2 b (var 0) (Syn.shift x) ≐ zero) ⋎
      lt (inst2 ρ (succ (var 0)) (Syn.shift x)) (inst2 ρ (var 0) (Syn.shift x)))) :
    Γ ⊢[PRAAx] Fm.all (lt (mu b (var 0) (Syn.shift x)) (var 0) ⋎
      le (inst2 ρ (var 0) (Syn.shift x) + var 0) (Syn.shift R)) := by
  refine PRA.qfInd _ ⟨lt_QF _ _, le_QF _ _⟩ ?_ ?_
  · simp only [Fm.subst_or, subst_le, subst_lt, subst_ap2, subst_inst2, PTm.subst_add, Syn.subst_var,
      Syn.inst_zero, Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact rs_base hR
  · simp only [Fm.subst_or, subst_le, subst_lt, subst_ap2, subst_inst2, PTm.subst_add, Syn.subst_var,
      Syn.repl_zero, subst_repl_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact rs_step hd.allOpen.wk Prf.hyp0

/-- `thm:rank-metastability`: the least search over `t ≤ R` finds a stable step. -/
theorem ranked_search (hR : Γ ⊢[PRAAx] le (inst2 ρ zero x) R)
    (hd : Γ ⊢[PRAAx] Fm.all ((inst2 b (var 0) (Syn.shift x) ≐ zero) ⋎
      lt (inst2 ρ (succ (var 0)) (Syn.shift x)) (inst2 ρ (var 0) (Syn.shift x)))) :
    Γ ⊢[PRAAx] lt (mu b (succ R) x) (succ R) ⋏ (inst2 b (mu b (succ R) x) x ≐ zero) := by
  have a := Prf.allE (succ R) (ranked_inv hR hd)
  simp only [Fm.subst_or, subst_le, subst_lt, subst_ap2, subst_inst2, PTm.subst_add, Syn.subst_var,
    Syn.inst_zero, Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ] at a
  have hlt : Γ ⊢[PRAAx] lt (mu b (succ R) x) (succ R) := by
    refine .orE a Prf.hyp0 ?_
    have h : (le (inst2 ρ (succ R) x + succ R) R :: Γ) ⊢[PRAAx] le (inst2 ρ (succ R) x + succ R) R :=
      Prf.hyp0
    have bad : (le (inst2 ρ (succ R) x + succ R) R :: Γ) ⊢[PRAAx] le (succ R) R := by
      ipra_le sl h + 𝔟 (inst2 ρ (succ R) x)
    exact lt_irrefl R _ bad
  exact .andI hlt (accepted_of_lt hlt)

end Search

end LeanProofs.IPRA.Foundations.RankedSearch
