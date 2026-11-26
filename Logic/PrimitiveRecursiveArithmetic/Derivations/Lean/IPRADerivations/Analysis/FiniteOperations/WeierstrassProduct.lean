import IPRADerivations.Core.OrderCertificates
import IPRADerivations.Core.Powers
import IPRADerivations.Core.BoundedSums

/-!
# The Weierstrass product inequality

Packet: `analysis/stirling_ipra`, `stirling_ipra.tex`, Section "A finite proof that `log e = 1`", the step
before `eq:EB`: "For `u_i ∈ [0, 1]`, finite induction proves `1 − ∑_i u_i ≤ ∏_i (1 − u_i) ≤ 1`", which is
applied to `u_i = i/m` to compare the binomial sums `B_m` with the exponential sums `E_m`.

With a common denominator `D`, `u_i = a_i/D` and `1 − u_i = c_i/D`, i.e. `a_i + c_i = D` for `i < N`
(a bounded hypothesis on the bodies `a(i, x)`, `c(i, x)`):

* `weierstrass_lower`: `D^{N+1} ≤ D^N ∑_{i<N} a_i + D ∏_{i<N} c_i`, i.e.
  `1 − ∑ u_i ≤ ∏ (1 − u_i)` multiplied by `D^{N+1}`;
* `weierstrass_upper`: `∏_{i<N} c_i ≤ D^N`, i.e. `∏ (1 − u_i) ≤ 1`.

Both are carried by one quantifier-free induction; the steps are the certificates
`c_k · (ih) + D^k S a_k` and `D · (ih) + P a_k`. The comparison `eq:EB` itself, which needs the binomial
sums `B_m`, is not derived here.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.WeierstrassProduct

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- The two inequalities at length `k`. -/
abbrev WInv (a c : PTm 2) (D k x : PTm n) : Fm PTm n :=
  le (pw D (succ k)) (pw D k * ap2 (sumF a) k x + D * ap2 (prodF c) k x) ⋏
    le (ap2 (prodF c) k x) (pw D k)

theorem w_base (a c : PTm 2) (D x : PTm n) : Γ ⊢[PRAAx] WInv a c D zero x := by
  have p₁ := natEq (pw_succ (Γ := Γ) D zero); have p₀ := natEq (pw_zero (Γ := Γ) D)
  have s₀ := natEq (sum_zero (Γ := Γ) a x); have q₀ := natEq (prod_zero (Γ := Γ) c x)
  refine .andI ?_ ?_
  · ipra_le 0 using rw [p₁, p₀, s₀, q₀]; ring
  · ipra_le 0 using rw [p₀, q₀]; ring

theorem w_step {a c : PTm 2} {D k x : PTm n}
    (hk : Γ ⊢[PRAAx] inst2 a k x + inst2 c k x ≐ D) (ih : Γ ⊢[PRAAx] WInv a c D k x) :
    Γ ⊢[PRAAx] WInv a c D (succ k) x := by
  have e := natEq hk
  have ps := natEq (pw_succ (Γ := Γ) D (succ k)); have ps₁ := natEq (pw_succ (Γ := Γ) D k)
  have es := natEq (sum_succ' (Γ := Γ) a k x)
  have ep' : Γ ⊢[PRAAx] ap2 (prodF c) (succ k) x ≐ ap2 (prodF c) k x * inst2 c k x := prod_succ c k x
  have ep := natEq ep'
  have ihL := Prf.andE₁ ih
  have ihU := Prf.andE₂ ih
  refine .andI ?_ ?_
  · ipra_le 𝔟 (inst2 c k x) * sl ihL + 𝔟 (pw D k) * 𝔟 (ap2 (sumF a) k x) * 𝔟 (inst2 a k x) using
      rw [ps, ps₁, es, ep]
      linear_combination (𝔟 (pw D k) * 𝔟 D - 𝔟 (pw D k) * 𝔟 (ap2 (sumF a) k x)) * e
  · ipra_le 𝔟 D * sl ihU + 𝔟 (ap2 (prodF c) k x) * 𝔟 (inst2 a k x) using
      rw [ps₁, ep]
      linear_combination (-𝔟 (ap2 (prodF c) k x)) * e

/-- One guarded step of the induction. -/
theorem w_guard {a c : PTm 2} {D k x N : PTm n} (hkN : Γ ⊢[PRAAx] le (succ k) N)
    (hk : Γ ⊢[PRAAx] inst2 a k x + inst2 c k x ≐ D)
    (ih : Γ ⊢[PRAAx] le k N ⟶ WInv a c D k x) : Γ ⊢[PRAAx] WInv a c D (succ k) x :=
  w_step hk (Prf.impE ih (le_trans (le_succ_self k) hkN))

section Main

variable {a c : PTm 2} {D x N : PTm n}

theorem w_all
    (hb : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      (inst2 a (var 0) (Syn.shift x) + inst2 c (var 0) (Syn.shift x) ≐ Syn.shift D))) :
    Γ ⊢[PRAAx] Fm.all (le (var 0) (Syn.shift N) ⟶ WInv a c (Syn.shift D) (var 0) (Syn.shift x)) := by
  refine PRA.qfInd _ ⟨le_QF _ _, le_QF _ _, le_QF _ _⟩ ?_ ?_
  · simp only [Fm.subst_imp, Fm.subst_and, subst_le, subst_ap2, PTm.subst_add, PTm.subst_mul, Syn.subst_var,
      Syn.inst_zero, Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact .impI (w_base a c D x)
  · simp only [Fm.subst_imp, Fm.subst_and, subst_le, subst_ap2, PTm.subst_add, PTm.subst_mul, Syn.subst_var,
      Syn.repl_zero, subst_repl_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact .impI (w_guard Prf.hyp0 (Prf.impE hb.allOpen.wk.wk Prf.hyp0) Prf.hyp1)

theorem w_at
    (hb : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      (inst2 a (var 0) (Syn.shift x) + inst2 c (var 0) (Syn.shift x) ≐ Syn.shift D))) :
    Γ ⊢[PRAAx] WInv a c D N x := by
  have h := Prf.allE N (w_all hb)
  simp only [Fm.subst_imp, Fm.subst_and, subst_le, subst_ap2, PTm.subst_add, PTm.subst_mul, Syn.subst_var,
    Syn.inst_zero, Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ] at h
  exact .impE h (le_refl N)

/-- `1 − ∑ u_i ≤ ∏ (1 − u_i)`, cleared: `D^{N+1} ≤ D^N ∑_{i<N} a_i + D ∏_{i<N} c_i`. -/
theorem weierstrass_lower
    (hb : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      (inst2 a (var 0) (Syn.shift x) + inst2 c (var 0) (Syn.shift x) ≐ Syn.shift D))) :
    Γ ⊢[PRAAx] le (pw D (succ N)) (pw D N * ap2 (sumF a) N x + D * ap2 (prodF c) N x) :=
  Prf.andE₁ (w_at hb)

/-- `∏ (1 − u_i) ≤ 1`, cleared: `∏_{i<N} c_i ≤ D^N`. -/
theorem weierstrass_upper
    (hb : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      (inst2 a (var 0) (Syn.shift x) + inst2 c (var 0) (Syn.shift x) ≐ Syn.shift D))) :
    Γ ⊢[PRAAx] le (ap2 (prodF c) N x) (pw D N) :=
  Prf.andE₂ (w_at hb)

end Main

end LeanProofs.IPRA.Analysis.WeierstrassProduct
