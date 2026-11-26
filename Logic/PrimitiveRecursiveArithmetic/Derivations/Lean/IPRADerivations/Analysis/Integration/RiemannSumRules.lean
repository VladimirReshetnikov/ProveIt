import IPRADerivations.Core.SumSplit
import IPRADerivations.Core.OrderCertificates
import IPRADerivations.Analysis.RationalArithmetic.PowerSums
import IPRADerivations.Probability.Independence

/-!
# The rules of the integral at the level of Riemann sums

Packet: `analysis/calculus_ipra`, Proposition `prop:integralrules`: the constructed integral is additive in
adjacent rational intervals, linear over the rationals, satisfies `|∫_u^v f| ≤ M |v − u|`, is nonnegative
for `f ≥ 0`, and `|f − g| ≤ C` gives `|∫ f − ∫ g| ≤ C |v − u|`.

The integral of the packet is named by its Riemann sums, and each rule is inherited from the corresponding
rule for the finite sums `∑_{i<N} f(i, x)` of sample numerators over a common denominator (the mesh and the
denominators are the same on both sides of every statement, so they are omitted):

* `rs_additive`: `∑_{i<M+K} f = ∑_{i<M} f + ∑_{i<K} f(M + i)` (adjacent intervals);
* `rs_add`, `rs_scale`: the sum of `f + g` is the sum of the sums, and `∑ c g = c ∑ g` (linearity);
* `rs_bound`: `f_i ≤ M` for `i < N` gives `∑_{i<N} f_i ≤ N M` (the bound `M |v − u|`);
* `rs_close`: `f_i ≤ g_i + e_i` for `i < N` gives `∑ f ≤ ∑ g + ∑ e`;
* `rs_close_const`: `f_i ≤ g_i + e_i` and `e_i ≤ C` give `∑ f ≤ ∑ g + N C` (the comparison rule; the
  other direction is the same statement with `f` and `g` exchanged).

Nonnegativity is automatic for natural numerators. The passage from the sums to the regular name of the
integral is `Analysis/RiemannRefinement`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.RiemannSumRules

open_ipra
open LeanProofs.IPRA.Analysis.PowerSums (sum_le)
open LeanProofs.IPRA.Probability.Independence (sum_scale)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- Additivity over adjacent intervals. -/
theorem rs_additive (f : PTm 2) (M K x : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF f) (M + K) x ≐ ap2 (sumF f) M x + ap2 (sumF (offB f)) K (pairT M x) :=
  sum_split f M K x

/-- Additivity in the integrand. -/
theorem rs_add (f g : PTm 2) (N x : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (addBody f g)) N x ≐ ap2 (sumF f) N x + ap2 (sumF g) N x :=
  sum_add f g N x

/-- Homogeneity: `h_i = c g_i` for `i < N` gives `∑ h = c ∑ g`. -/
theorem rs_scale (h g : PTm 2) (N c x : PTm n)
    (hp : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      (inst2 h (var 0) (Syn.shift x) ≐ Syn.shift c * inst2 g (var 0) (Syn.shift x)))) :
    Γ ⊢[PRAAx] ap2 (sumF h) N x ≐ c * ap2 (sumF g) N x :=
  sum_scale h g N c x x hp

/-! ## The bound `M |v − u|` -/

theorem bound_step {f : PTm 2} {k x M : PTm n} (hk : Γ ⊢[PRAAx] le (inst2 f k x) M)
    (ih : Γ ⊢[PRAAx] le (ap2 (sumF f) k x) (k * M)) :
    Γ ⊢[PRAAx] le (ap2 (sumF f) (succ k) x) (succ k * M) := by
  have es := natEq (sum_succ' (Γ := Γ) f k x)
  ipra_le sl ih + sl hk using rw [es]; ring

theorem bound_guard {f : PTm 2} {k x M N : PTm n} (hkN : Γ ⊢[PRAAx] le (succ k) N)
    (hk : Γ ⊢[PRAAx] le (inst2 f k x) M)
    (ih : Γ ⊢[PRAAx] le k N ⟶ le (ap2 (sumF f) k x) (k * M)) :
    Γ ⊢[PRAAx] le (ap2 (sumF f) (succ k) x) (succ k * M) :=
  bound_step hk (Prf.impE ih (le_trans (le_succ_self k) hkN))

/-- `f_i ≤ M` for `i < N` gives `∑_{i<N} f_i ≤ N M`. -/
theorem rs_bound {f : PTm 2} {N x M : PTm n}
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶ le (inst2 f (var 0) (Syn.shift x)) (Syn.shift M))) :
    Γ ⊢[PRAAx] le (ap2 (sumF f) N x) (N * M) := by
  have hall : Γ ⊢[PRAAx] Fm.all (le (var 0) (Syn.shift N) ⟶
      le (ap2 (sumF f) (var 0) (Syn.shift x)) (var 0 * Syn.shift M)) := by
    ipra_qfind (⟨le_QF _ _, le_QF _ _⟩) [subst_le, subst_ap2]
    · refine .impI ?_
      have z := natEq (sum_zero (Γ := le zero N :: Γ) f x)
      ipra_le 0 using rw [z]; ring
    · exact .impI (bound_guard Prf.hyp0 (Prf.impE h.allOpen.wk.wk Prf.hyp0) Prf.hyp1)
  have a := Prf.allE N hall
  simp only [Fm.subst_imp, subst_le, subst_ap2, PTm.subst_mul, Syn.subst_var, Syn.inst_zero,
    Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ] at a
  exact .impE a (le_refl N)

/-! ## Comparison of integrands -/

/-- `f_i ≤ g_i + e_i` for `i < N` gives `∑ f ≤ ∑ g + ∑ e`. -/
theorem rs_close {f g e : PTm 2} {N x : PTm n}
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      le (inst2 f (var 0) (Syn.shift x)) (inst2 g (var 0) (Syn.shift x) + inst2 e (var 0) (Syn.shift x)))) :
    Γ ⊢[PRAAx] le (ap2 (sumF f) N x) (ap2 (sumF g) N x + ap2 (sumF e) N x) := by
  have hs := sum_le f (addBody g e) x N (.allI (.impI (by
    rw [inst2_addBody]
    exact Prf.impE h.allOpen.wk Prf.hyp0)))
  exact le_congr (.eqRefl _) (sum_add g e N x) hs

/-- The comparison rule: `f_i ≤ g_i + e_i` and `e_i ≤ C` for `i < N` give `∑ f ≤ ∑ g + N C`. -/
theorem rs_close_const {f g e : PTm 2} {N x C : PTm n}
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      le (inst2 f (var 0) (Syn.shift x)) (inst2 g (var 0) (Syn.shift x) + inst2 e (var 0) (Syn.shift x))))
    (he : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶ le (inst2 e (var 0) (Syn.shift x)) (Syn.shift C))) :
    Γ ⊢[PRAAx] le (ap2 (sumF f) N x) (ap2 (sumF g) N x + N * C) := by
  have h₁ := rs_close h
  have h₂ := rs_bound he
  ipra_le sl h₁ + sl h₂

end LeanProofs.IPRA.Analysis.RiemannSumRules
