import IPRADerivations.DiophantineNumberTheory.FLTMultiples
import IPRADerivations.Core.OrderCertificates
import IPRADerivations.Core.SumOrder

/-!
# An integer root bound

Packet: `diophantine-number-theory/siegel_ipra`, `paper/03_runge.tex`, Lemma `lem:runge-root-bound`
("An integer root bound"): "If `r ≥ 1` and `G(x) = 0` for an integer `x`, then `|x| ≤ ∑_{i<r} |g_i|` …
put `t = |x| ≥ 1` and `L = ∑_{i<r} |g_i|`. Since the nonzero integer `g_r` has `|g_r| ≥ 1`, the equation
`g_r x^r = −∑_{i<r} g_i x^i` gives `t^r ≤ |g_r| t^r ≤ ∑_{i<r} |g_i| t^i ≤ L t^{r−1}`. Cancellation of the
positive integer `t^{r−1}` gives `t ≤ L`. … the comparison `t^i ≤ t^{r−1}` is proved by induction on the
exponent."

The coefficients' absolute values are a body `a(i, x)` and `t = fst x ≥ 1`; `r = r′ + 1`:

* `pw_exp_mono`: `1 ≤ t`, `e ≤ f` give `t^e ≤ t^f`;
* `tB a`: the body `a(i, x) t^i`; `weighted_le`: `∑_{i<J} a_i t^i ≤ t^{r′} ∑_{i<J} a_i` for `J ≤ r′ + 1`;
* `integer_root_bound`: from `1 ≤ t`, `1 ≤ g` and `g t^{r′+1} ≤ ∑_{i ≤ r′} a_i t^i` (the triangle
  inequality applied to the equation), `t ≤ ∑_{i ≤ r′} a_i`.

The triangle inequality from the signed equation and the case `x = 0` are not repeated here
(`DiophantineNumberTheory/RungeProduct` has the integer absolute value and its triangle inequality).
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.IntegerRootBound

open_ipra exports

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `t ≥ 1` gives `t = (t ∸ 1) + 1`. -/
theorem pos_of_one_le {t : PTm n} (h : Γ ⊢[PRAAx] le one t) : Γ ⊢[PRAAx] t ≐ succ (monus t one) := by
  ipra_lc natEq (eq_add_of_le h)

/-- `t^m ≥ 1` for `t ≥ 1`. -/
theorem pw_pos_of {t : PTm n} (h : Γ ⊢[PRAAx] le one t) (m : PTm n) :
    Γ ⊢[PRAAx] pw t m ≐ succ (pred (pw (succ (monus t one)) m)) :=
  (congrAp2 powF (.eqRefl m) (pos_of_one_le h)).eqTrans (pw_pos (monus t one) m)

/-- `1 ≤ t` and `e ≤ f` give `t^e ≤ t^f`. -/
theorem pw_exp_mono {t e f : PTm n} (ht : Γ ⊢[PRAAx] le one t) (h : Γ ⊢[PRAAx] le e f) :
    Γ ⊢[PRAAx] le (pw t e) (pw t f) :=
  pw_le_pw_exp ht h

section Sums

variable (a : PTm 2)

/-- `a(i, x) · (fst x)^i`. -/
def tB : PTm 2 := a * pw (fstT (var 1)) (var 0)

theorem inst2_tB (i x : PTm n) : inst2 (tB a) i x = inst2 a i x * pw (fstT x) i := by
  simp [inst2, tB]

/-- The invariant at the length `J`. -/
abbrev WInv (r' J x : PTm n) : Fm PTm n :=
  le (ap2 (sumF (tB a)) J x) (pw (fstT x) r' * ap2 (sumF a) J x)

theorem w_step {r' J x : PTm n} (ht : Γ ⊢[PRAAx] le one (fstT x)) (hJ : Γ ⊢[PRAAx] le J r')
    (ih : Γ ⊢[PRAAx] WInv a r' J x) : Γ ⊢[PRAAx] WInv a r' (succ J) x := by
  have s₁ := sum_succ' (Γ := Γ) (tB a) J x
  rw [inst2_tB] at s₁
  have e₁ := natEq s₁
  have e₂ := natEq (sum_succ' (Γ := Γ) a J x)
  have m := pw_exp_mono ht hJ
  ipra_le sl ih + 𝔟(inst2 a J x) * sl m using
    linear_combination 𝔟(pw (fstT x) r') * e₂ - e₁

theorem w_guard {r' J x : PTm n} (ht : Γ ⊢[PRAAx] le one (fstT x)) (hJ : Γ ⊢[PRAAx] le (succ J) (succ r'))
    (ih : Γ ⊢[PRAAx] le J (succ r') ⟶ WInv a r' J x) : Γ ⊢[PRAAx] WInv a r' (succ J) x :=
  w_step a ht ((succ_monus_succ J r').eqSymm.eqTrans hJ) (Prf.impE ih (le_trans (le_succ_self J) hJ))

/-- `∑_{i<J} a_i t^i ≤ t^{r′} ∑_{i<J} a_i` for `J ≤ r′ + 1`. -/
theorem weighted_le {r' x : PTm n} (ht : Γ ⊢[PRAAx] le one (fstT x)) :
    Γ ⊢[PRAAx] WInv a r' (succ r') x := by
  have shifted : Γ.map Fm.shift ⊢[PRAAx] le one (fstT (Syn.shift x)) := by
    simpa [Fm.shift, Syn.shift] using ht.shift
  refine le_congr (one_mul _) ((congrAdd (.eqRefl _) (zero_mul _)).eqTrans (add_zero _))
    (sum_scaled_le_weighted_pair (tB a) a a one (pw (fstT x) r') zero x x x (succ r') (.allI (.impI ?_)))
  simp only [Syn.shift, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero, subst_ap2, subst_fstT]
  rw [inst2_tB]
  have exponent : (lt (var 0) (succ (Syn.shift r')) :: Γ.map Fm.shift) ⊢[PRAAx]
      le (pw (fstT (Syn.shift x)) (var 0)) (pw (fstT (Syn.shift x)) (Syn.shift r')) :=
    pw_exp_mono shifted.wk (Order.le_of_lt_succ Prf.hyp0)
  exact le_congr (one_mul _).eqSymm
    ((mul_comm _ _).eqTrans ((congrAdd (.eqRefl _) (zero_mul _)).eqTrans (add_zero _)).eqSymm)
    (mul_le_mul_left _ exponent)

/-- `lem:runge-root-bound`: `t ≤ ∑_{i ≤ r′} |g_i|` for a nonzero integer root of absolute value `t`. -/
theorem integer_root_bound {r' g x : PTm n} (ht : Γ ⊢[PRAAx] le one (fstT x)) (hg : Γ ⊢[PRAAx] le one g)
    (h : Γ ⊢[PRAAx] le (g * pw (fstT x) (succ r')) (ap2 (sumF (tB a)) (succ r') x)) :
    Γ ⊢[PRAAx] le (fstT x) (ap2 (sumF a) (succ r') x) := by
  have w := weighted_le a (r' := r') ht
  have ps := natEq (pw_succ (Γ := Γ) (fstT x) r')
  have pp := natEq (pw_pos_of ht r')
  have key : Γ ⊢[PRAAx] le (succ (pred (pw (succ (monus (fstT x) one)) r')) * fstT x)
      (succ (pred (pw (succ (monus (fstT x) one)) r')) * ap2 (sumF a) (succ r') x) := by
    ipra_le sl h + sl w + sl hg * 𝔟(pw (fstT x) r') * 𝔟(fstT x) using
      linear_combination (𝔟(fstT x) - 𝔟(ap2 (sumF a) (succ r') x)) * pp + (𝔟 g) * ps
  exact mul_le_cancel key

end Sums

end LeanProofs.IPRA.DiophantineNumberTheory.IntegerRootBound
