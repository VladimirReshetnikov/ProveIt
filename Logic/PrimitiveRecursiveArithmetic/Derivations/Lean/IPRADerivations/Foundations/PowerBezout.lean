import IPRADerivations.Combinatorics.CatalanPowers

/-!
# Bézout witnesses for two coprime powers

Packet: `foundations/ipra_resources_and_elimination_2026-11-15`, proof of `thm:elim-bezout`
("Finite arithmetic Bézout bound"): "For completeness, coprimeness of these powers has explicit
finite witnesses. If `a ≠ b`, put `L = (U − a)/(b − a)`, `M = −(U − b)/(b − a)`, `L + M = 1`.
Expand `1 = (L + M)^{r+s−1}`. A term whose exponent of `L` is at least `r` is divisible by
`(U − a)^r`; every other term has exponent of `M` at least `s` and is divisible by `(U − b)^s`.
Grouping the terms gives polynomial Bézout coefficients for the two powers."

Cleared of the denominator `b − a`, with `x = U − a`, `y = b − U`, `x + y = b − a`, and
`r = r' + 1`, `s = s' + 1`, `n = r + s − 1 = r' + s' + 1`:

* `power_bezout`: `(x + y)^n = y^s · Q + x^r · P`, where
  `Q = Σ_{k<r} C(n, k) x^k y^{r−1−k}` (the terms with exponent of `x` below `r`) and
  `P = Σ_{j<s} C(n, r + j) x^j y^{s−1−j}` (the terms with exponent of `x` at least `r`).

So `(b − a)^{r+s−1}` is an explicit combination of `(U − a)^r` and `(b − U)^s`. The statement is
for natural numbers `x, y`; it is the two-variable binomial theorem
(`Combinatorics/BinomialTwo.binomial_two`) split at `k = r` (`Core/SumSplit.sum_split`), with the
common power factored out of each part.

* `gbody`, `g_at`: the summand `C(n, a + k) x^k y^{c−k}`;
* `q_point`, `p_point`: one term of each part.

Not derived: the product over several points and the degree comparison of `thm:elim-bezout`.
-/

namespace LeanProofs.IPRA.Foundations.PowerBezout

open_ipra exports
open LeanProofs.IPRA.Combinatorics.Vandermonde (gb congrGb)
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (congrPw)
open LeanProofs.IPRA.Combinatorics.BinomialTwo (bt bt_at binomial_two)
open LeanProofs.IPRA.Combinatorics.CatalanPowers (shift_pair shift_succ shift_zero)
open LeanProofs.IPRA.Combinatorics.BellTouchardPower (le_of_lt_succ)
open LeanProofs.IPRA.Probability.Independence (sum_scale)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem shift_add (a b : PTm n) : Syn.shift (a + b) = Syn.shift a + Syn.shift b := by
  simp [Syn.shift]

theorem shift_pw (a m : PTm n) : Syn.shift (pw a m) = pw (Syn.shift a) (Syn.shift m) := by
  simp [Syn.shift]

/-- `C(n, a + k) x^k y^{c−k}`, over `0 = k`, `1 = ⟨n, ⟨x, ⟨y, ⟨a, c⟩⟩⟩⟩`. -/
abbrev gbody : PTm 2 :=
  gb (fstT (var 1)) (fstT (sndT (sndT (sndT (var 1)))) + var 0) *
      pw (fstT (sndT (var 1))) (var 0) *
    pw (fstT (sndT (sndT (var 1)))) (monus (sndT (sndT (sndT (sndT (var 1))))) (var 0))

theorem g_at (k M X Y a c : PTm n) :
    Γ ⊢[PRAAx] inst2 gbody k (pairT M (pairT X (pairT Y (pairT a c)))) ≐
      gb M (a + k) * pw X k * pw Y (monus c k) := by
  have h : inst2 gbody k (pairT M (pairT X (pairT Y (pairT a c)))) =
      gb (fstT (pairT M (pairT X (pairT Y (pairT a c)))))
          (fstT (sndT (sndT (sndT (pairT M (pairT X (pairT Y (pairT a c))))))) + k) *
        pw (fstT (sndT (pairT M (pairT X (pairT Y (pairT a c)))))) k *
        pw (fstT (sndT (sndT (pairT M (pairT X (pairT Y (pairT a c)))))))
          (monus (sndT (sndT (sndT (sndT (pairT M (pairT X (pairT Y (pairT a c)))))))) k) := by
    simp [inst2]
  rw [h]
  have pM : Γ ⊢[PRAAx] fstT (pairT M (pairT X (pairT Y (pairT a c)))) ≐ M := fst_pair _ _
  have s₁ : Γ ⊢[PRAAx] sndT (pairT M (pairT X (pairT Y (pairT a c)))) ≐
      pairT X (pairT Y (pairT a c)) := snd_pair _ _
  have pX := (congrFst s₁).eqTrans (fst_pair _ _)
  have s₂ := (congrSnd s₁).eqTrans (snd_pair _ _)
  have pY := (congrFst s₂).eqTrans (fst_pair _ _)
  have s₃ := (congrSnd s₂).eqTrans (snd_pair _ _)
  have pa := (congrFst s₃).eqTrans (fst_pair _ _)
  have pc := (congrSnd s₃).eqTrans (snd_pair _ _)
  exact congrMul (congrMul (congrGb pM (congrAdd pa (.eqRefl _))) (congrPw pX (.eqRefl _)))
    (congrPw pY (congrMonus pc (.eqRefl _)))

/-- A term with exponent of `x` below `r = r' + 1`: `y^s` factors out. -/
theorem q_point {k r' s' X Y : PTm n} (hk : Γ ⊢[PRAAx] le k r') :
    Γ ⊢[PRAAx] gb (r' + succ s') k * pw X k * pw Y (monus (r' + succ s') k) ≐
      pw Y (succ s') * (gb (r' + succ s') (zero + k) * pw X k * pw Y (monus r' k)) := by
  have m₁ : Γ ⊢[PRAAx] monus (r' + succ s') k ≐ succ s' + monus r' k := by
    refine (congrMonus (b := (succ s' + monus r' k) + k) ?_ (.eqRefl _)).eqTrans (add_monus _ _)
    ipra_lc natEq (eq_add_of_le hk)
  have pwE := (congrPw (.eqRefl Y) m₁).eqTrans (pw_add Y (succ s') (monus r' k))
  have gE : Γ ⊢[PRAAx] gb (r' + succ s') k ≐ gb (r' + succ s') (zero + k) :=
    congrGb (.eqRefl _) (zero_add k).eqSymm
  refine (congrMul (congrMul gE (.eqRefl _)) pwE).eqTrans ?_
  ipra_ring

/-- A term with exponent of `x` at least `r = r' + 1`: `x^r` factors out. -/
theorem p_point {j r' s' X Y : PTm n} (hj : Γ ⊢[PRAAx] le j s') :
    Γ ⊢[PRAAx] gb (r' + succ s') (succ r' + j) * pw X (succ r' + j) *
        pw Y (monus (r' + succ s') (succ r' + j)) ≐
      pw X (succ r') * (gb (r' + succ s') (succ r' + j) * pw X j * pw Y (monus s' j)) := by
  have m₂ : Γ ⊢[PRAAx] monus (r' + succ s') (succ r' + j) ≐ monus s' j := by
    refine (congrMonus (b := monus s' j + (succ r' + j)) ?_ (.eqRefl _)).eqTrans (add_monus _ _)
    ipra_lc natEq (eq_add_of_le hj)
  have xE := pw_add (Γ := Γ) X (succ r') j
  refine (congrMul (congrMul (.eqRefl _) xE) (congrPw (.eqRefl Y) m₂)).eqTrans ?_
  ipra_ring

/-- Bézout witnesses for `x^r` and `y^s`: `(x + y)^{r+s−1} = y^s Q + x^r P`. -/
theorem power_bezout (r' s' X Y : PTm n) :
    Γ ⊢[PRAAx] pw (X + Y) (r' + succ s') ≐
      pw Y (succ s') * ap2 (sumF gbody) (succ r')
          (pairT (r' + succ s') (pairT X (pairT Y (pairT zero r')))) +
        pw X (succ r') * ap2 (sumF gbody) (succ s')
          (pairT (r' + succ s') (pairT X (pairT Y (pairT (succ r') s')))) := by
  have hM : Γ ⊢[PRAAx] succ (r' + succ s') ≐ succ r' + succ s' := by
    ipra_ring
  have B := (binomial_two (Γ := Γ) (r' + succ s') X Y).eqSymm
  have E₀ : Γ ⊢[PRAAx] ap2 (sumF bt) (succ (r' + succ s')) (pairT (r' + succ s') (pairT X Y)) ≐
      ap2 (sumF bt) (succ r' + succ s') (pairT (r' + succ s') (pairT X Y)) :=
    congrAp2 _ hM (.eqRefl _)
  have E₁ := sum_split (Γ := Γ) bt (succ r') (succ s') (pairT (r' + succ s') (pairT X Y))
  have part₁ : Γ ⊢[PRAAx] ap2 (sumF bt) (succ r') (pairT (r' + succ s') (pairT X Y)) ≐
      pw Y (succ s') * ap2 (sumF gbody) (succ r')
        (pairT (r' + succ s') (pairT X (pairT Y (pairT zero r')))) := by
    refine sum_scale _ _ _ _ _ _ (.allI (.impI ?_))
    simp only [shift_pair, shift_succ, shift_zero, shift_add, shift_pw]
    exact (bt_at _ _ _ _).eqTrans ((q_point (le_of_lt_succ Prf.hyp0)).eqTrans
      (congrMul (.eqRefl _) (g_at _ _ _ _ _ _).eqSymm))
  have part₂ : Γ ⊢[PRAAx] ap2 (sumF (offB bt)) (succ s')
        (pairT (succ r') (pairT (r' + succ s') (pairT X Y))) ≐
      pw X (succ r') * ap2 (sumF gbody) (succ s')
        (pairT (r' + succ s') (pairT X (pairT Y (pairT (succ r') s')))) := by
    refine sum_scale _ _ _ _ _ _ (.allI (.impI ?_))
    simp only [shift_pair, shift_succ, shift_add, shift_pw]
    rw [inst2_offB]
    exact (congrInst2 bt (congrAdd (fst_pair _ _) (.eqRefl _)) (snd_pair _ _)).eqTrans
      ((bt_at _ _ _ _).eqTrans ((p_point (le_of_lt_succ Prf.hyp0)).eqTrans
        (congrMul (.eqRefl _) (g_at _ _ _ _ _ _).eqSymm)))
  exact B.eqTrans (E₀.eqTrans (E₁.eqTrans (congrAdd part₁ part₂)))

end LeanProofs.IPRA.Foundations.PowerBezout
