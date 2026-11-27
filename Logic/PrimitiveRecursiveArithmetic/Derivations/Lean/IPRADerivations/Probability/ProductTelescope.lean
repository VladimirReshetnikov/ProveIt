import IPRADerivations.Analysis.RationalArithmetic.Powers.PowerSums
import IPRADerivations.Core.OrderCertificates
import IPRADerivations.Probability.ProductReplacement

/-!
# Product telescoping

Packet: `probability/normal_distribution_ipra_2026-11-16`, Appendix `app:finite-lemmas`,
Lemma `lem:product-telescope` (`eq:product-telescope`): for lists `a_j`, `b_j` (`j < n`) with
`|a_j|, |b_j| ≤ M`, `|∏ a_j − ∏ b_j| ≤ M^{n−1} ∑_j |a_j − b_j|`. The packet uses it to propagate interval
errors through exponentiation, likelihood products and characteristic-function products.

For bodies `a(j, x)`, `b(j, x)` with natural values and `|a − b| = (a ∸ b) + (b ∸ a)` (`sdB`), the bound is
stated without the exponent `n − 1`: if `a(j, x), b(j, x) ≤ M` for `j < N`, then

* `prod_telescope`: `M ∏_{j<N} a ≤ M ∏_{j<N} b + M^N ∑_{j<N} |a − b|`, together with `∏_{j<N} b ≤ M^N`;
* `prod_telescope_abs`: the same with `a` and `b` exchanged, so that
  `M |∏ a − ∏ b| ≤ M^N ∑ |a − b|`.

The product estimate uses the one-sided replacement theorem, with `|a_k − b_k|` as the pointwise error.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Probability.ProductTelescope

open_ipra

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- `|a − b| = (a ∸ b) + (b ∸ a)` for bodies. -/
abbrev sdB (a b : PTm 2) : PTm 2 := monus a b + monus b a

theorem inst2_sd (a b : PTm 2) (i x : PTm n) :
    inst2 (sdB a b) i x = monus (inst2 a i x) (inst2 b i x) + monus (inst2 b i x) (inst2 a i x) := by
  simp [inst2]

private theorem le_add_sd (a b : PTm 2) (k x : PTm n) :
    Γ ⊢[PRAAx] le (inst2 a k x) (inst2 b k x + inst2 (sdB a b) k x) := by
  rw [inst2_sd]
  exact le_trans (Common.le_add_monus _ _)
    (le_congr (.eqRefl _) (add_assoc _ _ _) (le_add_right _ _))

theorem prod_succ' (body : PTm 2) (N x : PTm n) :
    Γ ⊢[PRAAx] ap2 (prodF body) (succ N) x ≐ ap2 (prodF body) N x * inst2 body N x :=
  prod_succ body N x

/-- The invariant: `∏_{j<k} b ≤ M^k` and `M ∏_{j<k} a ≤ M ∏_{j<k} b + M^k ∑_{j<k} |a − b|`. -/
abbrev PInv (a b : PTm 2) (k x M : PTm n) : Fm PTm n :=
  le (ap2 (prodF b) k x) (pw M k) ⋏
    le (M * ap2 (prodF a) k x) (M * ap2 (prodF b) k x + pw M k * ap2 (sumF (sdB a b)) k x)

theorem pinv_base (a b : PTm 2) (x M : PTm n) : Γ ⊢[PRAAx] PInv a b zero x M := by
  have a0 := natEq (prod_zero (Γ := Γ) a x); have b0 := natEq (prod_zero (Γ := Γ) b x)
  have s0 := natEq (sum_zero (Γ := Γ) (sdB a b) x); have p0 := natEq (pw_zero (Γ := Γ) M)
  refine .andI ?_ ?_
  · ipra_le 0 using rw [b0, p0]; ring
  · ipra_le 0 using rw [a0, b0, s0]; ring

theorem pinv_step (a b : PTm 2) {k x M : PTm n} (ha : Γ ⊢[PRAAx] le (inst2 a k x) M)
    (hb : Γ ⊢[PRAAx] le (inst2 b k x) M) (ih : Γ ⊢[PRAAx] PInv a b k x M) :
    Γ ⊢[PRAAx] PInv a b (succ k) x M := by
  have next := ProductReplacement.repl_step ih.andE₁ ih.andE₂ (le_add_sd a b k x) ha hb
  have power := (pw_succ (Γ := Γ) M k).eqSymm
  have product := (prod_succ' (Γ := Γ) b k x).eqSymm
  refine .andI (le_congr product power next.andE₁) ?_
  exact le_congr (congrMul (.eqRefl _) (prod_succ' a k x).eqSymm)
    (congrAdd (congrMul (.eqRefl _) product)
      (congrMul power (sum_succ' (sdB a b) k x).eqSymm)) next.andE₂

/-- `lem:product-telescope`: if `a(j, x), b(j, x) ≤ M` for `j < N`, then `∏_{j<N} b ≤ M^N` and
`M ∏_{j<N} a ≤ M ∏_{j<N} b + M^N ∑_{j<N} |a − b|`. -/
theorem prod_telescope (a b : PTm 2) (x N M : PTm n)
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      (le (inst2 a (var 0) (Syn.shift x)) (Syn.shift M) ⋏ le (inst2 b (var 0) (Syn.shift x)) (Syn.shift M)))) :
    Γ ⊢[PRAAx] PInv a b N x M := by
  refine ProductReplacement.replacement_bound a b (sdB a b) M N x
    (.allI (.impI (le_add_sd a b _ _))) ?_ ?_
  · exact .allI (.impI (.andE₁ (.impE h.allOpen.wk Prf.hyp0)))
  · exact .allI (.impI (.andE₂ (.impE h.allOpen.wk Prf.hyp0)))

/-- `∑ |a − b| = ∑ |b − a|`. -/
theorem sd_comm (a b : PTm 2) (N x : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (sdB b a)) N x ≐ ap2 (sumF (sdB a b)) N x := by
  refine sum_congr_bounded (sdB b a) (sdB a b) x x N (.allI (.impI ?_))
  rw [inst2_sd, inst2_sd]
  exact add_comm _ _

/-- `lem:product-telescope`, both directions: `M |∏ a − ∏ b| ≤ M^N ∑ |a − b|`. -/
theorem prod_telescope_abs (a b : PTm 2) (x N M : PTm n)
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      (le (inst2 a (var 0) (Syn.shift x)) (Syn.shift M) ⋏ le (inst2 b (var 0) (Syn.shift x)) (Syn.shift M)))) :
    Γ ⊢[PRAAx] le (M * ap2 (prodF a) N x) (M * ap2 (prodF b) N x + pw M N * ap2 (sumF (sdB a b)) N x) ⋏
      le (M * ap2 (prodF b) N x) (M * ap2 (prodF a) N x + pw M N * ap2 (sumF (sdB a b)) N x) := by
  have h' : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      (le (inst2 b (var 0) (Syn.shift x)) (Syn.shift M) ⋏ le (inst2 a (var 0) (Syn.shift x)) (Syn.shift M))) :=
    .allI (.impI (.andI (Prf.andE₂ (Prf.impE h.allOpen.wk Prf.hyp0))
      (Prf.andE₁ (Prf.impE h.allOpen.wk Prf.hyp0))))
  have p1 := Prf.andE₂ (prod_telescope a b x N M h)
  have p2 := Prf.andE₂ (prod_telescope b a x N M h')
  exact .andI p1 (le_congr (.eqRefl _)
    (congrAdd (.eqRefl _) (congrMul (.eqRefl _) (sd_comm a b N x))) p2)

end LeanProofs.IPRA.Probability.ProductTelescope
