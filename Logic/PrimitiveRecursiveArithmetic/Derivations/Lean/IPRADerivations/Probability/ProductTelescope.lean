import IPRADerivations.Analysis.RationalArithmetic.Powers.PowerSums
import IPRADerivations.Core.OrderCertificates

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

The proof is the induction of the paper (`pinv_step`): the successor step multiplies by the new factor and
uses `a_k + (b_k ∸ a_k) = b_k + (a_k ∸ b_k)`. The telescoping sum of `eq:product-telescope` itself is not
formed.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Probability.ProductTelescope

open_ipra

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

/-- `|a − b| = (a ∸ b) + (b ∸ a)` for bodies. -/
abbrev sdB (a b : PTm 2) : PTm 2 := monus a b + monus b a

theorem inst2_sd (a b : PTm 2) (i x : PTm n) :
    inst2 (sdB a b) i x = monus (inst2 a i x) (inst2 b i x) + monus (inst2 b i x) (inst2 a i x) := by
  simp [inst2]

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
  have ih1 := Prf.andE₁ ih; have ih2 := Prf.andE₂ ih
  have ea := natEq (prod_succ' (Γ := Γ) a k x); have eb := natEq (prod_succ' (Γ := Γ) b k x)
  have es := natEq (sum_succ' (Γ := Γ) (sdB a b) k x)
  have ep := natEq (pw_succ (Γ := Γ) M k)
  have mx := natEq (monus_max (Γ := Γ) (inst2 a k x) (inst2 b k x))
  rw [inst2_sd] at es
  refine .andI ?_ ?_
  · ipra_le sl ih1 * 𝔞 M + 𝔞 (ap2 (prodF b) k x) * sl hb using rw [eb, ep]; ring
  · ipra_le sl ih2 * 𝔞 (inst2 a k x) + 𝔞 (pw M k) * 𝔞 (ap2 (sumF (sdB a b)) k x) * sl ha +
        𝔞 M * 𝔞 (ap2 (prodF b) k x) * 𝔞 (monus (inst2 b k x) (inst2 a k x)) +
        𝔞 (pw M k) * 𝔞 M * 𝔞 (monus (inst2 b k x) (inst2 a k x)) +
        𝔞 M * 𝔞 (monus (inst2 a k x) (inst2 b k x)) * sl ih1 using
      rw [ea, eb, es, ep]
      linear_combination (𝔞 M * 𝔞 (ap2 (prodF b) k x)) * mx

/-- `lem:product-telescope`: if `a(j, x), b(j, x) ≤ M` for `j < N`, then `∏_{j<N} b ≤ M^N` and
`M ∏_{j<N} a ≤ M ∏_{j<N} b + M^N ∑_{j<N} |a − b|`. -/
theorem prod_telescope (a b : PTm 2) (x N M : PTm n)
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      (le (inst2 a (var 0) (Syn.shift x)) (Syn.shift M) ⋏ le (inst2 b (var 0) (Syn.shift x)) (Syn.shift M)))) :
    Γ ⊢[PRAAx] PInv a b N x M := by
  have hall : Γ ⊢[PRAAx] Fm.all (le (var 0) (Syn.shift N) ⟶ PInv a b (var 0) (Syn.shift x) (Syn.shift M)) := by
    ipra_qfind (⟨le_QF _ _, le_QF _ _, le_QF _ _⟩) [subst_le, subst_ap2]
    · exact .impI (pinv_base a b x M)
    · have hf := h.allOpen
      refine .impI ?_
      have hle : (le (succ (var 0)) (Syn.shift N) ::
          (le (var 0) (Syn.shift N) ⟶ PInv a b (var 0) (Syn.shift x) (Syn.shift M)) ::
          Γ.map Fm.shift) ⊢[PRAAx] le (var 0) (Syn.shift N) :=
        le_trans (le_succ_self _) Prf.hyp0
      have ih := Prf.impE Prf.hyp1 hle
      have hp := Prf.impE hf.wk.wk (Prf.hyp0 : (le (succ (var 0)) (Syn.shift N) ::
          (le (var 0) (Syn.shift N) ⟶ PInv a b (var 0) (Syn.shift x) (Syn.shift M)) ::
          Γ.map Fm.shift) ⊢[PRAAx] _)
      exact pinv_step a b (Prf.andE₁ hp) (Prf.andE₂ hp) ih
  have h2 := Prf.allE N hall
  simp only [Fm.subst_imp, Fm.subst_and, subst_le, subst_ap2, PTm.subst_add, PTm.subst_mul, Syn.subst_var,
    Syn.inst_zero, Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero] at h2
  exact .impE h2 (le_refl N)

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
