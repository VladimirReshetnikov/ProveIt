import IPRADerivations.Combinatorics.BinomialTheorem
import IPRADerivations.Probability.Independence

/-!
# The binomial law

Packet: `probability/central_limit_ipra_2026-11-15` (Section "The de Moivre–Laplace theorems":
the Bernoulli moments (10.1) and the mean of `Bin(n, p)` used to centre the statements). The law
`Bin(n, p)` with `p = a/(a + 1)` has the weights `w_k = C(n, k) a^k`, of total `(a + 1)^n`
(`Combinatorics/BinomialTheorem`).

* `absorption`: `(k + 1) C(m + 1, k + 1) = (m + 1) C(m, k)` for `k ≤ m`;
* `binomial_mean`: `∑_{k ≤ m+1} k C(m + 1, k) a^k = (m + 1) a (a + 1)^m`; dividing by the total
  `(a + 1)^(m+1)` gives `E B_n = n p`;
* `binomial_second`: `∑_{k ≤ m+2} k² C(m + 2, k) a^k = (m + 2) a ((m + 2) a + 1) (a + 1)^m`;
* `binomial_variance`: with `W` the total weight and `n = m + 2`,
  `W ∑ k² w_k = (∑ k w_k)² + n a (a + 1)^(2n−2)`, i.e. `Var B_n = n p q`;
* `bernoulli_variance`: `b a² + a b² = a b (a + b)`: a Bernoulli variable with weights `b`, `a`
  on `0`, `1` and `N = a + b` has `∑ w abs(N X − a)² = a b N`, i.e. `σ² = p q`;
* `bernoulli_third`: `b a³ + a b³ = a b (a² + b²)`, i.e. `ρ₃ = p q (p² + q²)`.

The independence identities of `lem:finite-algebra` are `Probability/Independence`. The
Berry–Esseen bounds and the local theorems are not formalized.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Probability.BinomialLaw

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Combinatorics.Binomial
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (binom_eq mul_cancel)
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (tBody inst2_t congrBinom congrPw binomial_at)
open LeanProofs.IPRA.Probability.Independence (sum_scale)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Absorption -/

/-- `(k + 1) C(m + 1, k + 1) = (m + 1) C(m, k)` for `k ≤ m`. -/
theorem absorption {k m : PTm n} (h : Γ ⊢[PRAAx] le k m) :
    Γ ⊢[PRAAx] succ k * binom (succ m) (succ k) ≐ succ m * binom m k := by
  have h' : Γ ⊢[PRAAx] le (succ k) (succ m) := (succ_monus_succ _ _).eqTrans h
  have e₁ := natEq (binom_eq h'); have e₂ := natEq (binom_eq h)
  have f₁ := natEq (fact_succ (Γ := Γ) m zero); have f₂ := natEq (fact_succ (Γ := Γ) k zero)
  have f₃ := natEq (congrAp2 factF (succ_monus_succ (Γ := Γ) m k) (.eqRefl zero))
  refine (mul_cancel (bden_pos m k) ?_).eqSymm
  apply deriveNat; ipra_simps
  linear_combination -(𝔞(m) + 1) * e₂ - f₁ + e₁ +
    𝔞(ap2 factF (monus (succ m) (succ k)) zero) * 𝔞(binom (succ m) (succ k)) * f₂ +
    𝔞(ap2 factF k zero) * (𝔞(k) + 1) * 𝔞(binom (succ m) (succ k)) * f₃

/-! ## The mean -/

/-- `k C(fst x, k) (snd x)^k`. -/
abbrev kBody : PTm 2 := var 0 * tBody

theorem inst2_k (k x : PTm n) : inst2 kBody k x = k * (binom (fstT x) k * pw (sndT x) k) := by
  simp [inst2]

theorem mean_pt {i m a : PTm n} (h : Γ ⊢[PRAAx] le i m) :
    Γ ⊢[PRAAx] inst2 (shiftBody kBody) i (pairT (succ m) a) ≐ (succ m * a) * inst2 tBody i (pairT m a) := by
  rw [inst2_shiftBody, inst2_k, inst2_t]
  have c₁ : Γ ⊢[PRAAx] succ i * (binom (fstT (pairT (succ m) a)) (succ i) * pw (sndT (pairT (succ m) a)) (succ i)) ≐
      succ i * (binom (succ m) (succ i) * pw a (succ i)) :=
    congrMul (.eqRefl _) (congrMul (congrBinom (fst_pair _ _) (.eqRefl _)) (congrPw (snd_pair _ _) (.eqRefl _)))
  have c₂ : Γ ⊢[PRAAx] (succ m * a) * (binom (fstT (pairT m a)) i * pw (sndT (pairT m a)) i) ≐
      (succ m * a) * (binom m i * pw a i) :=
    congrMul (.eqRefl _) (congrMul (congrBinom (fst_pair _ _) (.eqRefl _)) (congrPw (snd_pair _ _) (.eqRefl _)))
  refine c₁.eqTrans (.eqTrans ?_ c₂.eqSymm)
  have ab := natEq (absorption h); have ps := natEq (pw_succ (Γ := Γ) a i)
  apply deriveNat; ipra_simps
  linear_combination 𝔞(pw a (succ i)) * ab + (𝔞(m) + 1) * 𝔞(binom m i) * ps

/-- `∑_{k ≤ m+1} k C(m + 1, k) a^k = (m + 1) a (a + 1)^m`. -/
theorem binomial_mean (m a : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF kBody) (succ (succ m)) (pairT (succ m) a) ≐ (succ m * a) * pw (succ a) m := by
  have s := sum_shift (Γ := Γ) kBody (succ m) (pairT (succ m) a)
  rw [inst2_k] at s
  have sc : Γ ⊢[PRAAx] ap2 (sumF (shiftBody kBody)) (succ m) (pairT (succ m) a) ≐
      (succ m * a) * ap2 (sumF tBody) (succ m) (pairT m a) := by
    refine sum_scale _ _ _ _ _ _ (.allI (.impI ?_))
    simp only [Syn.shift, subst_pairT, PTm.subst_mul, ConciseIPRA.PTm.subst_succ]
    exact mean_pt ((succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0)
  have e₀ := natEq s; have e₁ := natEq sc; have e₂ := natEq (binomial_at (Γ := Γ) m a)
  apply deriveNat; ipra_simps
  linear_combination e₀ + e₁ + (𝔞(m) + 1) * 𝔞(a) * e₂

/-! ## The second moment and the variance -/

/-- `k² C(fst x, k) (snd x)^k`. -/
abbrev qBody : PTm 2 := var 0 * var 0 * tBody

theorem inst2_q (k x : PTm n) : inst2 qBody k x = k * k * (binom (fstT x) k * pw (sndT x) k) := by
  simp [inst2]

theorem second_pt {j m a : PTm n} (h : Γ ⊢[PRAAx] le j (succ m)) :
    Γ ⊢[PRAAx] inst2 (shiftBody qBody) j (pairT (succ (succ m)) a) ≐
      (succ (succ m) * a) * inst2 (addBody kBody tBody) j (pairT (succ m) a) := by
  rw [inst2_shiftBody, inst2_q, inst2_addBody, inst2_k, inst2_t]
  have cb₁ : Γ ⊢[PRAAx] binom (fstT (pairT (succ (succ m)) a)) (succ j) * pw (sndT (pairT (succ (succ m)) a)) (succ j) ≐
      binom (succ (succ m)) (succ j) * pw a (succ j) :=
    congrMul (congrBinom (fst_pair _ _) (.eqRefl _)) (congrPw (snd_pair _ _) (.eqRefl _))
  have cb₂ : Γ ⊢[PRAAx] binom (fstT (pairT (succ m) a)) j * pw (sndT (pairT (succ m) a)) j ≐
      binom (succ m) j * pw a j :=
    congrMul (congrBinom (fst_pair _ _) (.eqRefl _)) (congrPw (snd_pair _ _) (.eqRefl _))
  refine (congrMul (.eqRefl _) cb₁).eqTrans (.eqTrans ?_
    (congrMul (.eqRefl _) (congrAdd (congrMul (.eqRefl _) cb₂) cb₂)).eqSymm)
  have ab := natEq (absorption h); have ps := natEq (pw_succ (Γ := Γ) a j)
  apply deriveNat; ipra_simps
  linear_combination (𝔞(j) + 1) * 𝔞(pw a (succ j)) * ab +
    (𝔞(j) + 1) * (𝔞(m) + 1 + 1) * 𝔞(binom (succ m) j) * ps

/-- `∑_{k ≤ m+2} k² C(m + 2, k) a^k = (m + 2) a ((m + 2) a + 1) (a + 1)^m`. -/
theorem binomial_second (m a : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF qBody) (succ (succ (succ m))) (pairT (succ (succ m)) a) ≐
      (succ (succ m) * a) * (succ (succ m) * a + one) * pw (succ a) m := by
  have s := sum_shift (Γ := Γ) qBody (succ (succ m)) (pairT (succ (succ m)) a)
  rw [inst2_q] at s
  have sc : Γ ⊢[PRAAx] ap2 (sumF (shiftBody qBody)) (succ (succ m)) (pairT (succ (succ m)) a) ≐
      (succ (succ m) * a) * ap2 (sumF (addBody kBody tBody)) (succ (succ m)) (pairT (succ m) a) := by
    refine sum_scale _ _ _ _ _ _ (.allI (.impI ?_))
    simp only [Syn.shift, subst_pairT, PTm.subst_mul, ConciseIPRA.PTm.subst_succ]
    exact second_pt ((succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0)
  have e₀ := natEq s; have e₁ := natEq sc
  have e₂ := natEq (sum_add (Γ := Γ) kBody tBody (succ (succ m)) (pairT (succ m) a))
  have e₃ := natEq (binomial_mean (Γ := Γ) m a); have e₄ := natEq (binomial_at (Γ := Γ) (succ m) a)
  have e₅ := natEq (pw_succ (Γ := Γ) (succ a) m)
  apply deriveNat; ipra_simps
  linear_combination e₀ + e₁ + (𝔞(m) + 1 + 1) * 𝔞(a) * (e₂ + e₃ + e₄ + e₅)

/-- The variance of `Bin(n, p)`, `n = m + 2`, cleared of the total `W = (a + 1)^n`:
`W ∑ k² w_k = (∑ k w_k)² + n a (a + 1)^(2n−2)`, i.e. `Var B_n = n a/(a + 1)² = n p q`. -/
theorem binomial_variance (m a : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF tBody) (succ (succ (succ m))) (pairT (succ (succ m)) a) *
        ap2 (sumF qBody) (succ (succ (succ m))) (pairT (succ (succ m)) a) ≐
      ap2 (sumF kBody) (succ (succ (succ m))) (pairT (succ (succ m)) a) *
        ap2 (sumF kBody) (succ (succ (succ m))) (pairT (succ (succ m)) a) +
      succ (succ m) * a * (pw (succ a) (succ m) * pw (succ a) (succ m)) := by
  have eW := natEq (binomial_at (Γ := Γ) (succ (succ m)) a)
  have eQ := natEq (binomial_second (Γ := Γ) m a)
  have eS := natEq (binomial_mean (Γ := Γ) (succ m) a)
  have p₁ := natEq (pw_succ (Γ := Γ) (succ a) m)
  have p₂ := natEq (pw_succ (Γ := Γ) (succ a) (succ m))
  apply deriveNat; ipra_simps
  rw [eW, eQ, eS, p₂, p₁]
  ring

/-! ## Bernoulli moments -/

/-- `σ² = p q`, cleared: `b a² + a b² = a b (a + b)`. -/
theorem bernoulli_variance (a b : PTm n) :
    Γ ⊢[PRAAx] b * (a * a) + a * (b * b) ≐ a * b * (a + b) := by
  apply deriveNat; ipra_simps; ring

/-- `ρ₃ = p q (p² + q²)`, cleared: `b a³ + a b³ = a b (a² + b²)`. -/
theorem bernoulli_third (a b : PTm n) :
    Γ ⊢[PRAAx] b * (a * a * a) + a * (b * b * b) ≐ a * b * (a * a + b * b) := by
  apply deriveNat; ipra_simps; ring

end LeanProofs.IPRA.Probability.BinomialLaw
