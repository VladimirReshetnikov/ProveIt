import IPRADerivations.Probability.PoissonShift
import IPRADerivations.Combinatorics.BinomialIdentities

/-!
# The Pascal recurrence of the binomial distribution function

Packet: `analysis/beta_function_ipra_2026-11-16`, Theorem `thm:binomial-cdf` ("Binomial CDF identity"),
`F_{n,k}(p) = I_{1−p}(n − k, k + 1) = 1 − I_p(k + 1, n − k)`, the alternative proof: "induction on `n`
using Pascal's identity stays entirely in polynomial arithmetic".

With `F_{n,k}(p) = ∑_{j ≤ k} C(n, j) p^j (1 − p)^{n−j}`, the inductive step in `n` is

`F_{n+1,k}(p) = F_{n,k}(p) − C(n, k) p^{k+1} (1 − p)^{n−k}`,

which matches the shift `I_p(k + 1, n − k + 1) = I_p(k + 1, n − k) + C(n, k) p^{k+1} (1 − p)^{n−k}` of the
regularized function in its second argument. For `p = a/(a + b)`, on the scales `(a + b)^n` and
`(a + b)^{n+1}`, with `n = fst x`, `a = fst (snd x)`, `b = snd (snd x)`:

* `cdB`, `cdB'`: the terms `C(n, j) a^j b^{n−j}` and `C(n + 1, j) a^j b^{n+1−j}`;
* `cdf_base`, `cdf_step`: the recurrence at `k = 0` and its step in `k`;
* `cdf_pascal`: for `k ≤ n`,
  `(a + b) ∑_{j ≤ k} C(n, j) a^j b^{n−j} = ∑_{j ≤ k} C(n + 1, j) a^j b^{n+1−j} + C(n, k) a^{k+1} b^{n−k}`.

The identification with the regularized incomplete Beta function (the integral) is not derived.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.BinomialCdf

open_ipra
open LeanProofs.IPRA.Combinatorics.Binomial
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (pascal_at binom_zero')
open LeanProofs.IPRA.Probability.PoissonShift (monus_pred)
open LeanProofs.IPRA.Foundations.ContractProducts (shift_fstT shift_sndT)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `C(n, j) a^j b^{n−j}`; variables `0 = j`, `1 = x = ⟨n, ⟨a, b⟩⟩`. -/
def cdB : PTm 2 :=
  binom (fstT (var 1)) (var 0) * pw (fstT (sndT (var 1))) (var 0) *
    pw (sndT (sndT (var 1))) (monus (fstT (var 1)) (var 0))

/-- `C(n + 1, j) a^j b^{n+1−j}` with the same parameter. -/
def cdB' : PTm 2 :=
  binom (succ (fstT (var 1))) (var 0) * pw (fstT (sndT (var 1))) (var 0) *
    pw (sndT (sndT (var 1))) (monus (succ (fstT (var 1))) (var 0))

theorem inst2_cdB (j x : PTm n) :
    inst2 cdB j x = binom (fstT x) j * pw (fstT (sndT x)) j * pw (sndT (sndT x)) (monus (fstT x) j) := by
  simp [inst2, cdB]

theorem inst2_cdB' (j x : PTm n) :
    inst2 cdB' j x = binom (succ (fstT x)) j * pw (fstT (sndT x)) j *
      pw (sndT (sndT x)) (monus (succ (fstT x)) j) := by
  simp [inst2, cdB']

/-- The claim at `k`. -/
abbrev CInv (k x : PTm n) : Fm PTm n :=
  (fstT (sndT x) + sndT (sndT x)) * ap2 (sumF cdB) (succ k) x ≐
    ap2 (sumF cdB') (succ k) x +
      binom (fstT x) k * pw (fstT (sndT x)) (succ k) * pw (sndT (sndT x)) (monus (fstT x) k)

theorem cdf_base (x : PTm n) : Γ ⊢[PRAAx] CInv zero x := by
  have s₁ := sum_succ' (Γ := Γ) cdB zero x
  rw [inst2_cdB] at s₁
  have s₂ := sum_succ' (Γ := Γ) cdB' zero x
  rw [inst2_cdB'] at s₂
  have e₁ := natEq s₁; have e₂ := natEq s₂
  have z := natEq (sum_zero (Γ := Γ) cdB x); have z' := natEq (sum_zero (Γ := Γ) cdB' x)
  have a₁ := natEq (pw_succ (Γ := Γ) (fstT (sndT x)) zero)
  have x₂ := natEq ((congrAp2 powF (monus_zero (Γ := Γ) (succ (fstT x))) (.eqRefl (sndT (sndT x)))).eqTrans
    ((pw_succ (sndT (sndT x)) (fstT x)).eqTrans
      (congrMul (congrAp2 powF (monus_zero (Γ := Γ) (fstT x)) (.eqRefl (sndT (sndT x)))).eqSymm
        (.eqRefl (sndT (sndT x))))))
  apply deriveNat; ipra_simps
  linear_combination (𝔟(fstT (sndT x)) + 𝔟(sndT (sndT x))) * e₁ +
    (𝔟(fstT (sndT x)) + 𝔟(sndT (sndT x))) * z - e₂ - z' -
    𝔟(binom (fstT x) zero) * 𝔟(pw (sndT (sndT x)) (monus (fstT x) zero)) * a₁ -
    𝔟(binom (succ (fstT x)) zero) * 𝔟(pw (fstT (sndT x)) zero) * x₂ +
    𝔟(sndT (sndT x)) * 𝔟(pw (fstT (sndT x)) zero) * 𝔟(pw (sndT (sndT x)) (monus (fstT x) zero)) *
      (natEq (binom_zero' (Γ := Γ) (fstT x)) - natEq (binom_zero' (Γ := Γ) (succ (fstT x))))

theorem cdf_step {k x : PTm n} (hk : Γ ⊢[PRAAx] lt k (fstT x)) (ih : Γ ⊢[PRAAx] CInv k x) :
    Γ ⊢[PRAAx] CInv (succ k) x := by
  have s₁ := sum_succ' (Γ := Γ) cdB (succ k) x
  rw [inst2_cdB] at s₁
  have s₂ := sum_succ' (Γ := Γ) cdB' (succ k) x
  rw [inst2_cdB'] at s₂
  ipra_lc (𝔟(fstT (sndT x)) + 𝔟(sndT (sndT x))) * natEq s₁ + natEq ih - natEq s₂ -
    𝔟(binom (fstT x) (succ k)) * 𝔟(pw (sndT (sndT x)) (monus (fstT x) (succ k))) * natEq (pw_succ (Γ := Γ) (fstT (sndT x)) (succ k)) -
    𝔟(pw (fstT (sndT x)) (succ k)) * 𝔟(pw (sndT (sndT x)) (monus (fstT x) k)) * natEq (pascal_at hk) -
    𝔟(binom (succ (fstT x)) (succ k)) * 𝔟(pw (fstT (sndT x)) (succ k)) * natEq (congrAp2 powF (succ_monus_succ (Γ := Γ) (fstT x) k) (.eqRefl (sndT (sndT x)))) -
    𝔟(binom (fstT x) (succ k)) * 𝔟(pw (fstT (sndT x)) (succ k)) * natEq ((congrAp2 powF (monus_pred hk) (.eqRefl (sndT (sndT x)))).eqTrans (pw_succ (Γ := Γ) (sndT (sndT x)) (monus (fstT x) (succ k))))

theorem cdf_guard {k x : PTm n} (hk : Γ ⊢[PRAAx] le (succ k) (fstT x))
    (ih : Γ ⊢[PRAAx] le k (fstT x) ⟶ CInv k x) : Γ ⊢[PRAAx] CInv (succ k) x :=
  cdf_step hk (Prf.impE ih (le_trans (le_succ_self k) hk))

theorem cdf_all (x : PTm n) :
    Γ ⊢[PRAAx] Fm.all (le (var 0) (Syn.shift (fstT x)) ⟶ CInv (var 0) (Syn.shift x)) := by
  refine PRA.qfInd _ ⟨le_QF _ _, trivial⟩ ?_ ?_
  · have e : (le (var 0) (Syn.shift (fstT x)) ⟶ CInv (var 0) (Syn.shift x)).subst (Syn.inst zero) =
        (le zero (fstT x) ⟶ CInv zero x) := by
      simp
    rw [e]
    exact .impI (cdf_base x)
  · have e : (le (var 0) (Syn.shift (fstT x)) ⟶ CInv (var 0) (Syn.shift x)).subst
          (Syn.repl (succ (var 0))) =
        (le (succ (var 0)) (Syn.shift (fstT x)) ⟶ CInv (succ (var 0)) (Syn.shift x)) := by
      simp
    rw [e, shift_fstT]
    exact .impI (cdf_guard Prf.hyp0 Prf.hyp1)

/-- `thm:binomial-cdf`, the Pascal step of the proof by induction on `n`: for `k ≤ n`,
`(a + b) F_{n,k} = F_{n+1,k} + C(n, k) a^{k+1} b^{n−k}` on the integer scale. -/
theorem cdf_pascal {k x : PTm n} (hk : Γ ⊢[PRAAx] le k (fstT x)) : Γ ⊢[PRAAx] CInv k x := by
  have a := Prf.allE k (cdf_all (Γ := Γ) x)
  have e : (le (var 0) (Syn.shift (fstT x)) ⟶ CInv (var 0) (Syn.shift x)).subst (Syn.inst k) =
      (le k (fstT x) ⟶ CInv k x) := by
    simp
  rw [e] at a
  exact Prf.impE a hk

end LeanProofs.IPRA.Analysis.BinomialCdf
