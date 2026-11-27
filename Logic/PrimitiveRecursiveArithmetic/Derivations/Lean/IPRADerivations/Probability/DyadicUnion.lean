import IPRADerivations.AnalyticNumberTheory.PowerCleared

/-!
# The dyadic union bound

Packet: `probability/expected_value_ipra_2026-11-16`, `paper/sections/08_samples_lln.tex`, proof of `thm:dyadic-slln`:
"The union bound over `r ≥ K` up to the last block is at most the infinite geometric majorant
`Σ_{r≥K} σ²/(2ε² 2^r) = σ²/(ε² 2^K)` … Formally, for a fixed finite `H`, only a finite geometric sum is used, and it is
bounded … through an elementary induction."

For a body `P(j, x)` (the probability of the bad block `K + j`, cleared) and constants `c, B`:

* `union_step`, `dyadic_union`: if `2 c 2^{K+j} P_j ≤ B` for every `j < J`, then
  `c 2^K 2^J Σ_{j<J} P_j + B ≤ 2^J B`, i.e. `c 2^K Σ_{j<J} P_j ≤ B (1 − 2^{−J}) < B`.

With `c = e² W²` (`ε = e/f`, values scaled by `f`) and `B = V T` (`V = W Q − S²`, `T` the total mass) this is the
packet's `P(∃ n ∈ [2^K, H] : |X̄_n − μ| ≥ 2ε) ≤ σ²/(ε² 2^K)`, stronger than the stated constant `4`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Probability.DyadicUnion

open_ipra

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- The invariant `c 2^K 2^J Σ_{j<J} P_j + B ≤ 2^J B`. -/
abbrev UF (P : PTm 2) (c K B J x : PTm n) : Fm PTm n :=
  le (c * pw two K * pw two J * ap2 (sumF P) J x + B) (pw two J * B)

theorem union_base (P : PTm 2) (c K B x : PTm n) : Γ ⊢[PRAAx] UF P c K B zero x := by
  refine le_of_eq_add (d := zero) ?_
  ipra_lc 𝔞 B * natEq (pw_zero (Γ := Γ) (two : PTm n)) -
    𝔞 c * 𝔞 (pw two K) * 𝔞 (pw two zero) * natEq (sum_zero (Γ := Γ) P x)

theorem union_step {P : PTm 2} {c K B J x : PTm n}
    (hJ : Γ ⊢[PRAAx] le (two * c * pw two (K + J) * inst2 P J x) B) (ih : Γ ⊢[PRAAx] UF P c K B J x) :
    Γ ⊢[PRAAx] UF P c K B (succ J) x := by
  refine le_of_eq_add (d := two * monus (pw two J * B) (c * pw two K * pw two J * ap2 (sumF P) J x + B) +
    monus B (two * c * pw two (K + J) * inst2 P J x)) ?_
  ipra_lc 2 * natEq (eq_add_of_le ih) + natEq (eq_add_of_le hJ) +
    (𝔞 B - 𝔞 c * 𝔞 (pw two K) * 𝔞 (ap2 (sumF P) J x) - 𝔞 c * 𝔞 (pw two K) * 𝔞 (inst2 P J x)) * natEq (pw_succ (Γ := Γ) two J) -
    𝔞 c * 𝔞 (pw two (succ J)) * 𝔞 (pw two K) * natEq (sum_succ' (Γ := Γ) P J x) +
    2 * 𝔞 c * 𝔞 (inst2 P J x) * natEq (pw_add (Γ := Γ) two K J)

/-- The dyadic union bound: `2 c 2^{K+j} P_j ≤ B` for `j < J` gives `c 2^K 2^J Σ_{j<J} P_j + B ≤ 2^J B`. -/
theorem dyadic_union {P : PTm 2} {c K B x J : PTm n}
    (hb : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift J) ⟶
      le (two * Syn.shift c * pw two (Syn.shift K + var 0) * inst2 P (var 0) (Syn.shift x)) (Syn.shift B))) :
    Γ ⊢[PRAAx] UF P c K B J x := by
  let invariant := UF P (Syn.shift c) (Syn.shift K) (Syn.shift B) (var 0) (Syn.shift x)
  suffices result : Γ ⊢[PRAAx] invariant.subst (Syn.inst J) by simpa [invariant] using result
  refine qfIndUpTo J (le_QF _ _) ?_ ?_
  · simpa [invariant] using union_base (Γ := Γ) P c K B x
  · simp [invariant]
    exact .impI (union_step (.impE hb.allOpen.wk.wk Prf.hyp0) Prf.hyp1)

end LeanProofs.IPRA.Probability.DyadicUnion
