import IPRADerivations.Probability.TruncationEstimate
import IPRADerivations.Geometry.HypercubeSplit
import IPRADerivations.Core.ProdLemmas

/-!
# Effective dominated convergence: the modulus composition

Packet: `probability/expected_value_ipra_2026-11-16`, `paper/sections/12_convergence.tex`, Theorem `thm:dct`
("Effective dominated convergence"): with `|X_n|, |X| ≤ G`, "an integrability-tail modulus for `G`, and a
convergence-in-probability modulus: given `p, q`, a primitive-recursive `N(p, q)` makes `n ≥ N(p, q) ⟹
P(|X_n − X| > 2^{−p}) ≤ 2^{−q}`", "`X_n → X` in `L¹` with a computable modulus". The proof applies
`lem:truncation` and chooses the three parameters so that each term is small.

The observables of the sequence are bodies over `(i, ⟨n, x⟩)`, values scaled by a natural `s` (so a body value `v`
means `v/s`), and the cleared expectation of a body `Z` at the index `n` is `Σ_{i<M} w_i Z_i` at the parameter
`⟨n, x⟩`. With `d_n = |X_n − X|`, the dominating `G` and indicators `e₁` (of `d_n > η`) and `e₂` (of `G > K`):

* `dct_at`: if `4·2^r η ≤ s`, `4·2^r · 2K · Σ w e₁ ≤ s Σ w` and `4·2^r Σ w G e₂ ≤ s Σ w`, then
  `2^r Σ w d_n ≤ s Σ w`, i.e. `E|X_n − X| ≤ 2^{−r}`: the threshold, the probability rate and the tail each
  contribute at most a quarter (the tail twice);
* `dct_modulus`: the same uniformly in `n ≥ N`: the convergence-in-probability modulus (at the level `η`, rate
  `s/(4·2^r·2K)`) and the tail modulus (at the level `K`) supply `N`, and `E|X_n − X| ≤ 2^{−r}` for every
  `n ≥ N` — an explicit `L¹` modulus.

Choosing `η`, `K` and `N` from given primitive-recursive moduli is a metalevel composition; the theorem is uniform
in all of them.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Probability.DominatedConvergence

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Probability.TruncationEstimate (TInv truncation)
open LeanProofs.IPRA.Geometry.HypercubeSplit (le_cancel_pos)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

section Modulus

variable (w d G e₁ e₂ : PTm 2)

theorem four_pos : Γ ⊢[PRAAx] (two * two : PTm n) ≐ succ (pred (two * two)) :=
  pos_mul' (congrSucc (pred_succ _).eqSymm) (congrSucc (pred_succ _).eqSymm)

/-- The arithmetic of the three quarters. -/
theorem quarters {SD W η K P T s r : PTm n}
    (t : Γ ⊢[PRAAx] le SD (η * W + two * K * P + two * T))
    (hη : Γ ⊢[PRAAx] le (two * two * pw two r * η) s)
    (hP : Γ ⊢[PRAAx] le (two * two * pw two r * (two * K) * P) (s * W))
    (hT : Γ ⊢[PRAAx] le (two * two * pw two r * T) (s * W)) :
    Γ ⊢[PRAAx] le (pw two r * SD) (s * W) := by
  refine le_cancel_pos four_pos ?_
  ipra_le 4 * 𝔟 (pw two r) * sl t + 𝔟 W * sl hη + sl hP + 2 * sl hT

/-- `E|X_n − X| ≤ 2^{−r}` at one index: `2^r Σ w d ≤ s Σ w`, the sums over `i < M` at the parameter `y`. -/
theorem dct_at {η K s r M y : PTm n}
    (hd : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift M) ⟶
      le (inst2 d (var 0) (Syn.shift y)) (two * inst2 G (var 0) (Syn.shift y))))
    (h₁ : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift M) ⟶
      (lt (Syn.shift η) (inst2 d (var 0) (Syn.shift y)) ⟶ (inst2 e₁ (var 0) (Syn.shift y) ≐ one))))
    (h₂ : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift M) ⟶
      (lt (Syn.shift K) (inst2 G (var 0) (Syn.shift y)) ⟶ (inst2 e₂ (var 0) (Syn.shift y) ≐ one))))
    (hη : Γ ⊢[PRAAx] le (two * two * pw two r * η) s)
    (hP : Γ ⊢[PRAAx] le (two * two * pw two r * (two * K) * ap2 (sumF (w * e₁)) M y) (s * ap2 (sumF w) M y))
    (hT : Γ ⊢[PRAAx] le (two * two * pw two r * ap2 (sumF (w * (G * e₂))) M y) (s * ap2 (sumF w) M y)) :
    Γ ⊢[PRAAx] le (pw two r * ap2 (sumF (w * d)) M y) (s * ap2 (sumF w) M y) :=
  quarters (truncation w d G e₁ e₂ hd h₁ h₂) hη hP hT

/-- `thm:dct`, the `L¹` modulus: if the domination and the indicator properties hold at every index `n`, the
tail bound holds at every `n`, and the probability bound holds for `n ≥ N`, then `2^r Σ w d_n ≤ s Σ w` for every
`n ≥ N`. The bodies read the index from `⟨n, x⟩`. -/
theorem dct_modulus {η K s r M N x : PTm n}
    (hd : Γ ⊢[PRAAx] Fm.all (Fm.all (lt (var 0) (Syn.shift (Syn.shift M)) ⟶
      le (inst2 d (var 0) (pairT (var 1) (Syn.shift (Syn.shift x))))
        (two * inst2 G (var 0) (pairT (var 1) (Syn.shift (Syn.shift x)))))))
    (h₁ : Γ ⊢[PRAAx] Fm.all (Fm.all (lt (var 0) (Syn.shift (Syn.shift M)) ⟶
      (lt (Syn.shift (Syn.shift η)) (inst2 d (var 0) (pairT (var 1) (Syn.shift (Syn.shift x)))) ⟶
        (inst2 e₁ (var 0) (pairT (var 1) (Syn.shift (Syn.shift x))) ≐ one)))))
    (h₂ : Γ ⊢[PRAAx] Fm.all (Fm.all (lt (var 0) (Syn.shift (Syn.shift M)) ⟶
      (lt (Syn.shift (Syn.shift K)) (inst2 G (var 0) (pairT (var 1) (Syn.shift (Syn.shift x)))) ⟶
        (inst2 e₂ (var 0) (pairT (var 1) (Syn.shift (Syn.shift x))) ≐ one)))))
    (hη : Γ ⊢[PRAAx] le (two * two * pw two r * η) s)
    (hP : Γ ⊢[PRAAx] Fm.all (le (Syn.shift N) (var 0) ⟶
      le (two * two * pw two (Syn.shift r) * (two * Syn.shift K) *
          ap2 (sumF (w * e₁)) (Syn.shift M) (pairT (var 0) (Syn.shift x)))
        (Syn.shift s * ap2 (sumF w) (Syn.shift M) (pairT (var 0) (Syn.shift x)))))
    (hT : Γ ⊢[PRAAx] Fm.all (le (two * two * pw two (Syn.shift r) *
          ap2 (sumF (w * (G * e₂))) (Syn.shift M) (pairT (var 0) (Syn.shift x)))
        (Syn.shift s * ap2 (sumF w) (Syn.shift M) (pairT (var 0) (Syn.shift x))))) :
    Γ ⊢[PRAAx] Fm.all (le (Syn.shift N) (var 0) ⟶
      le (pw two (Syn.shift r) * ap2 (sumF (w * d)) (Syn.shift M) (pairT (var 0) (Syn.shift x)))
        (Syn.shift s * ap2 (sumF w) (Syn.shift M) (pairT (var 0) (Syn.shift x)))) := by
  refine .allI (.impI ?_)
  let C : List (Fm PTm (n + 1)) := le (Syn.shift N) (var 0) :: Γ.map Fm.shift
  have e : Syn.shift (pairT (var 0) (Syn.shift x) : PTm (n + 1)) = pairT (var 1) (Syn.shift (Syn.shift x)) := by
    simp [Syn.shift]
  have hd' : C ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift (Syn.shift M)) ⟶
      le (inst2 d (var 0) (Syn.shift (pairT (var 0) (Syn.shift x))))
        (two * inst2 G (var 0) (Syn.shift (pairT (var 0) (Syn.shift x))))) := by
    rw [e]; exact hd.allOpen.wk
  have h₁' : C ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift (Syn.shift M)) ⟶
      (lt (Syn.shift (Syn.shift η)) (inst2 d (var 0) (Syn.shift (pairT (var 0) (Syn.shift x)))) ⟶
        (inst2 e₁ (var 0) (Syn.shift (pairT (var 0) (Syn.shift x))) ≐ one))) := by
    rw [e]; exact h₁.allOpen.wk
  have h₂' : C ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift (Syn.shift M)) ⟶
      (lt (Syn.shift (Syn.shift K)) (inst2 G (var 0) (Syn.shift (pairT (var 0) (Syn.shift x)))) ⟶
        (inst2 e₂ (var 0) (Syn.shift (pairT (var 0) (Syn.shift x))) ≐ one))) := by
    rw [e]; exact h₂.allOpen.wk
  have hη' : C ⊢[PRAAx] le (two * two * pw two (Syn.shift r) * Syn.shift η) (Syn.shift s) := by
    simpa [Fm.shift, Syn.shift] using hη.shift.wk
  exact dct_at w d G e₁ e₂ hd' h₁' h₂' hη' (Prf.impE hP.allOpen.wk Prf.hyp0) hT.allOpen.wk

end Modulus

end LeanProofs.IPRA.Probability.DominatedConvergence
