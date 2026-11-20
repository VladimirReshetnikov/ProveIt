import IPRADerivations.Combinatorics.LucasIdentities
import IPRADerivations.Core.SumLemmas

/-!
# The alternating sum of Fibonacci numbers

Packet: `combinatorics/fibonacci_lucas_ipra`, `FibonacciLucasIPRA.tex`, Theorem "Finite sums", the second
identity of (14): `∑_{k=0}^n (−1)^k F_k = (−1)^n F_{n−1} − 1` for `n ≥ 1`.

Signs are carried by the parity bit, with subtracted terms on the other side: for `n = N + 1`,

  `∑_{k≤N+1} [k even] F_k + [N even] F_N + 1 = ∑_{k≤N+1} [k odd] F_k + [N odd] F_N`

(`alt_sum_fib`). It is the first identity of (14), `LucasIdentities.alt_sum`, after the shift `k = j + 1`
(`Core/SumLemmas.sum_shift` with `F_0 = 0`): the odd part of the `F_k` sum is the even part of the
`F_{j+1}` sum and conversely (`shift_odd`, `shift_even`, from `par (j + 1) = 1 ∸ par j`).
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Combinatorics.FibonacciAltSum

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Combinatorics.Fibonacci
open LeanProofs.IPRA.Combinatorics.LucasIdentities (evfB odfB alt_sum)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

set_option hygiene false in
local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk Γ t)

/-- `[k even] F_k`. -/
abbrev evkB : PTm 2 := monus one (par (var 0)) * fib (var 0)
/-- `[k odd] F_k`. -/
abbrev odkB : PTm 2 := par (var 0) * fib (var 0)

theorem one_monus_one_monus_par (x : PTm n) : Γ ⊢[PRAAx] monus one (monus one (par x)) ≐ par x := by
  refine .orE (par_cases x) ?_ ?_
  · have h : ((par x ≐ zero) :: Γ) ⊢[PRAAx] par x ≐ zero := Prf.hyp0
    exact ((congrMonus (.eqRefl one) ((congrMonus (.eqRefl one) h).eqTrans (monus_zero one))).eqTrans
      (monus_self one)).eqTrans h.eqSymm
  · have h : ((par x ≐ one) :: Γ) ⊢[PRAAx] par x ≐ one := Prf.hyp0
    exact ((congrMonus (.eqRefl one) ((congrMonus (.eqRefl one) h).eqTrans (monus_self one))).eqTrans
      (monus_zero one)).eqTrans h.eqSymm

/-- The shifted odd body is the even body of the `F_{j+1}` sum. -/
theorem shift_odd_at {m : ℕ} {Δ : List (Fm PTm m)} (i x : PTm m) :
    Δ ⊢[PRAAx] inst2 (shiftBody odkB) i x ≐ inst2 evfB i x := by
  have e1 : inst2 odkB (succ i) x = par (succ i) * fib (succ i) := by simp [inst2]
  rw [inst2_shiftBody, e1, LucasIdentities.inst2_evf]
  exact congrMul (par_succ i) (fib_succ i)

/-- The shifted even body is the odd body of the `F_{j+1}` sum. -/
theorem shift_even_at {m : ℕ} {Δ : List (Fm PTm m)} (i x : PTm m) :
    Δ ⊢[PRAAx] inst2 (shiftBody evkB) i x ≐ inst2 odfB i x := by
  have e1 : inst2 evkB (succ i) x = monus one (par (succ i)) * fib (succ i) := by simp [inst2]
  rw [inst2_shiftBody, e1, LucasIdentities.inst2_odf]
  exact congrMul ((congrMonus (.eqRefl one) (par_succ i)).eqTrans (one_monus_one_monus_par i)) (fib_succ i)

theorem shift_odd (M : PTm n) : Γ ⊢[PRAAx] ap2 (sumF (shiftBody odkB)) M zero ≐ ap2 (sumF evfB) M zero :=
  sum_congr_bounded _ _ _ _ _ (.allI (.impI (shift_odd_at _ _)))

theorem shift_even (M : PTm n) : Γ ⊢[PRAAx] ap2 (sumF (shiftBody evkB)) M zero ≐ ap2 (sumF odfB) M zero :=
  sum_congr_bounded _ _ _ _ _ (.allI (.impI (shift_even_at _ _)))

/-- (14), second identity, for `n = N + 1`:
`∑_{k≤N+1} [k even] F_k + [N even] F_N + 1 = ∑_{k≤N+1} [k odd] F_k + [N odd] F_N`. -/
theorem alt_sum_fib (N : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF evkB) (succ (succ N)) zero + monus one (par N) * fib N + one ≐
      ap2 (sumF odkB) (succ (succ N)) zero + par N * fib N := by
  have a := natEq (alt_sum (Γ := Γ) N)
  have s1 := natEq (sum_shift (Γ := Γ) odkB (succ N) zero)
  have s2 := natEq (sum_shift (Γ := Γ) evkB (succ N) zero)
  have c1 := natEq (shift_odd (Γ := Γ) (succ N))
  have c2 := natEq (shift_even (Γ := Γ) (succ N))
  have z1 := natEq (fib_zero (Γ := Γ) (n := n))
  have i1 : inst2 odkB zero (zero : PTm n) = par zero * fib zero := by simp [inst2]
  have i2 : inst2 evkB zero (zero : PTm n) = monus one (par zero) * fib zero := by simp [inst2]
  rw [i1] at s1
  rw [i2] at s2
  apply deriveNat; ipra_simps
  linear_combination s2 - s1 + c2 - c1 - a + (𝔟 (monus one (par zero)) - 𝔟 (par zero)) * z1

end LeanProofs.IPRA.Combinatorics.FibonacciAltSum
