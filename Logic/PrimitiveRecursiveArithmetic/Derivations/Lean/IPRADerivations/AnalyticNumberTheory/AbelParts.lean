import IPRADerivations.AnalyticNumberTheory.AbsDiff

/-!
# Finite summation by parts with signed increments (`pnt_ipra_constructive_2026-11-14`, `sb:finite-abel`)

Packet: `analytic-number-theory/pnt_ipra_constructive_2026-11-14`, `selberg.tex`, proof of Lemma `sb:weighted-sum`:
"The exact finite summation-by-parts identity is
`Σ_{n=1}^N (a(n) − 2 log n) g_n = Δ_N g_{N+1} + Σ_{n=1}^N Δ_n (g_n − g_{n+1})` (`sb:finite-abel`)." The increments
`g_n − g_{n+1}` have no sign, so in ℕ they are split into `g_n ∸ g_{n+1}` and `g_{n+1} ∸ g_n`. For coefficient and
value bodies `a`, `g` with `A(n) = Σ_{k≤n} a(k)`:

  `Σ_{n≤N} a(n) g(n) + Σ_{n≤N} A(n)(g(n+1) ∸ g(n)) = A(N) g(N+1) + Σ_{n≤N} A(n)(g(n) ∸ g(n+1))`

(`abel_parts`, one closed QF induction; `max_eq`: `b + (c ∸ b) = c + (b ∸ c)`).
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.AbelParts

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `b + (c ∸ b) = c + (b ∸ c)` (both are `max(b, c)`). -/
theorem max_eq (b c : PTm n) : Γ ⊢[PRAAx] b + monus c b ≐ c + monus b c := by
  refine .orE (le_total b c) ?_ ?_
  · have h : (le b c :: Γ) ⊢[PRAAx] le b c := Prf.hyp0
    have e := natEq (eq_add_of_le h); have z := natEq h
    apply deriveNat; ipra_simps; linear_combination -e - z
  · have h : (le c b :: Γ) ⊢[PRAAx] le c b := Prf.hyp0
    have e := natEq (eq_add_of_le h); have z := natEq h
    apply deriveNat; ipra_simps; linear_combination e + z

section Parts

variable (a g : PTm 2)

/-- `a(n) g(n)`. -/
abbrev agB : PTm 2 := a * g
/-- `A(n)(g(n+1) ∸ g(n))`. -/
abbrev upB : PTm 2 := ap2 (sumF a) (succ (var 0)) (var 1) * monus (Syn.subst ![succ (var 0), var 1] g) g
/-- `A(n)(g(n) ∸ g(n+1))`. -/
abbrev dnB : PTm 2 := ap2 (sumF a) (succ (var 0)) (var 1) * monus g (Syn.subst ![succ (var 0), var 1] g)

theorem inst2_g1 (k y : PTm n) : Syn.subst ![k, y] (Syn.subst ![succ (var 0), var 1] g) = inst2 g (succ k) y := by
  simp only [inst2, Syn.subst_subst]; congr 1; funext i; fin_cases i <;> simp

theorem inst2_agB (k y : PTm n) : inst2 (agB a g) k y = inst2 a k y * inst2 g k y := by simp [inst2]

theorem inst2_upB (k y : PTm n) :
    inst2 (upB a g) k y = ap2 (sumF a) (succ k) y * monus (inst2 g (succ k) y) (inst2 g k y) := by
  simp only [upB, inst2, PTm.subst_mul, PTm.subst_monus, subst_ap2, ConciseIPRA.PTm.subst_succ, Syn.subst_var]
  rw [inst2_g1]; simp [inst2]

theorem inst2_dnB (k y : PTm n) :
    inst2 (dnB a g) k y = ap2 (sumF a) (succ k) y * monus (inst2 g k y) (inst2 g (succ k) y) := by
  simp only [dnB, inst2, PTm.subst_mul, PTm.subst_monus, subst_ap2, ConciseIPRA.PTm.subst_succ, Syn.subst_var]
  rw [inst2_g1]; simp [inst2]

/-- The invariant, over `0 = N`, `1 = y`. -/
abbrev partsF : Fm PTm 2 :=
  ap2 (sumF (agB a g)) (succ (var 0)) (var 1) + ap2 (sumF (upB a g)) (succ (var 0)) (var 1) ≐
    ap2 (sumF a) (succ (var 0)) (var 1) * inst2 g (succ (var 0)) (var 1) +
      ap2 (sumF (dnB a g)) (succ (var 0)) (var 1)

theorem parts_step {N y : PTm n} (ih : Γ ⊢[PRAAx]
      ap2 (sumF (agB a g)) (succ N) y + ap2 (sumF (upB a g)) (succ N) y ≐
        ap2 (sumF a) (succ N) y * inst2 g (succ N) y + ap2 (sumF (dnB a g)) (succ N) y) :
    Γ ⊢[PRAAx] ap2 (sumF (agB a g)) (succ (succ N)) y + ap2 (sumF (upB a g)) (succ (succ N)) y ≐
      ap2 (sumF a) (succ (succ N)) y * inst2 g (succ (succ N)) y + ap2 (sumF (dnB a g)) (succ (succ N)) y := by
  have e0 := natEq ih
  have s1 := sum_succ' (Γ := Γ) (agB a g) (succ N) y; rw [inst2_agB] at s1
  have s2 := sum_succ' (Γ := Γ) (upB a g) (succ N) y; rw [inst2_upB] at s2
  have s3 := sum_succ' (Γ := Γ) (dnB a g) (succ N) y; rw [inst2_dnB] at s3
  have s4 := natEq (sum_succ' (Γ := Γ) a (succ N) y)
  have m := natEq (max_eq (Γ := Γ) (inst2 g (succ N) y) (inst2 g (succ (succ N)) y))
  have f1 := natEq s1; have f2 := natEq s2; have f3 := natEq s3
  apply deriveNat; ipra_simps
  linear_combination f1 + f2 - f3 + e0 - 𝔞 (inst2 g (succ N) y) * s4 +
    𝔞 (ap2 (sumF a) (succ (succ N)) y) * m

theorem parts_zero (y : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (agB a g)) (succ zero) y + ap2 (sumF (upB a g)) (succ zero) y ≐
      ap2 (sumF a) (succ zero) y * inst2 g (succ zero) y + ap2 (sumF (dnB a g)) (succ zero) y := by
  have s1 := sum_succ' (Γ := Γ) (agB a g) zero y; rw [inst2_agB] at s1
  have s2 := sum_succ' (Γ := Γ) (upB a g) zero y; rw [inst2_upB] at s2
  have s3 := sum_succ' (Γ := Γ) (dnB a g) zero y; rw [inst2_dnB] at s3
  have s4 := sum_succ' (Γ := Γ) a zero y
  have z1 := natEq (sum_zero (Γ := Γ) (agB a g) y); have z2 := natEq (sum_zero (Γ := Γ) (upB a g) y)
  have z3 := natEq (sum_zero (Γ := Γ) (dnB a g) y); have z4 := natEq (sum_zero (Γ := Γ) a y)
  have m := natEq (max_eq (Γ := Γ) (inst2 g zero y) (inst2 g (succ zero) y))
  have f1 := natEq s1; have f2 := natEq s2; have f3 := natEq s3; have f4 := natEq s4
  apply deriveNat; ipra_simps
  linear_combination f1 + f2 - f3 + z1 + z2 - z3 - 𝔞 (inst2 g zero y) * (f4 + z4) +
    𝔞 (ap2 (sumF a) (succ zero) y) * m

private theorem parts₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] partsF a g := by
  refine ind _ trivial ?_ ?_
  · simp only [Fm.subst_eq, PTm.subst_add, PTm.subst_mul, subst_ap2, subst_inst2, Syn.subst_var, Syn.inst_zero,
      Syn.inst_one, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact parts_zero a g _
  · simp only [Fm.subst_eq, PTm.subst_add, PTm.subst_mul, subst_ap2, subst_inst2, Syn.subst_var, Syn.repl_zero,
      repl_one, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact parts_step a g Prf.hyp0

/-- Summation by parts: `Σ a g + Σ A (g' ∸ g) = A(N) g(N+1) + Σ A (g ∸ g')`. -/
theorem abel_parts (N y : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (agB a g)) (succ N) y + ap2 (sumF (upB a g)) (succ N) y ≐
      ap2 (sumF a) (succ N) y * inst2 g (succ N) y + ap2 (sumF (dnB a g)) (succ N) y := by
  have i := inst (Γ := Γ) (parts₀ a g) (![N, y] : Fin 2 → PTm n)
  simpa using i

end Parts

end LeanProofs.IPRA.AnalyticNumberTheory.AbelParts
