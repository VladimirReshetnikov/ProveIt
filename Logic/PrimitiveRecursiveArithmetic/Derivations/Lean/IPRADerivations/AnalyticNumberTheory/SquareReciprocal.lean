import IPRADerivations.AnalyticNumberTheory.HarmonicUpper
import IPRADerivations.Core.LinearCombination
import IPRADerivations.Core.SubstCommand
import IPRADerivations.Core.Header

/-!
# The telescoping bound for `Σ 1/d²` (Khinchin (K6))

Packet: `diophantine-number-theory/hurwitz_khinchin_ipra`, `khinchin.tex` (K6):
"`Σ_{d=2}^{Q} 1/d² ≤ 1/4 + Σ_{d=3}^{Q} 1/(d(d−1)) ≤ 3/4` ... The first telescopes".

With `T(N, F) = Σ_{i<N} ⌊F/(i+1)²⌋`:

* `cancel_le`: `N A ≤ N B` with `N ≥ 1` gives `A ≤ B`;
* `square_bound`: `4N · T(N, F) + 4F ≤ 7N F` for `N ≥ 2`, that is
  `Σ_{d=1}^{N} ⌊F/d²⌋ ≤ 7F/4 − F/N`, by induction on `N` from `N = 2`; the step uses
  `(N+1)² ⌊F/(N+1)²⌋ ≤ F` and the telescoping identity
  `(N+1)(7N F − 4F) + 4F = N (7(N+1) F − 4F)`;
* `square_bound_closed` (closed sentence): with `F = (N!)²` the floors are exact, so
  `Σ_{d=2}^{N} 1/d² ≤ 3/4 − 1/N ≤ 3/4`.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.SquareReciprocal

open_ipra
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicUpper (block_le)
open LeanProofs.IPRA.AnalyticNumberTheory.Totient (quo_eq)

set_option autoImplicit false

variable {n : ℕ}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `⌊F/(i+1)²⌋` in `(i, F)`. -/
abbrev sqB : PTm 2 := quo (var 1) (succ (var 0) * succ (var 0))

/-- `T(N, F) = Σ_{i<N} ⌊F/(i+1)²⌋`. -/
abbrev T (N F : PTm n) : PTm n := ap2 (sumF sqB) N F

theorem inst2_sq (i F : PTm n) : inst2 sqB i F = quo F (succ i * succ i) := by simp [inst2]

/-- `N A ≤ N B`, `N ≥ 1` give `A ≤ B`. -/
theorem cancel_le {Γ : List (Fm PTm n)} {N A B : PTm n} (hN : Γ ⊢[PRAAx] N ≐ succ (pred N))
    (h : Γ ⊢[PRAAx] le (N * A) (N * B)) : Γ ⊢[PRAAx] le A B := by
  refine .orE (lt_or_le B A) ?_ Prf.hyp0
  let Δ : List (Fm PTm n) := lt B A :: Γ
  refine .botE _ (succ_ne_zero (a := pred N + N * monus A (succ B) + monus (N * B) (N * A)) ?_)
  ipra_lc -natEq (eq_add_of_le (Γ := Δ) h.wk) - 𝔞 N * natEq (eq_add_of_le (Γ := Δ) Prf.hyp0) - natEq (Γ := Δ) hN.wk

/-- `(N+1)² ⌊F/(N+1)²⌋ ≤ F`. -/
theorem sq_quo_le {Γ : List (Fm PTm n)} (N F : PTm n) :
    Γ ⊢[PRAAx] le (succ N * succ N * quo F (succ N * succ N)) F := by
  have hK : Γ ⊢[PRAAx] succ N * succ N ≐ succ (N + N * succ N) := by ipra_ring
  have d := div_mod_at (Γ := Γ) (x := F) hK
  refine le_of_eq_add (d := rem F (succ N * succ N)) ?_
  ipra_lc natEq (Prf.andE₁ d)

/-- The invariant at `N = M + 2`: `4N T(N) + 4F ≤ 7NF`. -/
def sqInv (M F : PTm n) : Fm PTm n :=
  le (num 4 * succ (succ M) * T (succ (succ M)) F + num 4 * F) (num 7 * succ (succ M) * F)

ipra_subst sqInv [subst_ap2]

theorem T_succ {Γ : List (Fm PTm n)} (N F : PTm n) :
    Γ ⊢[PRAAx] T (succ N) F ≐ T N F + quo F (succ N * succ N) := by
  refine (sum_succ' sqB N F).eqTrans ?_
  rw [inst2_sq]; exact .eqRefl _

/-- The telescoping step with atoms: `T' = T + q`, `4NT + 4F ≤ 7NF` and `(N+1)² q ≤ F` give
`N (4(N+1) T' + 4F) ≤ N · 7(N+1) F`. -/
theorem sq_step {Γ : List (Fm PTm n)} {N F Tn Tn1 q : PTm n} (ts : Γ ⊢[PRAAx] Tn1 ≐ Tn + q)
    (ih : Γ ⊢[PRAAx] le (num 4 * N * Tn + num 4 * F) (num 7 * N * F))
    (hq : Γ ⊢[PRAAx] le (succ N * succ N * q) F) :
    Γ ⊢[PRAAx] le (N * (num 4 * succ N * Tn1 + num 4 * F)) (N * (num 7 * succ N * F)) := by
  refine le_of_eq_add (d := succ N * monus (num 7 * N * F) (num 4 * N * Tn + num 4 * F) +
    num 4 * monus F (succ N * succ N * q) + num 4 * succ N * q) ?_
  ipra_lc (𝔞 N + 1) * natEq (eq_add_of_le ih) + 4 * natEq (eq_add_of_le hq) - 4 * 𝔞 N * (𝔞 N + 1) * natEq ts

/-- `4N T(N, F) + 4F ≤ 7NF` for `N = M + 2`. -/
theorem square_bound {Γ : List (Fm PTm n)} (M F : PTm n) : Γ ⊢[PRAAx] sqInv M F := by
  have hall : Γ ⊢[PRAAx] Fm.all (sqInv (var 0) (Syn.shift F)) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · -- `N = 2`: `8(F + ⌊F/4⌋) + 4F ≤ 14F`
      rw [subst_sqInv]
      simp only [Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
      have t1 := T_succ (Γ := Γ) (succ zero) F
      have t0 := T_succ (Γ := Γ) zero F
      have q1 : Γ ⊢[PRAAx] quo F (succ zero * succ zero) ≐ F :=
        (congrAp2 quoF (.eqRefl _) (one_mul _)).eqTrans
          (quo_eq (congrSucc (pred_succ _).eqSymm) (by ipra_ring) ((succ_monus_succ _ _).eqTrans (zero_monus _)))
      have e1 := natEq t1; have e0 := natEq t0; have eq1 := natEq q1
      refine le_of_eq_add (d := two * monus F (succ (succ zero) * succ (succ zero) * quo F (succ (succ zero) * succ (succ zero)))) ?_
      ipra_lc 2 * natEq (eq_add_of_le (sq_quo_le (Γ := Γ) (succ zero) F)) - 8 * e1 - 8 * e0 -
        8 * natEq (sum_zero (Γ := Γ) sqB F) - 8 * eq1
    · rw [subst_sqInv]
      simp only [Syn.subst_var, Syn.repl_zero, subst_repl_shift]
      let Δ := sqInv (var 0) (Syn.shift F) :: Γ.map Fm.shift
      let N : PTm (n + 1) := succ (succ (var 0))
      let F' : PTm (n + 1) := Syn.shift F
      have ih : Δ ⊢[PRAAx] sqInv (var 0) F' := Prf.hyp0
      have hN : Δ ⊢[PRAAx] N ≐ succ (pred N) := congrSucc (pred_succ _).eqSymm
      exact cancel_le hN (sq_step (T_succ N F') ih (sq_quo_le N F'))
  have a := Prf.allE M hall
  rw [subst_sqInv] at a
  simpa [Syn.subst_inst_shift] using a

/-- Variable `0 = M`, `N = M + 2`: `4N Σ_{d≤N} (N!)²/d² + 4(N!)² ≤ 7N (N!)²`, i.e.
`Σ_{d=2}^{N} 1/d² ≤ 3/4 − 1/N`. -/
abbrev squareFormula : Fm PTm 1 :=
  sqInv (var 0) (fact (succ (succ (var 0))) * fact (succ (succ (var 0))))

/-- (K6), the telescoping half, as a closed sentence of iPRA. -/
theorem square_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1 squareFormula :=
  closeUniv 1 (square_bound _ _)

end LeanProofs.IPRA.AnalyticNumberTheory.SquareReciprocal
