import IPRADerivations.AnalyticNumberTheory.Harmonic
import IPRADerivations.Core.SumOrder
import IPRADerivations.Core.LinearCombination
import IPRADerivations.Core.SubstCommand
import IPRADerivations.Core.Header

/-!
# The dyadic upper bound for harmonic numbers

Packets: `diophantine-number-theory/hurwitz_khinchin_ipra`, `khinchin.tex` (K6):
"`Σ_{d=2}^{2^k} 1/d ≤ k` ... the second splits the sum into the `k` blocks `(2^{j−1}, 2^j]`, each of
sum at most one"; the same bound is the upper half of `AnalyticNumberTheory/Harmonic` (the lower
bound `lem:dyadic`).

With `S(N, F) = Σ_{i<N} ⌊F/(i+1)⌋` (`Harmonic.S`):

* `block_up`: `S(M + d, F) ≤ S(M, F) + d ⌊F/(M+1)⌋` for all `M, d` (each new quotient has a
  denominator `≥ M + 1`);
* `harmonic_upper`: `S(2^k, F) ≤ (k + 1) F` for all `k, F`, by induction on `k`: the block
  `2^k < m ≤ 2^{k+1}` adds at most `2^k ⌊F/(2^k + 1)⌋ ≤ F`;
* `harmonic_upper_closed` (closed sentence): with `F = N!`, `N = 2^k`, the floors are exact and this
  is `Σ_{m=1}^{N} N!/m ≤ (k + 1) N!`, that is `H_{2^k} ≤ k + 1`, equivalently
  `Σ_{d=2}^{2^k} 1/d ≤ k` (K6).
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.HarmonicUpper

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.Harmonic (S hB inst2_h quo_anti S_one)
open LeanProofs.IPRA.Analysis.Products (fact)

set_option autoImplicit false

variable {n : ℕ}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## One block -/

/-- `S(M + d) ≤ S(M) + d ⌊F/(M+1)⌋`. -/
def blockInv (d F M : PTm n) : Fm PTm n := le (S (M + d) F) (S M F + d * quo F (succ M))

ipra_subst blockInv [subst_ap2]

theorem block_up {Γ : List (Fm PTm n)} (d F M : PTm n) : Γ ⊢[PRAAx] blockInv d F M := by
  have hall : Γ ⊢[PRAAx] Fm.all (blockInv (var 0) (Syn.shift F) (Syn.shift M)) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · rw [subst_blockInv]
      simp only [Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
      refine le_congr (congrAp2 (sumF hB) (add_zero _) (.eqRefl _)).eqSymm ?_ (le_refl _)
      ipra_ring
    · rw [subst_blockInv]
      simp only [Syn.subst_var, Syn.repl_zero, subst_repl_shift]
      let Δ := blockInv (var 0) (Syn.shift F) (Syn.shift M) :: Γ.map Fm.shift
      have ih : Δ ⊢[PRAAx] blockInv (var 0) (Syn.shift F) (Syn.shift M) := Prf.hyp0
      -- `S(M + d + 1) = S(M + d) + ⌊F/(M + d + 1)⌋`
      have es : Δ ⊢[PRAAx] S (Syn.shift M + succ (var 0)) (Syn.shift F) ≐
          S (Syn.shift M + var 0) (Syn.shift F) + quo (Syn.shift F) (succ (Syn.shift M + var 0)) := by
        refine (congrAp2 (sumF hB) (add_succ _ _) (.eqRefl _)).eqTrans ((sum_succ' hB _ _).eqTrans ?_)
        rw [inst2_h]; exact .eqRefl _
      have hq : Δ ⊢[PRAAx] le (quo (Syn.shift F) (succ (Syn.shift M + var 0))) (quo (Syn.shift F) (succ (Syn.shift M))) :=
        quo_anti (congrSucc (pred_succ _).eqSymm) ((succ_monus_succ _ _).eqTrans (le_add_right _ _))
      have hs := add_le_add₂ ih hq
      refine le_congr es.eqSymm ?_ hs
      ipra_ring
  have a := Prf.allE d hall
  rw [subst_blockInv] at a
  simpa [Syn.subst_inst_shift] using a

/-! ## The dyadic induction -/

def dyInv (k F : PTm n) : Fm PTm n := le (S (pw two k) F) (succ k * F)

ipra_subst dyInv [subst_ap2]

/-- `2^k ⌊F/(2^k + 1)⌋ ≤ F`. -/
theorem block_le {Γ : List (Fm PTm n)} (K F : PTm n) : Γ ⊢[PRAAx] le (K * quo F (succ K)) F := by
  have d := div_mod_at (Γ := Γ) (x := F) (y := succ K) (c := K) (.eqRefl _)
  refine le_of_eq_add (d := quo F (succ K) + rem F (succ K)) ?_
  ipra_lc natEq (Prf.andE₁ d)

/-- `S(2^k, F) ≤ (k + 1) F`. -/
theorem harmonic_upper {Γ : List (Fm PTm n)} (k F : PTm n) : Γ ⊢[PRAAx] dyInv k F := by
  have hall : Γ ⊢[PRAAx] Fm.all (dyInv (var 0) (Syn.shift F)) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · rw [subst_dyInv]
      simp only [Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
      exact le_congr (S_one _).eqSymm (one_mul _).eqSymm (le_refl _)
    · rw [subst_dyInv]
      simp only [Syn.subst_var, Syn.repl_zero, subst_repl_shift]
      let Δ := dyInv (var 0) (Syn.shift F) :: Γ.map Fm.shift
      have ih : Δ ⊢[PRAAx] dyInv (var 0) (Syn.shift F) := Prf.hyp0
      have ep : Δ ⊢[PRAAx] pw two (succ (var 0)) ≐ pw two (var 0) + pw two (var 0) := by
        have a := natEq (pw_succ (Γ := Δ) two (var 0))
        apply deriveNat; ipra_simps; linear_combination a
      have hb := block_up (Γ := Δ) (pw two (var 0)) (Syn.shift F) (pw two (var 0))
      have hs := le_trans hb (add_le_add₂ ih (block_le _ _))
      refine le_congr (congrAp2 (sumF hB) ep (.eqRefl _)).eqSymm ?_ hs
      ipra_ring
  have a := Prf.allE k hall
  rw [subst_dyInv] at a
  simpa [Syn.subst_inst_shift] using a

/-- Variable `0 = k`: `Σ_{m=1}^{N} N!/m ≤ (k + 1) N!` for `N = 2^k`, i.e. `H_{2^k} ≤ k + 1`. -/
abbrev upperFormula : Fm PTm 1 := le (S (pw two (var 0)) (fact (pw two (var 0)))) (succ (var 0) * fact (pw two (var 0)))

/-- (K6), the harmonic half, as a closed sentence of iPRA. -/
theorem harmonic_upper_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1 upperFormula :=
  closeUniv 1 (harmonic_upper _ _)

end LeanProofs.IPRA.AnalyticNumberTheory.HarmonicUpper
