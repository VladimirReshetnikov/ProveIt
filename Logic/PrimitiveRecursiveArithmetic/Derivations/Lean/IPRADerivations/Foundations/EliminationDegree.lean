import IPRADerivations.Core.Permutation
import IPRADerivations.AnalyticNumberTheory.WeightedMangoldt
import IPRADerivations.Foundations.ProductSumDomination
import IPRADerivations.Combinatorics.CoefficientLogConcave
import IPRADerivations.Probability.Variance
import IPRADerivations.Foundations.FiniteAMGM

/-!
# Sums over a permuted range, and the total-degree audit of the elimination polynomial

Packet: `foundations/ipra_resources_and_elimination_2026-11-15`, `lem:elim-degree` ("The
total-degree audit": "If `R ≠ 0`, then `deg R ≤ de`."). Proof: "Consider one nonzero term of the
determinant expansion. In the row `V^r F_c`, an entry selected from column `k` is `f_{k−r}`, and
its degree is at most `d − (k − r)`. In the row `V^s G_c`, the corresponding bound is
`e − (k − s)`. A permutation uses each column `0, …, d + e − 1` once. Therefore the degree of
the selected product is at most
`2de − Σ_{k=0}^{d+e−1} k + Σ_{r=0}^{e−1} r + Σ_{s=0}^{d−1} s = de`."

Number the rows `i < e + d`: the row `i = r < e` is `V^r F_c` and the row `i = e + s` is
`V^s G_c`. The bound on the degree of the entry in row `i` and column `k` is `c_i − k` with
`c_i = d + i` for `i < e` and `c_i = e + (i − e) = i` otherwise, i.e. `c_i = i + d [i < e]`.

* `expB`, `prod_exp`, `exp_inj`: `∏_{i<N} 2^{G_i} = 2^{Σ_{i<N} G_i}` and `2^a = 2^b → a = b`;
* `sum_perm`: `Σ_{i<N} F(σ(i)) = Σ_{j<N} F(j)` for a permutation `σ` of `[0, N)` with inverse
  `τ` (hypotheses as in `Core/Permutation.prod_perm`, from which it follows through the
  exponentials);
* `sum_perm_id`: `Σ_{i<N} σ(i) = Σ_{k<N} k` ("A permutation uses each column once");
* `elim_degree`: if the selected entries have degree bounds `β_i` with
  `β_i + σ(i) = i + d [i < e]` for all rows `i < e + d`, then `Σ_i β_i = e d`: the degree of
  every term of the determinant expansion is at most `d e`.

Not derived: the determinant expansion of the elimination polynomial itself, and that a sum of
terms of degree at most `de` has degree at most `de`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.EliminationDegree

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Permutation (FS rangeAll invAll retAll prod_perm)
open LeanProofs.IPRA.Combinatorics.Stirling (gle gle_of_le gle_above)
open LeanProofs.IPRA.Combinatorics.CoefficientLogConcave (inst2_mul inst2_monus inst2_ap2)
open LeanProofs.IPRA.Combinatorics.CatalanPowers (shift_pair shift_succ)
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (congrPw)
open LeanProofs.IPRA.AnalyticNumberTheory.WeightedMangoldt (pw_lt_exp)
open LeanProofs.IPRA.Foundations.ProductSumDomination (sum_trunc)
open LeanProofs.IPRA.Foundations.FiniteAMGM (prod_succ'')
open LeanProofs.IPRA.Probability.Variance (sum_const_of)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Sums through exponentials -/

/-- `2^{G(i, x)}`. -/
def expB (G : PTm 2) : PTm 2 := ap2 powF G two

theorem inst2_expB (G : PTm 2) (i x : PTm n) :
    inst2 (expB G) i x = pw two (inst2 G i x) := by
  have t : inst2 (two : PTm 2) i x = two := by simp [inst2]
  rw [expB, inst2_ap2, t]

theorem prod_exp_step (G : PTm 2) {N x : PTm n}
    (ih : Γ ⊢[PRAAx] ap2 (prodF (expB G)) N x ≐ pw two (ap2 (sumF G) N x)) :
    Γ ⊢[PRAAx] ap2 (prodF (expB G)) (succ N) x ≐ pw two (ap2 (sumF G) (succ N) x) := by
  have a := prod_succ'' (Γ := Γ) (expB G) N x
  rw [inst2_expB] at a
  exact a.eqTrans ((congrMul ih (.eqRefl _)).eqTrans ((pw_add two _ _).eqSymm.eqTrans
    (congrPw (.eqRefl _) (sum_succ' G N x).eqSymm)))

/-- The induction formula of `prod_exp`; variable `0` is the upper limit. -/
abbrev peF (G : PTm 2) (x : PTm n) : Fm PTm (n + 1) :=
  ap2 (prodF (expB G)) (var 0) (Syn.shift x) ≐ pw two (ap2 (sumF G) (var 0) (Syn.shift x))

/-- `∏_{i<N} 2^{G_i} = 2^{Σ_{i<N} G_i}`. -/
theorem prod_exp (G : PTm 2) (N x : PTm n) :
    Γ ⊢[PRAAx] ap2 (prodF (expB G)) N x ≐ pw two (ap2 (sumF G) N x) := by
  have hall : Γ ⊢[PRAAx] Fm.all (peF G x) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · have b : Γ ⊢[PRAAx] ap2 (prodF (expB G)) zero x ≐ pw two (ap2 (sumF G) zero x) :=
        (prod_zero _ _).eqTrans ((pw_zero two).eqSymm.eqTrans
          (congrPw (.eqRefl _) (sum_zero G x).eqSymm))
      simpa using b
    · have st : (peF G x :: Γ.map Fm.shift) ⊢[PRAAx]
          ap2 (prodF (expB G)) (succ (var 0)) (Syn.shift x) ≐
            pw two (ap2 (sumF G) (succ (var 0)) (Syn.shift x)) :=
        prod_exp_step G Prf.hyp0
      simpa [subst_repl_shift, Syn.repl_zero] using st
  have h2 := Prf.allE N hall
  simpa [Syn.subst_inst_shift, Syn.inst_zero] using h2

/-- `2^a = 2^b → a = b`. -/
theorem exp_inj {a b : PTm n} (h : Γ ⊢[PRAAx] pw two a ≐ pw two b) : Γ ⊢[PRAAx] a ≐ b := by
  refine .orE (lt_or_le a b) ?_ ?_
  · exact lt_irrefl (pw two b) _ (lt_congr h.wk (.eqRefl _)
      (pw_lt_exp (le_refl two) (Prf.hyp0 (Γ := Γ) (φ := lt a b))))
  · refine .orE (lt_or_eq_of_le (Prf.hyp0 (Γ := Γ) (φ := le b a))) ?_ Prf.hyp0.eqSymm
    exact lt_irrefl (pw two a) _ (lt_congr h.wk.wk.eqSymm (.eqRefl _)
      (pw_lt_exp (le_refl two) (Prf.hyp0 (Γ := le b a :: Γ) (φ := lt b a))))

/-! ## Sums over a permuted range -/

section Perm

variable {F S τ : PTm 2}

theorem FS_exp (F S : PTm 2) : FS (expB F) S = expB (FS F S) := by
  simp [FS, expB]

/-- `Σ_{i<N} F(σ(i)) = Σ_{j<N} F(j)` for a permutation `σ` of `[0, N)` with inverse `τ`. -/
theorem sum_perm {N x : PTm n} (hr : Γ ⊢[PRAAx] rangeAll S N x)
    (hinv : Γ ⊢[PRAAx] invAll S τ N x) (hret : Γ ⊢[PRAAx] retAll S τ N x) :
    Γ ⊢[PRAAx] ap2 (sumF (FS F S)) N x ≐ ap2 (sumF F) N x := by
  have p := prod_perm (F := expB F) hr hinv hret
  rw [FS_exp] at p
  exact exp_inj ((prod_exp (FS F S) N x).eqSymm.eqTrans (p.eqTrans (prod_exp F N x)))

theorem FS_id (S : PTm 2) : FS (var 0 : PTm 2) S = S := by simp [FS]

/-- "A permutation uses each column once": `Σ_{i<N} σ(i) = Σ_{k<N} k`. -/
theorem sum_perm_id {N x : PTm n} (hr : Γ ⊢[PRAAx] rangeAll S N x)
    (hinv : Γ ⊢[PRAAx] invAll S τ N x) (hret : Γ ⊢[PRAAx] retAll S τ N x) :
    Γ ⊢[PRAAx] ap2 (sumF S) N x ≐ ap2 (sumF (var 0 : PTm 2)) N x := by
  have h := sum_perm (F := (var 0 : PTm 2)) hr hinv hret
  rw [FS_id] at h
  exact h

end Perm

/-! ## The degree audit -/

/-- `d [i < e]`, over `0 = i`, `1 = ⟨d, e⟩`. -/
def dlB : PTm 2 := fstT (var 1) * monus one (monus (succ (var 0)) (sndT (var 1)))

theorem dl_at (i d e : PTm n) :
    Γ ⊢[PRAAx] inst2 dlB i (pairT d e) ≐ d * gle (succ i) e := by
  have h : inst2 (dlB : PTm 2) i (pairT d e) =
      fstT (pairT d e) * monus one (monus (succ i) (sndT (pairT d e))) := by
    simp [inst2, dlB]
  rw [h]
  exact congrMul (fst_pair _ _) (congrMonus (.eqRefl _) (congrMonus (.eqRefl _) (snd_pair _ _)))

theorem inst2_var0 (i x : PTm n) : inst2 (var 0 : PTm 2) i x = i := by simp [inst2]

/-- `Σ_{i<e+d} d [i < e] = e d`. -/
theorem dl_sum (d e : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF dlB) (e + d) (pairT d e) ≐ e * d := by
  have t : Γ ⊢[PRAAx] ap2 (sumF dlB) (e + d) (pairT d e) ≐ ap2 (sumF dlB) e (pairT d e) := by
    refine sum_trunc _ (le_add_right e d) (.allI (.impI (.impI ?_)))
    simp only [shift_pair]
    have hle : (le (Syn.shift e) (var 0) :: lt (var 0) (Syn.shift (e + d)) :: Γ.map Fm.shift)
        ⊢[PRAAx] le (succ (Syn.shift e)) (succ (var 0)) :=
      (succ_monus_succ _ _).eqTrans Prf.hyp0
    exact (dl_at _ _ _).eqTrans ((congrMul (.eqRefl _) (gle_above hle)).eqTrans (mul_zero _))
  refine t.eqTrans (sum_const_of _ _ _ _ (.allI (.impI ?_)))
  simp only [shift_pair]
  exact (dl_at _ _ _).eqTrans ((congrMul (.eqRefl _) (gle_of_le Prf.hyp0)).eqTrans
    (by apply deriveNat; ipra_simps; ring))

/-- `lem:elim-degree`: for a permutation `σ` of the `e + d` columns and degree bounds `β_i` of
the selected entries with `β_i + σ(i) = i + d [i < e]`, the selected product has degree bound
`Σ_i β_i = e d`. -/
theorem elim_degree {β S τ : PTm 2} {d e x : PTm n}
    (hr : Γ ⊢[PRAAx] rangeAll S (e + d) x) (hinv : Γ ⊢[PRAAx] invAll S τ (e + d) x)
    (hret : Γ ⊢[PRAAx] retAll S τ (e + d) x)
    (hβ : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift (e + d)) ⟶
      (inst2 β (var 0) (Syn.shift x) + inst2 S (var 0) (Syn.shift x) ≐
        var 0 + Syn.shift d * gle (succ (var 0)) (Syn.shift e)))) :
    Γ ⊢[PRAAx] ap2 (sumF β) (e + d) x ≐ e * d := by
  have A := natEq (sum_add (Γ := Γ) β S (e + d) x)
  have B : Γ ⊢[PRAAx] ap2 (sumF (addBody β S)) (e + d) x ≐
      ap2 (sumF (addBody (var 0) dlB)) (e + d) (pairT d e) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    simp only [shift_pair]
    rw [inst2_addBody, inst2_addBody, inst2_var0]
    exact (Prf.impE hβ.allOpen.wk Prf.hyp0).eqTrans
      (congrAdd (.eqRefl _) (dl_at _ _ _).eqSymm)
  have C := natEq (sum_add (Γ := Γ) (var 0 : PTm 2) dlB (e + d) (pairT d e))
  have D : Γ ⊢[PRAAx] ap2 (sumF (var 0 : PTm 2)) (e + d) (pairT d e) ≐
      ap2 (sumF (var 0 : PTm 2)) (e + d) x := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [inst2_var0, inst2_var0]
    exact .eqRefl _
  have eB := natEq B
  have eD := natEq D
  have eP := natEq (sum_perm_id hr hinv hret)
  have eL := natEq (dl_sum (Γ := Γ) d e)
  apply deriveNat; ipra_simps
  linear_combination -A + eB + C + eD - eP + eL

end LeanProofs.IPRA.Foundations.EliminationDegree
