import IPRADerivations.Core.SumSplit
import IPRADerivations.Core.OrderCertificates
import IPRADerivations.Core.Header

/-!
# Sums over a partition into consecutive blocks (`hurwitz_khinchin_ipra`, gap lists)

Packet: `diophantine-number-theory/hurwitz_khinchin_ipra`, `khinchin.tex`, §"Amplification by the finitely many
residual gaps": "write `[0,1] ∖ U_j` as a finite list of closed rational gaps … process each old gap once,
aggregate the new intervals". On a finite grid of cells, a list of consecutive blocks (the gaps and the covered
runs between them) is given by an endpoint body `e(g, x)` with `e(0) = 0 ≤ e(1) ≤ … ≤ e(G)`; any cellwise
quantity is then summed gap by gap:

  `Σ_{i < e(G)} f(i, x) = Σ_{g < G} Σ_{k < e(g+1) − e(g)} f(e(g) + k, x)`        (`block_sum`).

The inner sum is the body `blockB f e` (`inst2_blockB`), the outer one a plain bounded sum, so a per-block bound
summed with `KhinchinBlock.sum_le_lin1` is a bound on the whole grid. The proof is one quantifier-free induction
on the number of blocks, splitting the cell range at each endpoint (`Core.SumSplit.sum_split`).
-/

namespace LeanProofs.IPRA.Foundations.BlockPartitionSum

open_ipra exports

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- The block sum `Σ_{k < e(g+1) − e(g)} f(e(g) + k, x)` as a body in `0 = g`, `1 = x`. -/
def blockB (f e : PTm 2) : PTm 2 :=
  ap2 (sumF (offB f)) (monus (Syn.subst ![succ (var 0), var 1] e) e) (pairT e (var 1))

theorem inst2_blockB (f e : PTm 2) (g x : PTm n) :
    inst2 (blockB f e) g x =
      ap2 (sumF (offB f)) (monus (inst2 e (succ g) x) (inst2 e g x)) (pairT (inst2 e g x) x) := by
  have h : Syn.subst ![g, x] (Syn.subst ![succ (var 0), var 1] e) = Syn.subst ![succ g, x] e := by
    rw [Syn.subst_subst]; congr 1; funext k; fin_cases k <;> simp
  simp only [inst2, blockB, subst_ap2, subst_pairT, PTm.subst_monus, h]
  simp

/-- `Σ_{i < e(G)} f(i, x) = Σ_{g < G} Σ_{k < e(g+1) − e(g)} f(e(g) + k, x)` for endpoints `e(0) = 0` and
`e(g) ≤ e(g+1)` (`g < G`). -/
theorem block_sum (f e : PTm 2) (G x : PTm n) (h0 : Γ ⊢[PRAAx] inst2 e zero x ≐ zero)
    (hmono : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift G) ⟶
      le (inst2 e (var 0) (Syn.shift x)) (inst2 e (succ (var 0)) (Syn.shift x)))) :
    Γ ⊢[PRAAx] ap2 (sumF f) (inst2 e G x) x ≐ ap2 (sumF (blockB f e)) G x := by
  let P : Fm PTm (n + 1) :=
    ap2 (sumF f) (inst2 e (var 0) (Syn.shift x)) (Syn.shift x) ≐
      ap2 (sumF (blockB f e)) (var 0) (Syn.shift x)
  have atBound : Γ ⊢[PRAAx] P.subst (Syn.inst G) := by
    refine qfIndUpTo G trivial ?_ ?_
    · ipra_ind_simp [P, subst_ap2, subst_inst2, Syn.subst_inst_shift]
      exact ((congrAp2 (sumF f) h0 (.eqRefl _)).eqTrans (sum_zero f x)).eqTrans (sum_zero _ x).eqSymm
    · ipra_ind_simp [P, subst_ap2, subst_inst2, subst_repl_shift]
      refine .impI ?_
      let Θ := lt (var 0) (Syn.shift G) :: P :: Γ.map Fm.shift
      have mono : Θ ⊢[PRAAx] le (inst2 e (var 0) (Syn.shift x)) (inst2 e (succ (var 0)) (Syn.shift x)) :=
        .impE hmono.allOpen.wk.wk Prf.hyp0
      have eB : Θ ⊢[PRAAx] inst2 (blockB f e) (var 0) (Syn.shift x) ≐
          ap2 (sumF (offB f)) (monus (inst2 e (succ (var 0)) (Syn.shift x)) (inst2 e (var 0) (Syn.shift x)))
            (pairT (inst2 e (var 0) (Syn.shift x)) (Syn.shift x)) := by
        rw [inst2_blockB]; exact .eqRefl _
      exact ((congrAp2 (sumF f) (eq_add_of_le mono) (.eqRefl _)).eqTrans (sum_split f _ _ _)).eqTrans
        ((congrAdd Prf.hyp1 eB.eqSymm).eqTrans (sum_succ' _ _ _).eqSymm)
  simpa only [P, Fm.subst_eq, subst_ap2, subst_inst2, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
    using atBound

end LeanProofs.IPRA.Foundations.BlockPartitionSum
