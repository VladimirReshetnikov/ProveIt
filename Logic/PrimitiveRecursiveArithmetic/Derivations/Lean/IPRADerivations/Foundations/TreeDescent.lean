import IPRADerivations.Analysis.Names.Rates.ErrorBudgets
import IPRADerivations.Foundations.TraceInvariant

/-!
# Observational descent along a rooted spanning tree

Packets: `FINER-iPRA-framework-2026-11-16` (`sections/06_finite_relations.tex`: Theorems `thm:exact-descent`
"Exact observational descent" and `thm:metric-descent` "Metric observational descent") and
`scope_ipra_framework_2026-11-16` ("Exact tree descent", "Metric tree descent"): "Each non-root vertex has a
parent of smaller depth. Induct on the depth."

The tree is given by parent and depth arrays, bodies `par(u, y)` and `dep(u, y)`, with
`dep(par u) + 1 = dep u` whenever `dep u ≥ 1`; observations are a body `o(u, y)` (natural numerators). The
ancestors of `v` are the iterates `anc(v, j) = par^j(v)` (one primitive recursion, `ancF`).

* `anc_zero`, `anc_succ`: `anc(v, 0) = v`, `anc(v, j + 1) = par(anc(v, j))`;
* `exact_descent` (`thm:exact-descent`): if `o u = o(par u)` on every tree edge (`dep u ≥ 1`) and the
  depth-zero vertices carry the root observation `o r`, then `o v = o r` for every vertex `v`;
* `metric_descent` (`thm:metric-descent`): if `|o u − o(par u)| ≤ ε(u)` on every tree edge, then
  `|o r − o v| ≤ ∑_{i < dep v} ε(anc(v, i))`, the sum of the edge errors along the tree path from `v` to the
  root.

Both are quantifier-free inductions on the number of parent steps, with the invariant
`dep(anc(v, j)) + j = dep v`.
-/

namespace LeanProofs.IPRA.Foundations.TreeDescent

open_ipra exports
open LeanProofs.IPRA.Probability.Variance (ad)
open LeanProofs.IPRA.Analysis.ErrorBudgets (ad_tri congrAd')

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

section Tree

variable (par dep o eps : PTm 2)

/-- The iterated parent, over `(j, ⟨v, y⟩)`. -/
def ancF : PR 2 := rec2 (fstT (var 0)) (Syn.subst ![var 1, sndT (var 2)] par)

/-- `anc(v, j) = par^j(v)`. -/
abbrev anc (v j y : PTm n) : PTm n := ap2 (ancF par) j (pairT v y)

theorem anc_zero (v y : PTm n) : Γ ⊢[PRAAx] anc par v zero y ≐ v :=
  TraceInvariant.run_zero par v y

theorem anc_succ (v j y : PTm n) : Γ ⊢[PRAAx] anc par v (succ j) y ≐ inst2 par (anc par v j y) y :=
  TraceInvariant.run_succ par j v y

/-- A universal hypothesis of `Γ`, instantiated at a term of the shifted context. -/
theorem inst_shifted {P : Fm PTm (n + 1)} (h : Γ ⊢[PRAAx] Fm.all P) (u : PTm (n + 1)) :
    Γ.map Fm.shift ⊢[PRAAx] P.subst (fun i => Syn.subst (Syn.inst u) (Syn.up (fun i => Syn.var i.succ) i)) := by
  have a := Prf.allE u h.shift
  rw [Fm.subst_subst] at a
  exact a

theorem sub_shift (u : PTm (n + 1)) (y : PTm n) :
    Syn.subst (fun i => Syn.subst (Syn.inst u) (Syn.up (fun i => Syn.var i.succ) i)) (Syn.shift y) = Syn.shift y := by
  rw [show Syn.shift y = Syn.subst (fun i => Syn.var i.succ) y from rfl, Syn.subst_subst]
  congr 1

theorem sub_zero' (u : PTm (n + 1)) :
    (fun i => Syn.subst (Syn.inst u) (Syn.up (fun i => Syn.var i.succ) i)) (0 : Fin (n + 1)) = u := by
  simp

/-- The descent step, at `j + 1 ≤ dep v`. -/
theorem descent_step {v j y : PTm n}
    (hD : Γ ⊢[PRAAx] le one (inst2 dep (anc par v j y) y) ⟶
      (succ (inst2 dep (inst2 par (anc par v j y) y) y) ≐ inst2 dep (anc par v j y) y))
    (hk : Γ ⊢[PRAAx] le (succ j) (inst2 dep v y))
    (ih : Γ ⊢[PRAAx] inst2 dep (anc par v j y) y + j ≐ inst2 dep v y) :
    (Γ ⊢[PRAAx] le one (inst2 dep (anc par v j y) y)) ∧
      (Γ ⊢[PRAAx] inst2 dep (anc par v (succ j) y) y + succ j ≐ inst2 dep v y) := by
  have i := natEq ih
  have one_le : Γ ⊢[PRAAx] le one (inst2 dep (anc par v j y) y) := by
    have k : Γ ⊢[PRAAx] le (succ j) (inst2 dep v y) := hk
    ipra_le sl k using linear_combination i
  refine ⟨one_le, ?_⟩
  have d := natEq (Prf.impE hD one_le)
  have a := natEq (congrInst2 dep (anc_succ (Γ := Γ) par v j y) (.eqRefl y))
  apply deriveNat; ipra_simps
  rw [a]
  linear_combination d + i

/-- The tree hypotheses: `dep(par u) + 1 = dep u`, `o u = o(par u)` for `dep u ≥ 1`. -/
abbrev DepEdge (y : PTm n) : Fm PTm (n + 1) :=
  le one (inst2 dep (var 0) (Syn.shift y)) ⟶
    (succ (inst2 dep (inst2 par (var 0) (Syn.shift y)) (Syn.shift y)) ≐ inst2 dep (var 0) (Syn.shift y))
abbrev ObsEdge (y : PTm n) : Fm PTm (n + 1) :=
  le one (inst2 dep (var 0) (Syn.shift y)) ⟶
    (inst2 o (var 0) (Syn.shift y) ≐ inst2 o (inst2 par (var 0) (Syn.shift y)) (Syn.shift y))
abbrev RootObs (y r : PTm n) : Fm PTm (n + 1) :=
  (inst2 dep (var 0) (Syn.shift y) ≐ zero) ⟶ (inst2 o (var 0) (Syn.shift y) ≐ inst2 o (Syn.shift r) (Syn.shift y))

/-- Variables: `0 = j`; `v`, `y` shifted. -/
abbrev DepInv (v y : PTm n) : Fm PTm (n + 1) :=
  le (var 0) (inst2 dep (Syn.shift v) (Syn.shift y)) ⟶
    ((inst2 o (anc par (Syn.shift v) (var 0) (Syn.shift y)) (Syn.shift y) ≐ inst2 o (Syn.shift v) (Syn.shift y)) ⋏
      (inst2 dep (anc par (Syn.shift v) (var 0) (Syn.shift y)) (Syn.shift y) + var 0 ≐
        inst2 dep (Syn.shift v) (Syn.shift y)))

/-- `thm:exact-descent`: exact agreement on the tree edges carries the root observation to every vertex. -/
theorem exact_descent {y r : PTm n} (hD : Γ ⊢[PRAAx] Fm.all (DepEdge par dep y))
    (hE : Γ ⊢[PRAAx] Fm.all (ObsEdge par dep o y)) (hR : Γ ⊢[PRAAx] Fm.all (RootObs dep o y r))
    (v : PTm n) : Γ ⊢[PRAAx] inst2 o v y ≐ inst2 o r y := by
  have hall : Γ ⊢[PRAAx] Fm.all (DepInv par dep o v y) := by
    refine PRA.qfInd _ ⟨le_QF _ _, trivial, trivial⟩ ?_ ?_
    · simp only [DepInv, Fm.subst_imp, Fm.subst_and, Fm.subst_eq, subst_le, subst_inst2, subst_ap2, subst_pairT,
        PTm.subst_add, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
      refine .impI (.andI ?_ ?_)
      · exact congrInst2 o (anc_zero par v y) (.eqRefl y)
      · have a := natEq (congrInst2 (Γ := le zero (inst2 dep v y) :: Γ) dep (anc_zero par v y) (.eqRefl y))
        apply deriveNat; ipra_simps; rw [a]; ring
    · simp only [DepInv, Fm.subst_imp, Fm.subst_and, Fm.subst_eq, subst_le, subst_inst2, subst_ap2, subst_pairT,
        PTm.subst_add, Syn.subst_var, Syn.repl_zero, subst_repl_shift]
      refine .impI ?_
      have hk : (le (succ (var 0)) (inst2 dep (Syn.shift v) (Syn.shift y)) ::
          DepInv par dep o v y :: Γ.map Fm.shift) ⊢[PRAAx] le (succ (var 0)) (inst2 dep (Syn.shift v) (Syn.shift y)) :=
        Prf.hyp0
      have ih := Prf.impE Prf.hyp1 (le_trans (le_succ_self _) hk)
      have hDu : (le (succ (var 0)) (inst2 dep (Syn.shift v) (Syn.shift y)) ::
          DepInv par dep o v y :: Γ.map Fm.shift) ⊢[PRAAx] (DepEdge par dep y).subst
            (fun i => Syn.subst (Syn.inst (anc par (Syn.shift v) (var 0) (Syn.shift y)))
              (Syn.up (fun i => Syn.var i.succ) i)) := (inst_shifted hD _).wk.wk
      have hEu : (le (succ (var 0)) (inst2 dep (Syn.shift v) (Syn.shift y)) ::
          DepInv par dep o v y :: Γ.map Fm.shift) ⊢[PRAAx] (ObsEdge par dep o y).subst
            (fun i => Syn.subst (Syn.inst (anc par (Syn.shift v) (var 0) (Syn.shift y)))
              (Syn.up (fun i => Syn.var i.succ) i)) := (inst_shifted hE _).wk.wk
      simp only [DepEdge, ObsEdge, Fm.subst_imp, Fm.subst_eq, subst_le, subst_inst2, sub_shift, Syn.subst_var,
        Syn.up_zero, Syn.inst_zero, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] at hDu hEu
      have st := descent_step par dep hDu hk (Prf.andE₂ ih)
      have eo := (congrInst2 o (anc_succ par (Syn.shift v) (var 0) (Syn.shift y)) (.eqRefl _)).eqTrans
        ((Prf.impE hEu st.1).eqSymm.eqTrans (Prf.andE₁ ih))
      exact .andI eo st.2
  have h2 := Prf.allE (inst2 dep v y) hall
  simp only [DepInv, Fm.subst_imp, Fm.subst_and, Fm.subst_eq, subst_le, subst_inst2, subst_ap2, subst_pairT,
    PTm.subst_add, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] at h2
  have c := Prf.impE h2 (le_refl _)
  have z : Γ ⊢[PRAAx] inst2 dep (anc par v (inst2 dep v y) y) y ≐ zero := by
    ipra_lc natEq (Prf.andE₂ c)
  have r := Prf.allE (anc par v (inst2 dep v y) y) hR
  simp only [RootObs, Fm.subst_imp, Fm.subst_eq, subst_inst2, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
    ConciseIPRA.PTm.subst_zero] at r
  exact (Prf.andE₁ c).eqSymm.eqTrans (Prf.impE r z)

/-- The edge error `ε(anc(v, i))`, over `(i, ⟨v, y⟩)`. -/
def epsA : PTm 2 := Syn.subst ![ap2 (ancF par) (var 0) (var 1), sndT (var 1)] eps

theorem epsA_at (i v y : PTm n) :
    Γ ⊢[PRAAx] inst2 (epsA par eps) i (pairT v y) ≐ inst2 eps (anc par v i y) y := by
  have e : inst2 (epsA par eps) i (pairT v y) = inst2 eps (anc par v i y) (sndT (pairT v y)) := by
    simp only [inst2, epsA, Syn.subst_subst]
    congr 1; funext k; fin_cases k <;> simp
  rw [e]; exact congrInst2 eps (.eqRefl _) (snd_pair _ _)

/-- The metric edge hypothesis: `|o u − o(par u)| ≤ ε(u)` for `dep u ≥ 1`. -/
abbrev MetEdge (y : PTm n) : Fm PTm (n + 1) :=
  le one (inst2 dep (var 0) (Syn.shift y)) ⟶
    le (ad (inst2 o (var 0) (Syn.shift y)) (inst2 o (inst2 par (var 0) (Syn.shift y)) (Syn.shift y)))
      (inst2 eps (var 0) (Syn.shift y))

/-- Variables: `0 = j`; `v`, `y` shifted. -/
abbrev MetInv (v y : PTm n) : Fm PTm (n + 1) :=
  le (var 0) (inst2 dep (Syn.shift v) (Syn.shift y)) ⟶
    (le (ad (inst2 o (anc par (Syn.shift v) (var 0) (Syn.shift y)) (Syn.shift y)) (inst2 o (Syn.shift v) (Syn.shift y)))
        (ap2 (sumF (epsA par eps)) (var 0) (pairT (Syn.shift v) (Syn.shift y))) ⋏
      (inst2 dep (anc par (Syn.shift v) (var 0) (Syn.shift y)) (Syn.shift y) + var 0 ≐
        inst2 dep (Syn.shift v) (Syn.shift y)))

/-- `thm:metric-descent`: `|o r − o v| ≤ ∑_{i < dep v} ε(anc(v, i))`. -/
theorem metric_descent {y r : PTm n} (hD : Γ ⊢[PRAAx] Fm.all (DepEdge par dep y))
    (hM : Γ ⊢[PRAAx] Fm.all (MetEdge par dep o eps y)) (hR : Γ ⊢[PRAAx] Fm.all (RootObs dep o y r))
    (v : PTm n) :
    Γ ⊢[PRAAx] le (ad (inst2 o r y) (inst2 o v y)) (ap2 (sumF (epsA par eps)) (inst2 dep v y) (pairT v y)) := by
  have hall : Γ ⊢[PRAAx] Fm.all (MetInv par dep o eps v y) := by
    refine PRA.qfInd _ ⟨le_QF _ _, le_QF _ _, trivial⟩ ?_ ?_
    · simp only [MetInv, Fm.subst_imp, Fm.subst_and, Fm.subst_eq, subst_le, subst_inst2, subst_ap2, subst_pairT,
        PTm.subst_add, PTm.subst_monus, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
      refine .impI (.andI ?_ ?_)
      · have c := natEq (congrAd' (Γ := le zero (inst2 dep v y) :: Γ)
          (congrInst2 o (anc_zero par v y) (.eqRefl y)) (.eqRefl (inst2 o v y)))
        have z := natEq (sum_zero (Γ := le zero (inst2 dep v y) :: Γ) (epsA par eps) (pairT v y))
        have m := natEq (monus_self (Γ := le zero (inst2 dep v y) :: Γ) (inst2 o v y))
        ipra_le 0 using linear_combination z - c - 2 * m
      · have a := natEq (congrInst2 (Γ := le zero (inst2 dep v y) :: Γ) dep (anc_zero par v y) (.eqRefl y))
        apply deriveNat; ipra_simps; rw [a]; ring
    · simp only [MetInv, Fm.subst_imp, Fm.subst_and, Fm.subst_eq, subst_le, subst_inst2, subst_ap2, subst_pairT,
        PTm.subst_add, PTm.subst_monus, Syn.subst_var, Syn.repl_zero, subst_repl_shift]
      refine .impI ?_
      have hk : (le (succ (var 0)) (inst2 dep (Syn.shift v) (Syn.shift y)) ::
          MetInv par dep o eps v y :: Γ.map Fm.shift) ⊢[PRAAx] le (succ (var 0)) (inst2 dep (Syn.shift v) (Syn.shift y)) :=
        Prf.hyp0
      have ih := Prf.impE Prf.hyp1 (le_trans (le_succ_self _) hk)
      have hDu : (le (succ (var 0)) (inst2 dep (Syn.shift v) (Syn.shift y)) ::
          MetInv par dep o eps v y :: Γ.map Fm.shift) ⊢[PRAAx] (DepEdge par dep y).subst
            (fun i => Syn.subst (Syn.inst (anc par (Syn.shift v) (var 0) (Syn.shift y)))
              (Syn.up (fun i => Syn.var i.succ) i)) := (inst_shifted hD _).wk.wk
      have hMu : (le (succ (var 0)) (inst2 dep (Syn.shift v) (Syn.shift y)) ::
          MetInv par dep o eps v y :: Γ.map Fm.shift) ⊢[PRAAx] (MetEdge par dep o eps y).subst
            (fun i => Syn.subst (Syn.inst (anc par (Syn.shift v) (var 0) (Syn.shift y)))
              (Syn.up (fun i => Syn.var i.succ) i)) := (inst_shifted hM _).wk.wk
      simp only [DepEdge, MetEdge, Fm.subst_imp, Fm.subst_eq, subst_le, subst_inst2, PTm.subst_add, PTm.subst_monus,
        sub_shift, Syn.subst_var, Syn.up_zero, Syn.inst_zero, ConciseIPRA.PTm.subst_succ,
        ConciseIPRA.PTm.subst_zero] at hDu hMu
      have st := descent_step par dep hDu hk (Prf.andE₂ ih)
      refine .andI ?_ st.2
      have edge := Prf.impE hMu st.1
      have t := ad_tri (Γ := le (succ (var 0)) (inst2 dep (Syn.shift v) (Syn.shift y)) ::
          MetInv par dep o eps v y :: Γ.map Fm.shift)
        (inst2 o (anc par (Syn.shift v) (succ (var 0)) (Syn.shift y)) (Syn.shift y))
        (inst2 o (anc par (Syn.shift v) (var 0) (Syn.shift y)) (Syn.shift y))
        (inst2 o (Syn.shift v) (Syn.shift y))
      have c := natEq (congrAd' (Γ := le (succ (var 0)) (inst2 dep (Syn.shift v) (Syn.shift y)) ::
          MetInv par dep o eps v y :: Γ.map Fm.shift)
        (congrInst2 o (anc_succ par (Syn.shift v) (var 0) (Syn.shift y)) (.eqRefl (Syn.shift y)))
        (.eqRefl (inst2 o (anc par (Syn.shift v) (var 0) (Syn.shift y)) (Syn.shift y))))
      have s' := sum_succ' (Γ := le (succ (var 0)) (inst2 dep (Syn.shift v) (Syn.shift y)) ::
          MetInv par dep o eps v y :: Γ.map Fm.shift) (epsA par eps) (var 0) (pairT (Syn.shift v) (Syn.shift y))
      have s := natEq (s'.eqTrans (congrAdd (.eqRefl _) (epsA_at par eps _ _ _)))
      have i₁ := Prf.andE₁ ih
      ipra_le sl t + sl edge + sl i₁ using
        rw [s]
        linear_combination -c
  have h2 := Prf.allE (inst2 dep v y) hall
  simp only [MetInv, Fm.subst_imp, Fm.subst_and, Fm.subst_eq, subst_le, subst_inst2, subst_ap2, subst_pairT,
    PTm.subst_add, PTm.subst_monus, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] at h2
  have cc := Prf.impE h2 (le_refl _)
  have z : Γ ⊢[PRAAx] inst2 dep (anc par v (inst2 dep v y) y) y ≐ zero := by
    ipra_lc natEq (Prf.andE₂ cc)
  have r' := Prf.allE (anc par v (inst2 dep v y) y) hR
  simp only [RootObs, Fm.subst_imp, Fm.subst_eq, subst_inst2, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
    ConciseIPRA.PTm.subst_zero] at r'
  exact le_congr (congrAd' (Prf.impE r' z) (.eqRefl _)) (.eqRefl _) (Prf.andE₁ cc)

end Tree

end LeanProofs.IPRA.Foundations.TreeDescent
