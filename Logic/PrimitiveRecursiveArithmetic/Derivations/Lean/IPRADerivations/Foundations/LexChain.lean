import IPRADerivations.Foundations.LexPotential
import IPRADerivations.Core.SumLemmas

/-!
# The controlled lexicographic chain bound (`ipra_resources_and_elimination_2026-11-15`, `thm:controlled-lex`)

Packet: `foundations/ipra_resources_and_elimination_2026-11-15`, theorem `thm:controlled-lex`: "Fix
`d`. Let `v_s, v_{s+1}, …, v_{s+L−1} ∈ ℕ^d` be a finite sequence such that
`v_t >_lex v_{t+1}` whenever both terms occur, and every coordinate of `v_t` is at most
`h(x, t)`. Then `s + L ≤ F_d(x, s)`. For each fixed `d`, this statement ... is provable in iPRA."

The sequence is given by `d` coordinate terms `w_j(i, y)` (`i` is the position in the chain,
so `v_{s+i} = (w_j(i, y))_j`), and the chain has `L = L' + 1` members. The hypotheses are
formulas with a bounded quantifier, derivable in the context:

* for `i < L'`: `v_{s+i} >_lex v_{s+i+1}`;
* the envelope at the first member, `w_j(0, y) ≤ h(x, s)`, and at every later member,
  `w_j(i + 1, y) ≤ h(x, s + i + 1)` for `i < L'`.

The proof iterates the potential of `Foundations/LexPotential` instead of cutting the chain
into blocks:

* `pair_congr₁`, `G_congr_t`, `subst_G`: the potential depends only on the value of the time,
  and commutes with substitution;
* `co`: the tuple at a position;
* `potential_chain`: for `i ≤ L'`, `G(v_{s+i}, s + i) ≤ G(v_s, s)`, by quantifier-free
  induction on `i` in the context of the two hypotheses;
* `controlled_lex`: `s + L' + 1 ≤ F_d(x, s)`, for every external dimension `d`.

The empty chain (`L = 0`) is `s ≤ F_d(x, s)`, which is `fuel_grow`. Not derived:
`thm:automatic-lex-fuel` (the trajectory envelope as a bounded maximum and the contradiction
at time `B(x)`), and the exactness of the bound.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.LexChain

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.LexFuelMonotone (itStep itP F)
open LeanProofs.IPRA.Foundations.LexPotential (G lexgt G_lower G_upper G_descent)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {k : ℕ} {Γ : List (Fm PTm k)}

theorem pair_congr₁ {a a' b b' : PTm k} (ha : Γ ⊢[PRAAx] a ≐ a') (hb : Γ ⊢[PRAAx] b ≐ b') :
    Γ ⊢[PRAAx] pairT a b ≐ pairT a' b' :=
  congrAdd (congrMul (congrAdd ha hb) (congrAdd ha hb)) ha

variable (h : PTm 2)

/-- The potential depends only on the value of the time. -/
theorem G_congr_t : {d : ℕ} → (c : Fin d → PTm k) → (x : PTm k) → {t t' : PTm k} →
    (Γ ⊢[PRAAx] t ≐ t') → (Γ ⊢[PRAAx] G h c x t ≐ G h c x t')
  | 0, _, _, _, _, e => congrSucc e
  | d + 1, c, x, _, _, e =>
    congrAp2 (rec2 (sndT (var 0)) (itStep (F h d))) (.eqRefl _)
      (pair_congr₁ (.eqRefl x) (G_congr_t (fun j => c j.succ) x e))

/-- The potential commutes with substitution. -/
theorem subst_G {m : ℕ} (σ : Fin k → PTm m) : {d : ℕ} → (c : Fin d → PTm k) → (x t : PTm k) →
    Syn.subst σ (G h c x t) =
      G h (fun j => Syn.subst σ (c j)) (Syn.subst σ x) (Syn.subst σ t)
  | 0, _, _, _ => by simp [G]
  | d + 1, c, x, t => by
    show Syn.subst σ (itP (F h d) (c 0) x (G h (fun j => c j.succ) x t)) =
      itP (F h d) (Syn.subst σ (c 0)) (Syn.subst σ x)
        (G h (fun j => Syn.subst σ (c j.succ)) (Syn.subst σ x) (Syn.subst σ t))
    rw [← subst_G σ (fun j => c j.succ) x t]
    simp only [subst_ap2, subst_pairT]

/-- The tuple at position `i` of the chain. -/
abbrev co {d : ℕ} (w : Fin d → PTm 2) (i y : PTm k) : Fin d → PTm k := fun j => inst2 (w j) i y

variable {h}

/-- The potential does not increase along the chain: `G(v_{s+i}, s + i) ≤ G(v_s, s)` for
`i ≤ L'`. -/
theorem potential_chain
    (hh : ∀ {k : ℕ} {Γ : List (Fm PTm k)} {x s t : PTm k},
      (Γ ⊢[PRAAx] le s t) → (Γ ⊢[PRAAx] le (inst2 h x s) (inst2 h x t)))
    {d : ℕ} (w : Fin d → PTm 2) {s x y L' : PTm k}
    (hdesc : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift L') ⟶
      lexgt (co w (var 0) (Syn.shift y)) (co w (succ (var 0)) (Syn.shift y))))
    (henv : ∀ j, Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift L') ⟶
      le (inst2 (w j) (succ (var 0)) (Syn.shift y))
        (inst2 h (Syn.shift x) (succ (Syn.shift s + var 0))))) :
    Γ ⊢[PRAAx] Fm.all (le (var 0) (Syn.shift L') ⟶
      le (G h (co w (var 0) (Syn.shift y)) (Syn.shift x) (Syn.shift s + var 0))
        (G h (co w zero (Syn.shift y)) (Syn.shift x) (Syn.shift s + zero))) := by
  refine PRA.qfInd _ ⟨le_QF _ _, le_QF _ _⟩ ?_ ?_
  · simp only [Fm.subst_imp, subst_le, subst_G, subst_inst2, PTm.subst_add, Syn.subst_var,
      Syn.inst_zero, Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero]
    exact .impI (le_refl _)
  · simp only [Fm.subst_imp, subst_le, subst_G, subst_inst2, PTm.subst_add, Syn.subst_var,
      Syn.repl_zero, subst_repl_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    refine .impI ?_
    exact le_congr (G_congr_t h _ _ (add_succ _ _).eqSymm) (.eqRefl _)
      (le_trans
        (G_descent hh (c := co w (var 0) (Syn.shift y))
          (c' := co w (succ (var 0)) (Syn.shift y)) (x := Syn.shift x)
          (t := Syn.shift s + var 0) (.impE hdesc.allOpen.wk.wk Prf.hyp0)
          (fun j => .impE (henv j).allOpen.wk.wk Prf.hyp0))
        (.impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0)))

/-- `thm:controlled-lex`: a controlled strictly descending chain with `L' + 1` members starting
at time `s` satisfies `s + L' + 1 ≤ F_d(x, s)`. -/
theorem controlled_lex
    (hh : ∀ {k : ℕ} {Γ : List (Fm PTm k)} {x s t : PTm k},
      (Γ ⊢[PRAAx] le s t) → (Γ ⊢[PRAAx] le (inst2 h x s) (inst2 h x t)))
    {d : ℕ} (w : Fin d → PTm 2) {s x y L' : PTm k}
    (hdesc : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift L') ⟶
      lexgt (co w (var 0) (Syn.shift y)) (co w (succ (var 0)) (Syn.shift y))))
    (henv₀ : ∀ j, Γ ⊢[PRAAx] le (inst2 (w j) zero y) (inst2 h x s))
    (henv : ∀ j, Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift L') ⟶
      le (inst2 (w j) (succ (var 0)) (Syn.shift y))
        (inst2 h (Syn.shift x) (succ (Syn.shift s + var 0))))) :
    Γ ⊢[PRAAx] le (succ (s + L')) (inst2 (F h d) x s) := by
  have hall := potential_chain hh w hdesc henv
  have i := Prf.allE L' hall
  simp only [Fm.subst_imp, subst_le, subst_G, subst_inst2, PTm.subst_add, Syn.subst_var,
    Syn.inst_zero, Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero] at i
  have c₁ := Prf.impE i (le_refl L')
  exact le_trans (G_lower hh (co w L' y) x (s + L'))
    (le_trans c₁ (le_congr (G_congr_t h _ _ (add_zero s)).eqSymm (.eqRefl _)
      (G_upper hh henv₀)))

end LeanProofs.IPRA.Foundations.LexChain
