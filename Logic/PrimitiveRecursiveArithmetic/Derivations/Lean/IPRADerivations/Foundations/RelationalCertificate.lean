import IPRADerivations.Foundations.BoundedDescent

/-!
# Reflection of relational viability certificates

Packets: `foundations/ipra_finite_use_framework_2026-11-15` and its `_v2` edition,
`sections/05_relational.tex`, Definition "Viability certificate" and Proposition `prop:rel-cert`
("Relational certificate reflection"): `RelCertOK(x, h, c) = 1 → TranscriptOK(x, h, extract(c)) = 1`.
"Extract the root path by following the selected edge. Induct on the decreasing resource. The checker
supplies local validity and the pointer to the next viable node. At resource zero or at a marked terminal
node, the checker supplies `Post = 1`."

The certificate graph is given by unary terms on node codes: the selected successor `nx(v)`, the resource
`ρ(v)`, the viability label `V(v)`, the terminal label `H(v)` (a bit), the postcondition check `P(v)` and the
local validity of the selected answer `Lc(v)`. The checked clauses (`Checked`) are rules:

* `bit`: `H(v)` is `0` or `1`;
* `live`: a viable nonterminal node has a locally valid selected answer pointing to a viable node of smaller
  resource;
* `post`: a viable terminal node satisfies the postcondition.

The extracted path follows `nx` and stops at terminal nodes: `step(v) = H(v) v + (1 ∸ H(v)) nx(v)`.

* `step_term`, `step_live`: the step fixes terminal nodes and follows the selected edge otherwise;
* `descent`: the hypotheses of `BoundedDescent.Descent` for the step, the resource, `H` and `V`;
* `path_viable`, `path_local`: every node of the extracted path is viable, and every nonterminal one has a
  locally valid answer (`descent_inv`);
* `path_post` (`prop:rel-cert`): after `ρ(root)` steps the path is at a terminal node satisfying the
  postcondition (`BoundedDescent.terminal`).
-/

namespace LeanProofs.IPRA.Foundations.RelationalCertificate

open_ipra exports
open LeanProofs.IPRA.Foundations.BoundedDescent (Descent descent_inv terminal)
open LeanProofs.IPRA.Foundations.BoundedReflection (one_ne_zero)

variable (nx ρ V H P Lc : PTm 1)

/-- The path step: stay at a terminal node, follow the selected edge otherwise. -/
def stepT : PTm 1 := app1 H (Syn.var 0) * Syn.var 0 + monus one (app1 H (Syn.var 0)) * app1 nx (Syn.var 0)

theorem app1_stepT {k : ℕ} (s : PTm k) :
    app1 (stepT nx H) s = app1 H s * s + monus one (app1 H s) * app1 nx s := by
  have e : (fun _ : Fin 1 => s) = (![s] : Fin 1 → PTm k) := by funext i; fin_cases i; rfl
  simp [app1, stepT, Syn.subst_subst, e]
  try rfl

/-- The checked clauses of a viability certificate. -/
structure Checked : Prop where
  bit : ∀ {k : ℕ} {Δ : List (Fm PTm k)} (s : PTm k), Δ ⊢[PRAAx] (app1 H s ≐ zero) ⋎ (app1 H s ≐ one)
  live : ∀ {k : ℕ} {Δ : List (Fm PTm k)} {s : PTm k}, (Δ ⊢[PRAAx] app1 V s ≐ one) →
    (Δ ⊢[PRAAx] app1 H s ≐ zero) →
      (Δ ⊢[PRAAx] (app1 V (app1 nx s) ≐ one) ⋏ (lt (app1 ρ (app1 nx s)) (app1 ρ s) ⋏ (app1 Lc s ≐ one)))
  post : ∀ {k : ℕ} {Δ : List (Fm PTm k)} {s : PTm k}, (Δ ⊢[PRAAx] app1 V s ≐ one) →
    (Δ ⊢[PRAAx] app1 H s ≐ one) → (Δ ⊢[PRAAx] app1 P s ≐ one)

variable {nx ρ V H P Lc}

theorem step_term {k : ℕ} {Δ : List (Fm PTm k)} {s : PTm k} (h : Δ ⊢[PRAAx] app1 H s ≐ one) :
    Δ ⊢[PRAAx] app1 (stepT nx H) s ≐ s := by
  rw [app1_stepT]
  exact (congrAdd ((congrMul h (.eqRefl s)).eqTrans (one_mul s))
    ((congrMul ((congrMonus (.eqRefl _) h).eqTrans (monus_self one)) (.eqRefl _)).eqTrans (zero_mul _))).eqTrans
    (add_zero s)

theorem step_live {k : ℕ} {Δ : List (Fm PTm k)} {s : PTm k} (h : Δ ⊢[PRAAx] app1 H s ≐ zero) :
    Δ ⊢[PRAAx] app1 (stepT nx H) s ≐ app1 nx s := by
  rw [app1_stepT]
  exact (congrAdd ((congrMul h (.eqRefl s)).eqTrans (zero_mul s))
    ((congrMul ((congrMonus (.eqRefl _) h).eqTrans (monus_zero one)) (.eqRefl _)).eqTrans (one_mul _))).eqTrans
    (zero_add _)

/-- The path step satisfies the hypotheses of bounded descent. -/
theorem descent (C : Checked nx ρ V H P Lc) : Descent (stepT nx H) ρ H V where
  pres := fun {k} {Δ} {s} hv => by
    refine .orE (C.bit s) ?_ ?_
    · exact (congrApp1 V (step_live Prf.hyp0)).eqTrans (Prf.andE₁ (C.live hv.wk Prf.hyp0))
    · exact (congrApp1 V (step_term Prf.hyp0)).eqTrans hv.wk
  fix := fun hv hd => step_term hd
  dec := fun {k} {Δ} {s} hv hnd => by
    refine .orE (C.bit s) ?_ ?_
    · exact lt_congr (congrApp1 ρ (step_live Prf.hyp0)).eqSymm (.eqRefl _)
        (Prf.andE₁ (Prf.andE₂ (C.live hv.wk Prf.hyp0)))
    · exact .botE _ (.impE hnd.wk Prf.hyp0)

/-- Every node of the extracted path is viable. -/
theorem path_viable (C : Checked nx ρ V H P Lc) {k : ℕ} {Δ : List (Fm PTm k)} {root : PTm k}
    (h₀ : Δ ⊢[PRAAx] app1 V root ≐ one) (t : PTm k) :
    Δ ⊢[PRAAx] app1 V (iter (stepT nx H) t root) ≐ one :=
  Prf.andE₁ (descent_inv (descent C) h₀ t)

/-- Every nonterminal node of the extracted path has a locally valid selected answer. -/
theorem path_local (C : Checked nx ρ V H P Lc) {k : ℕ} {Δ : List (Fm PTm k)} {root t : PTm k}
    (h₀ : Δ ⊢[PRAAx] app1 V root ≐ one)
    (ht : Δ ⊢[PRAAx] app1 H (iter (stepT nx H) t root) ≐ zero) :
    Δ ⊢[PRAAx] app1 Lc (iter (stepT nx H) t root) ≐ one :=
  Prf.andE₂ (Prf.andE₂ (C.live (path_viable C h₀ t) ht))

/-- `prop:rel-cert`: after `ρ(root)` steps the extracted path is at a terminal node satisfying the
postcondition. -/
theorem path_post (C : Checked nx ρ V H P Lc) {k : ℕ} {Δ : List (Fm PTm k)} {root : PTm k}
    (h₀ : Δ ⊢[PRAAx] app1 V root ≐ one) :
    Δ ⊢[PRAAx] (app1 H (iter (stepT nx H) (app1 ρ root) root) ≐ one) ⋏
      (app1 P (iter (stepT nx H) (app1 ρ root) root) ≐ one) := by
  have ht := terminal (descent C) h₀
  exact .andI ht (C.post (path_viable C h₀ _) ht)

end LeanProofs.IPRA.Foundations.RelationalCertificate
