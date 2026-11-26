import IPRADerivations.Foundations.TraceComposition
import IPRADerivations.Core.Header

/-!
# Closure of certified trace systems under products, branches and loops

Packet: `foundations/ipra_certified_finitary_framework_2026-11-15`, `paper/sections/04_trace_compiler.tex`,
Theorem `thm:transducer-closure` ("Finite transducer closure"): certified finite transducers are closed
under sequential composition, finite products, bounded loops, overlapping guarded branches and finite
acyclic networks. "Products pair states and conjoin invariants. A bounded loop is already a trace. A
guarded branch uses a total Boolean."

A certified trace system is a step `f` with a quantifier-free invariant `R(s, y)` preserved by the step
(`TraceComposition.Preserved`). Sequential composition is `TraceComposition.compose` and acyclic networks are
`Foundations/ForwardValidity`; here:

* `prodStep`, `prodInv` (with `app1_prodStep`, `rel_prodInv`): the product step
  `⟨s₁, s₂⟩ ↦ ⟨f₁(s₁), f₂(s₂)⟩` and the conjoined invariant `R₁(s₁) ∧ R₂(s₂)`;
* `prod_preserved`: the product of two certified systems is certified;
* `branchStep` (with `app1_branchStep`): the guarded branch `b(s) f(s) + (1 ∸ b(s)) g(s)` for a Boolean
  guard `b`; `branch_preserved`: if both branches preserve `R`, so does the branch;
* `loop_preserved`: `k` iterations of a certified step preserve its invariant (a bounded loop is a trace,
  `TraceComposition.run_invariant`).
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.TraceClosure

open_ipra
open LeanProofs.IPRA.Foundations.IterationFusion (app1 iter rel rel_congr congrApp1)
open LeanProofs.IPRA.Foundations.TraceComposition (Preserved run_invariant)

theorem const_vec {k : ℕ} (t : PTm k) : (fun _ : Fin 1 => t) = (![t] : Fin 1 → PTm k) := by
  funext i; fin_cases i; rfl

/-! ## Products -/

section Product

variable (f₁ f₂ : PTm 1) (R₁ R₂ : Fm PTm 2)

/-- The product step `⟨s₁, s₂⟩ ↦ ⟨f₁(s₁), f₂(s₂)⟩`. -/
def prodStep : PTm 1 := pairT (app1 f₁ (fstT (Syn.var 0))) (app1 f₂ (sndT (Syn.var 0)))

/-- The conjoined invariant `R₁(s₁, y) ∧ R₂(s₂, y)`. -/
def prodInv : Fm PTm 2 :=
  R₁.subst ![fstT (Syn.var 0), Syn.var 1] ⋏ R₂.subst ![sndT (Syn.var 0), Syn.var 1]

theorem app1_prodStep {k : ℕ} (s : PTm k) :
    app1 (prodStep f₁ f₂) s = pairT (app1 f₁ (fstT s)) (app1 f₂ (sndT s)) := by
  simp [app1, prodStep, Syn.subst_subst, const_vec]

theorem rel_prodInv {k : ℕ} (s y : PTm k) :
    rel (prodInv R₁ R₂) s y = (rel R₁ (fstT s) y ⋏ rel R₂ (sndT s) y) := by
  simp only [rel, prodInv, Fm.subst_and, Fm.subst_subst]
  congr 1 <;> (congr 1; funext i; fin_cases i <;> simp)

variable {f₁ f₂ R₁ R₂}

/-- The product of two certified trace systems is certified. -/
theorem prod_preserved (h₁ : Preserved f₁ R₁) (h₂ : Preserved f₂ R₂) :
    Preserved (prodStep f₁ f₂) (prodInv R₁ R₂) := by
  intro k Γ s y h
  rw [rel_prodInv] at h ⊢
  rw [app1_prodStep]
  exact .andI (rel_congr R₁ (fst_pair _ _).eqSymm (.eqRefl _) (h₁ (Prf.andE₁ h)))
    (rel_congr R₂ (snd_pair _ _).eqSymm (.eqRefl _) (h₂ (Prf.andE₂ h)))

end Product

/-! ## Guarded branches -/

section Branch

variable (b f g : PTm 1)

/-- The guarded branch `b(s) f(s) + (1 ∸ b(s)) g(s)`. -/
def branchStep : PTm 1 :=
  app1 b (Syn.var 0) * app1 f (Syn.var 0) + monus one (app1 b (Syn.var 0)) * app1 g (Syn.var 0)

theorem app1_branchStep {k : ℕ} (s : PTm k) :
    app1 (branchStep b f g) s = app1 b s * app1 f s + monus one (app1 b s) * app1 g s := by
  simp [app1, branchStep, Syn.subst_subst, const_vec]
  try rfl

variable {b f g} {R : Fm PTm 2}

/-- If the guard is Boolean and both branches preserve `R`, the guarded branch preserves `R`. -/
theorem branch_preserved
    (hb : ∀ {k : ℕ} {Γ : List (Fm PTm k)} (s : PTm k), Γ ⊢[PRAAx] (app1 b s ≐ zero) ⋎ (app1 b s ≐ one))
    (hf : Preserved f R) (hg : Preserved g R) : Preserved (branchStep b f g) R := by
  intro k Γ s y h
  refine .orE (hb s) ?_ ?_
  · have e : ((app1 b s ≐ zero) :: Γ) ⊢[PRAAx] app1 (branchStep b f g) s ≐ app1 g s := by
      rw [app1_branchStep]
      exact (congrAdd ((congrMul Prf.hyp0 (.eqRefl _)).eqTrans (zero_mul _))
        ((congrMul ((congrMonus (.eqRefl _) Prf.hyp0).eqTrans (monus_zero one)) (.eqRefl _)).eqTrans
          (one_mul _))).eqTrans (zero_add _)
    exact rel_congr R e.eqSymm (.eqRefl _) (hg h.wk)
  · have e : ((app1 b s ≐ one) :: Γ) ⊢[PRAAx] app1 (branchStep b f g) s ≐ app1 f s := by
      rw [app1_branchStep]
      exact (congrAdd ((congrMul Prf.hyp0 (.eqRefl _)).eqTrans (one_mul _))
        ((congrMul ((congrMonus (.eqRefl _) Prf.hyp0).eqTrans (monus_self one)) (.eqRefl _)).eqTrans
          (zero_mul _))).eqTrans (add_zero _)
    exact rel_congr R e.eqSymm (.eqRefl _) (hf h.wk)

end Branch

/-! ## Bounded loops -/

/-- `k` iterations of a certified step preserve its invariant: a bounded loop is a trace. -/
theorem loop_preserved {f : PTm 1} {R : Fm PTm 2} (hqf : R.QF) (hp : Preserved f R) {n : ℕ}
    {Γ : List (Fm PTm n)} {x y : PTm n} (h : Γ ⊢[PRAAx] rel R x y) (t : PTm n) :
    Γ ⊢[PRAAx] rel R (iter f t x) y :=
  run_invariant hqf hp h t

end LeanProofs.IPRA.Foundations.TraceClosure
