import ConciseIPRA.NativeZeroNormal

/-!
# Equality in the initializer

`NIPrf` has the equality rule of the package `Research/initializer_equality`,
on the zero-normal syntax of `NativeZeroNormal`.  Transport in a term template
is replaced by replacement of the initializer of an iterator:

  **Seed**: from `s = t` and `C(c, s, h) = r` infer `C(c, t, h) = r`,

where `C(c, a, h)` is the iterator `I(c, a; u.h)` with the zero computation
contracted, so that `C(0, a, h)` is `a`.  The counter and the body are not
changed, and no template is supplied.  With successor computation, `QE`, `DE`,
`D` by cases and `Q` by progress there are seven rules; there is no
reflexivity rule and no transport rule.

* `niprf_iff_nprf`: `NPrf Γ A ↔ NIPrf (Γ.map fnf) (fnf A)`;
* `NIPrf.normal`: from zero-normal hypotheses only zero-normal formulas are
  derivable.

At the counter `0` the rule replaces at the root: from `s = t` and `s = r`
it infers `t = r` (`NIPrf.root`), which gives reflexivity from one successor
computation, symmetry and transitivity.  At the counter `1` it applies any
template `h`: `I(1, s; u.h)` is `h(s)` by successor computation, so from
`s = t` and `h(s) = u` the rule gives `I(1, t; u.h) = u`, and that is
`h(t) = u` (`NIPrf.trOneNf`).

The package has six rules, because it uses the single introduction of
`NativeOneIntro`; here the two introductions of the kernel are kept.
-/

namespace LeanProofs.ConciseIPRA

open Syn
open Tm (zero succ iter)
open scoped Fm
open ZeroNormalization

variable {n m : ℕ}

/-- Derivability on zero-normal terms with replacement of an initializer as
the only equality rule. -/
inductive NIPrf : {n : ℕ} → List (NFm n) → NFm n → Prop
  | hyp {n : ℕ} {Γ : List (NFm n)} {A : NFm n} (h : A ∈ Γ) : NIPrf Γ A
  /-- `I(S c, a; u.h) = h[I(c, a; u.h)/u]`. -/
  | iterSucc {n : ℕ} {Γ : List (NFm n)} (c a : Tm n) (h : Tm (n + 1)) :
      NIPrf Γ (fnf (.eq (iter (succ c) a h) (Syn.subst (inst (iter c a h)) h)))
  /-- Seed: from `s = t` and `C(c, s, h) = r` infer `C(c, t, h) = r`. -/
  | seed {n : ℕ} {Γ : List (NFm n)} (c : Tm n) (h : Tm (n + 1)) {s t r : Tm n}
      (h₁ : NIPrf Γ (.eq s t)) (h₂ : NIPrf Γ (.eq (nf (iter c s h)) r)) :
      NIPrf Γ (.eq (nf (iter c t h)) r)
  | qE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 1)} (t : Tm n)
      (h₁ : NIPrf Γ (.Q B)) (h₂ : NIPrf Γ (fnf (B.subst (inst zero)))) :
      NIPrf Γ (fnf (B.subst (inst t)))
  | dE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 2)} {A : NFm n}
      (h₁ : NIPrf Γ (.D B)) (h₂ : NIPrf (.Q B :: Γ.map NFm.shift) A.shift) : NIPrf Γ A
  | dICase {n : ℕ} {Γ : List (NFm n)} (B : NFm (n + 2)) (t : Tm n) (hB : fnf B = B)
      (h : NIPrf ((fnf ((B.subst (up (inst t))).subst (inst zero))).shift :: Γ.map NFm.shift)
        (fnf ((B.subst (up (inst t))).subst (repl (succ (var 0)))))) :
      NIPrf Γ (.D B)
  | qIInd {n : ℕ} {Γ : List (NFm n)} (s₁ s₂ : Tm (n + 1)) (h₁ : nf s₁ = s₁) (h₂ : nf s₂ = s₂)
      (h : NIPrf (NFm.eq s₁ s₂ :: Γ.map NFm.shift)
        (fnf ((NFm.eq s₁ s₂).subst (repl (succ (var 0)))))) :
      NIPrf Γ (.Q (.eq s₁ s₂))

variable {Γ : List (NFm n)} {A : NFm n}

namespace NIPrf

/-- Every rule is a derived rule of the kernel, up to normal forms. -/
theorem toNPrf (h : NIPrf Γ A) : NPrf Γ A := by
  induction h with
  | hyp h => exact .hyp h
  | iterSucc c a h => exact (equivFnf _).mp (.iterSucc c a h)
  | @seed _ Γ c h s t r _ _ ih₁ ih₂ =>
    have hc : NPrf Γ (.eq (iter c s h) (iter c t h)) := by
      have k := NPrf.eqCongr
        (iter (Syn.shift c) (Syn.var 0) (Syn.subst (up fun i => Syn.var i.succ) h)) ih₁
      simpa only [Tm.subst_iter, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
        Syn.subst_up_inst_up_shift] using k
    exact NPrf.eqTrans (NPrf.eqSymm (eqNf _)) (NPrf.eqTrans (NPrf.eqSymm hc)
      (NPrf.eqTrans (eqNf _) ih₂))
  | qE t _ _ ih₁ ih₂ => exact (equivFnf _).mp (.qE t ih₁ ((equivFnf _).mpr ih₂))
  | dE _ _ ih₁ ih₂ => exact .dE ih₁ ih₂
  | dICase B t _ _ ih =>
    exact .dICase B t ((equivFnf _).mpr
      (NPrf.cut1 ((equivFnf _).shift.mp NPrf.hyp0) (NPrf.wkUnder ih)))
  | qIInd s₁ s₂ _ _ _ ih => exact .qIInd s₁ s₂ ((equivFnf _).mpr ih)

/-- Replacement at the root: Seed at the counter `0`. -/
theorem root {x y z : Tm n} (h₁ : NIPrf Γ (.eq (nf x) (nf y)))
    (h₂ : NIPrf Γ (.eq (nf x) (nf z))) : NIPrf Γ (.eq (nf y) (nf z)) := by
  have k := NIPrf.seed zero (Syn.var 0) h₁ (r := nf z)
    (by simpa only [nf_iter, nf_zero, smartI_zero, nf_idempotent] using h₂)
  simpa only [nf_iter, nf_zero, smartI_zero, nf_idempotent] using k

/-- One iteration applies the body: `I(1, s; u.h) = h(s)`. -/
theorem stepOne (h : Tm (n + 1)) (s : Tm n) :
    NIPrf Γ (.eq (nf (iter (succ zero) (nf s) h)) (nf (Syn.subst (inst s) h))) := by
  have k : NIPrf Γ (.eq (nf (iter (succ zero) (nf s) h))
      (nf (Syn.subst (inst (iter zero (nf s) h)) h))) := NIPrf.iterSucc zero (nf s) h
  rwa [nf_subst_congr (t := h) (t' := h) (σ' := inst s) rfl (fun i => by
    refine Fin.cases ?_ (fun j => ?_) i
    · show nf (iter zero (nf s) h) = nf s
      simp only [nf_iter, nf_zero, smartI_zero, nf_idempotent]
    · rfl)] at k

/-- Reflexivity: one successor computation, then replacement at the root. -/
theorem reflNf (t : Tm n) : NIPrf Γ (.eq (nf t) (nf t)) := by
  have a := stepOne (Γ := Γ) (Syn.var 0) t
  simp only [Syn.subst_var, Syn.inst_zero] at a
  exact root a a

theorem symmNf {x y : Tm n} (h : NIPrf Γ (.eq (nf x) (nf y))) : NIPrf Γ (.eq (nf y) (nf x)) :=
  root h (reflNf x)

theorem transNf {x y z : Tm n} (h₁ : NIPrf Γ (.eq (nf x) (nf y)))
    (h₂ : NIPrf Γ (.eq (nf y) (nf z))) : NIPrf Γ (.eq (nf x) (nf z)) :=
  root (symmNf h₁) h₂

/-- Transport in one term: Seed at the counter `1`. -/
theorem trOneNf (h : Tm (n + 1)) {s t u : Tm n} (h₁ : NIPrf Γ (.eq (nf s) (nf t)))
    (h₂ : NIPrf Γ (.eq (nf (Syn.subst (inst s) h)) (nf u))) :
    NIPrf Γ (.eq (nf u) (nf (Syn.subst (inst t) h))) := by
  have k := NIPrf.seed (succ zero) h h₁ (transNf (stepOne h s) h₂)
  exact symmNf (root (stepOne h t) k)

/-- From zero-normal hypotheses only zero-normal formulas are derivable. -/
theorem normal (h : NIPrf Γ A) : (∀ B ∈ Γ, fnf B = B) → fnf A = A := by
  induction h with
  | hyp h => exact fun hΓ => hΓ _ h
  | iterSucc c a h => exact fun _ => fnf_idempotent _
  | seed c h _ _ _ ih₂ =>
    intro hΓ
    have e := ih₂ hΓ
    simp only [fnf, NFm.eq.injEq] at e
    simp only [fnf, nf_idempotent, e.2]
  | qE t _ _ _ _ => exact fun _ => fnf_idempotent _
  | @dE _ Γ B A _ _ ih₁ ih₂ =>
    intro hΓ
    have hB : fnf B = B := by
      have e := ih₁ hΓ
      simpa only [fnf, NFm.D.injEq] using e
    have e := ih₂ fun C hC => by
      rcases List.mem_cons.1 hC with rfl | hC
      · simp only [fnf, hB]
      · obtain ⟨C₀, hC₀, rfl⟩ := List.mem_map.1 hC
        rw [fnf_shift, hΓ C₀ hC₀]
    rw [fnf_shift] at e
    have e' := congrArg (fun X : NFm _ => X.subst (inst zero)) e
    simpa only [NFm.subst_inst_shift] using e'
  | dICase B t hB _ _ => exact fun _ => by simp only [fnf, hB]
  | qIInd s₁ s₂ h₁ h₂ _ _ => exact fun _ => by simp only [fnf, h₁, h₂]

end NIPrf

/-- Every kernel derivation becomes a derivation with Seed when its formulas
are normalized. -/
theorem NPrf.toNI (h : NPrf Γ A) : NIPrf (Γ.map fnf) (fnf A) := by
  induction h with
  | hyp h => exact .hyp (List.mem_map_of_mem h)
  | iterZero a h => exact NIPrf.reflNf a
  | iterSucc c a h => exact .iterSucc c a h
  | trOne h _ _ ih₁ ih₂ => exact NIPrf.trOneNf h ih₁ ih₂
  | @qE _ Γ B t _ _ ih₁ ih₂ =>
    have h₂ : NIPrf (Γ.map fnf) (fnf ((fnf B).subst (inst zero))) := by
      rw [fnf_subst_congr (σ' := inst zero) (fnf_idempotent B) (fun _ => rfl)]
      exact ih₂
    have r := NIPrf.qE (nf t) ih₁ h₂
    rw [fnf_subst_congr (fnf_idempotent B) (nf_inst t)] at r
    exact r
  | dE _ _ ih₁ ih₂ =>
    rw [List.map_cons, map_fnf_shift, fnf_shift] at ih₂
    exact .dE ih₁ ih₂
  | @dICase _ _ B t _ ih =>
    refine .dICase (fnf B) (nf t) (fnf_idempotent B) ?_
    rw [List.map_cons, map_fnf_shift, fnf_shift] at ih
    have e : fnf ((fnf B).subst (up (inst (nf t)))) = fnf (B.subst (up (inst t))) :=
      fnf_subst_congr (fnf_idempotent B) (nf_up_congr (nf_inst t))
    rw [fnf_subst_congr (σ' := inst zero) e (fun _ => rfl),
      fnf_subst_congr (σ' := repl (succ (Syn.var 0))) e (fun _ => rfl)]
    exact ih
  | @qIInd _ _ s₁ s₂ _ ih =>
    refine .qIInd (nf s₁) (nf s₂) (nf_idempotent s₁) (nf_idempotent s₂) ?_
    rw [List.map_cons, map_fnf_shift] at ih
    rw [fnf_subst_congr (A' := .eq s₁ s₂) (σ' := repl (succ (Syn.var 0)))
      (by simp only [fnf, nf_idempotent]) (fun _ => rfl)]
    exact ih

/-- **Replacement of an initializer is enough.**  The kernel derives a sequent
exactly when the calculus with Seed derives its zero-normal form. -/
theorem niprf_iff_nprf : NIPrf (Γ.map fnf) (fnf A) ↔ NPrf Γ A :=
  ⟨fun h => (equivFnf A).mpr (h.toNPrf.cut fun B hB => by
      obtain ⟨C, hC, rfl⟩ := List.mem_map.1 hB
      exact (equivFnf C).mp (.hyp hC)), NPrf.toNI⟩

/-- The same calculus proves the zero-normal form of a sequent exactly when
iPRA proves its reading. -/
theorem niprf_iff_pra : NIPrf (Γ.map fnf) (fnf A) ↔ (Γ.map NFm.toPRA ⊢[PRAAx] A.toPRA) :=
  niprf_iff_nprf.trans native_iff_pra

end LeanProofs.ConciseIPRA
