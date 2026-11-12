import ConciseIPRA.NativeZeroNormal

/-!
# Seed evaluation

`NVPrf` is the arithmetic and equality interface of the package
`Research/seed_evaluation`, on the zero-normal syntax of `NativeZeroNormal`:
reflexivity and one rule

  **SeedEval**: from `a = b` and `I(S c, a; u.h) = r` infer
  `r = h[I(c, b; u.h)/u]`,

where every substitution is followed by the contraction `nf`.  The equation
premise is about the seed alone; the previous value `I(c, b; u.h)` is built by
the rule.  With `QE`, `DE`, `D` by cases and `Q` by progress it has seven
rules; there is no computation axiom and no transport rule.

* `nvprf_iff_nprf`: `NPrf Γ A ↔ NVPrf (Γ.map fnf) (fnf A)`;
* `NVPrf.normal`: from zero-normal hypotheses only zero-normal formulas are
  derivable.

At the counter `0` the previous value `I(0, b; u.h)` is `b` by the syntax, so
SeedEval is the rule Step of `NativeZeroStep` at the counter `0`
(`NVPrf.stepZero`), and the pivot and the two-step transport of that module
carry over.  Successor computation is SeedEval on two reflexivities.
-/

namespace LeanProofs.ConciseIPRA

open Syn
open Tm (zero succ iter)
open scoped Fm
open ZeroNormalization

variable {n m : ℕ}

/-- Derivability on zero-normal terms with reflexivity and the rule SeedEval. -/
inductive NVPrf : {n : ℕ} → List (NFm n) → NFm n → Prop
  | hyp {n : ℕ} {Γ : List (NFm n)} {A : NFm n} (h : A ∈ Γ) : NVPrf Γ A
  | refl {n : ℕ} {Γ : List (NFm n)} (t : Tm n) (ht : nf t = t) : NVPrf Γ (.eq t t)
  /-- SeedEval: from `a = b` and `I(S c, a; u.h) = r` infer
  `r = h[I(c, b; u.h)/u]`. -/
  | seed {n : ℕ} {Γ : List (NFm n)} (c : Tm n) (h : Tm (n + 1)) {a b r : Tm n}
      (h₁ : NVPrf Γ (.eq a b)) (h₂ : NVPrf Γ (.eq (nf (iter (succ c) a h)) r)) :
      NVPrf Γ (.eq r (nf (Syn.subst (inst (iter c b h)) h)))
  | qE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 1)} (t : Tm n)
      (h₁ : NVPrf Γ (.Q B)) (h₂ : NVPrf Γ (fnf (B.subst (inst zero)))) :
      NVPrf Γ (fnf (B.subst (inst t)))
  | dE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 2)} {A : NFm n}
      (h₁ : NVPrf Γ (.D B)) (h₂ : NVPrf (.Q B :: Γ.map NFm.shift) A.shift) : NVPrf Γ A
  | dICase {n : ℕ} {Γ : List (NFm n)} (B : NFm (n + 2)) (t : Tm n) (hB : fnf B = B)
      (h : NVPrf ((fnf ((B.subst (up (inst t))).subst (inst zero))).shift :: Γ.map NFm.shift)
        (fnf ((B.subst (up (inst t))).subst (repl (succ (var 0)))))) :
      NVPrf Γ (.D B)
  | qIInd {n : ℕ} {Γ : List (NFm n)} (s₁ s₂ : Tm (n + 1)) (h₁ : nf s₁ = s₁) (h₂ : nf s₂ = s₂)
      (h : NVPrf (NFm.eq s₁ s₂ :: Γ.map NFm.shift)
        (fnf ((NFm.eq s₁ s₂).subst (repl (succ (var 0)))))) :
      NVPrf Γ (.Q (.eq s₁ s₂))

variable {Γ : List (NFm n)} {A : NFm n}

namespace NVPrf

/-- Every rule is a derived rule of the kernel, up to normal forms. -/
theorem toNPrf (h : NVPrf Γ A) : NPrf Γ A := by
  induction h with
  | hyp h => exact .hyp h
  | refl t _ => exact NPrf.eqRefl t
  | @seed _ Γ c h a b r _ _ ih₁ ih₂ =>
    have hc : NPrf Γ (.eq (iter c a h) (iter c b h)) := by
      have k := NPrf.eqCongr
        (iter (Syn.shift c) (Syn.var 0) (Syn.subst (up fun i => Syn.var i.succ) h)) ih₁
      simpa only [Tm.subst_iter, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
        Syn.subst_up_inst_up_shift] using k
    exact NPrf.eqTrans (NPrf.eqSymm ih₂) (NPrf.eqTrans (NPrf.eqSymm (eqNf _))
      (NPrf.eqTrans (.iterSucc c a h) (NPrf.eqTrans (NPrf.eqCongr h hc) (eqNf _))))
  | qE t _ _ ih₁ ih₂ => exact (equivFnf _).mp (.qE t ih₁ ((equivFnf _).mpr ih₂))
  | dE _ _ ih₁ ih₂ => exact .dE ih₁ ih₂
  | dICase B t _ _ ih =>
    exact .dICase B t ((equivFnf _).mpr
      (NPrf.cut1 ((equivFnf _).shift.mp NPrf.hyp0) (NPrf.wkUnder ih)))
  | qIInd s₁ s₂ _ _ _ ih => exact .qIInd s₁ s₂ ((equivFnf _).mpr ih)

theorem reflNf (t : Tm n) : NVPrf Γ (.eq (nf t) (nf t)) := .refl _ (nf_idempotent t)

/-- SeedEval at the counter `0`: from `a = b` and `I(S 0, a; u.h) = r` infer
`r = h[b/u]`. -/
theorem stepZero (h : Tm (n + 1)) {a b r : Tm n} (h₁ : NVPrf Γ (.eq a b))
    (h₂ : NVPrf Γ (.eq (nf (iter (succ zero) a h)) r)) :
    NVPrf Γ (.eq r (nf (Syn.subst (inst b) h))) := by
  have k := NVPrf.seed zero h h₁ h₂
  rwa [nf_subst_congr (t := h) (t' := h) (σ' := inst b) rfl (fun i => by
    refine Fin.cases ?_ (fun j => ?_) i
    · show nf (iter zero b h) = nf b
      simp only [nf_iter, nf_zero, smartI_zero]
    · rfl)] at k

/-- The pivot: from `x = y` and `x = z` infer `z = y`, by two evaluations
through `I(S 0, x; v.v)`. -/
theorem pivot {x y z : Tm n} (h₁ : NVPrf Γ (.eq (nf x) (nf y)))
    (h₂ : NVPrf Γ (.eq (nf x) (nf z))) : NVPrf Γ (.eq (nf z) (nf y)) := by
  have k := stepZero (Syn.var 0) h₂ (reflNf (iter (succ zero) (nf x) (Syn.var 0)))
  have k' := stepZero (Syn.var 0) h₁ (r := nf z)
    (by simpa only [Syn.subst_var, Syn.inst_zero, nf_idempotent] using k)
  simpa only [Syn.subst_var, Syn.inst_zero, nf_idempotent] using k'

theorem symmNf {x y : Tm n} (h : NVPrf Γ (.eq (nf x) (nf y))) : NVPrf Γ (.eq (nf y) (nf x)) :=
  pivot (reflNf x) h

theorem transNf {x y z : Tm n} (h₁ : NVPrf Γ (.eq (nf x) (nf y)))
    (h₂ : NVPrf Γ (.eq (nf y) (nf z))) : NVPrf Γ (.eq (nf x) (nf z)) :=
  pivot h₂ (symmNf h₁)

/-- Successor computation, by SeedEval on two reflexivities. -/
theorem iterSuccNf (c a : Tm n) (h : Tm (n + 1)) :
    NVPrf Γ (fnf (.eq (iter (succ c) a h) (Syn.subst (inst (iter c a h)) h))) := by
  have k := NVPrf.seed (Γ := Γ) c h (reflNf a) (r := nf (iter (succ c) a h))
    (by simpa only [nf_iter, nf_succ, nf_idempotent] using
      reflNf (Γ := Γ) (iter (succ c) a h))
  rw [nf_subst_congr (t := h) (t' := h) (σ' := inst (iter c a h)) rfl (fun i => by
    refine Fin.cases ?_ (fun j => ?_) i
    · show nf (iter c (nf a) h) = nf (iter c a h)
      simp only [nf_iter, nf_idempotent]
    · rfl)] at k
  exact k

/-- Transport in one term, by two evaluations at the counter `0`. -/
theorem trOneNf (h : Tm (n + 1)) {s t u : Tm n} (h₁ : NVPrf Γ (.eq (nf s) (nf t)))
    (h₂ : NVPrf Γ (.eq (nf (Syn.subst (inst s) h)) (nf u))) :
    NVPrf Γ (.eq (nf u) (nf (Syn.subst (inst t) h))) := by
  have k := stepZero h (reflNf (Γ := Γ) s) (reflNf (iter (succ zero) (nf s) h))
  rw [nf_subst_congr (t := h) (t' := h) rfl (nf_inst s)] at k
  have k₃ := stepZero h h₁ (transNf k h₂)
  rw [nf_subst_congr (t := h) (t' := h) rfl (nf_inst t)] at k₃
  exact k₃

/-- From zero-normal hypotheses only zero-normal formulas are derivable. -/
theorem normal (h : NVPrf Γ A) : (∀ B ∈ Γ, fnf B = B) → fnf A = A := by
  induction h with
  | hyp h => exact fun hΓ => hΓ _ h
  | refl t ht => exact fun _ => by simp only [fnf, ht]
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

end NVPrf

/-- Every kernel derivation becomes a derivation with reflexivity and SeedEval
when its formulas are normalized. -/
theorem NPrf.toNV (h : NPrf Γ A) : NVPrf (Γ.map fnf) (fnf A) := by
  induction h with
  | hyp h => exact .hyp (List.mem_map_of_mem h)
  | iterZero a h => exact NVPrf.reflNf a
  | iterSucc c a h => exact NVPrf.iterSuccNf c a h
  | trOne h _ _ ih₁ ih₂ => exact NVPrf.trOneNf h ih₁ ih₂
  | @qE _ Γ B t _ _ ih₁ ih₂ =>
    have h₂ : NVPrf (Γ.map fnf) (fnf ((fnf B).subst (inst zero))) := by
      rw [fnf_subst_congr (σ' := inst zero) (fnf_idempotent B) (fun _ => rfl)]
      exact ih₂
    have r := NVPrf.qE (nf t) ih₁ h₂
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

/-- **Reflexivity and seed evaluation suffice on zero-normal terms.** -/
theorem nvprf_iff_nprf : NVPrf (Γ.map fnf) (fnf A) ↔ NPrf Γ A :=
  ⟨fun h => (equivFnf A).mpr (h.toNPrf.cut fun B hB => by
      obtain ⟨C, hC, rfl⟩ := List.mem_map.1 hB
      exact (equivFnf C).mp (.hyp hC)), NPrf.toNV⟩

/-- The same calculus proves the zero-normal form of a sequent exactly when
iPRA proves its reading. -/
theorem nvprf_iff_pra : NVPrf (Γ.map fnf) (fnf A) ↔ (Γ.map NFm.toPRA ⊢[PRAAx] A.toPRA) :=
  nvprf_iff_nprf.trans native_iff_pra

end LeanProofs.ConciseIPRA
