import ConciseIPRA.NativeZeroNormal

/-!
# One successor step for equality and computation

`NSPrf` is the arithmetic and equality interface of the package
`Research/uniform_step`, on the zero-normal syntax of `NativeZeroNormal`:
reflexivity and one rule

  **Step**: from `I(c, a; u.h) = t` and `I(S c, a; u.h) = r` infer `r = h[t/u]`,

where at `c = 0` the first source is `a` by the syntax, and every substitution
is followed by the contraction `nf`.  With `QE`, `DE`, `D` by cases and `Q` by
progress it has seven rules; there is no computation axiom and no transport
rule.

* `nsprf_iff_nprf`: `NPrf Γ A ↔ NSPrf (Γ.map fnf) (fnf A)`;
* `NSPrf.normal`: from zero-normal hypotheses only zero-normal formulas are
  derivable.

The pivot of the report recovers equality: for `K = I(S 0, x; v.v)`, Step on
`x = z` and `K = K` gives `K = z`, and Step on `x = y` and `K = z` gives
`z = y` (`NSPrf.pivot`).  Transport in a template `h` along `s = t` is two
Steps at the counter `0` and seed `s` (`NSPrf.trOneNf`).  No induction is used.
-/

namespace LeanProofs.ConciseIPRA

open Syn
open Tm (zero succ iter)
open scoped Fm
open ZeroNormalization

variable {n m : ℕ}

/-- Derivability on zero-normal terms with reflexivity and the rule Step. -/
inductive NSPrf : {n : ℕ} → List (NFm n) → NFm n → Prop
  | hyp {n : ℕ} {Γ : List (NFm n)} {A : NFm n} (h : A ∈ Γ) : NSPrf Γ A
  | refl {n : ℕ} {Γ : List (NFm n)} (t : Tm n) (ht : nf t = t) : NSPrf Γ (.eq t t)
  /-- Step: from `I(c, a; u.h) = t` and `I(S c, a; u.h) = r` infer
  `r = h[t/u]`. -/
  | step {n : ℕ} {Γ : List (NFm n)} (c a : Tm n) (h : Tm (n + 1)) {t r : Tm n}
      (h₁ : NSPrf Γ (.eq (nf (iter c a h)) t))
      (h₂ : NSPrf Γ (.eq (nf (iter (succ c) a h)) r)) :
      NSPrf Γ (.eq r (nf (Syn.subst (inst t) h)))
  | qE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 1)} (t : Tm n)
      (h₁ : NSPrf Γ (.Q B)) (h₂ : NSPrf Γ (fnf (B.subst (inst zero)))) :
      NSPrf Γ (fnf (B.subst (inst t)))
  | dE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 2)} {A : NFm n}
      (h₁ : NSPrf Γ (.D B)) (h₂ : NSPrf (.Q B :: Γ.map NFm.shift) A.shift) : NSPrf Γ A
  | dICase {n : ℕ} {Γ : List (NFm n)} (B : NFm (n + 2)) (t : Tm n) (hB : fnf B = B)
      (h : NSPrf ((fnf ((B.subst (up (inst t))).subst (inst zero))).shift :: Γ.map NFm.shift)
        (fnf ((B.subst (up (inst t))).subst (repl (succ (var 0)))))) :
      NSPrf Γ (.D B)
  | qIInd {n : ℕ} {Γ : List (NFm n)} (s₁ s₂ : Tm (n + 1)) (h₁ : nf s₁ = s₁) (h₂ : nf s₂ = s₂)
      (h : NSPrf (NFm.eq s₁ s₂ :: Γ.map NFm.shift)
        (fnf ((NFm.eq s₁ s₂).subst (repl (succ (var 0)))))) :
      NSPrf Γ (.Q (.eq s₁ s₂))

variable {Γ : List (NFm n)} {A : NFm n}

namespace NSPrf

/-- Every rule is a derived rule of the kernel, up to normal forms. -/
theorem toNPrf (h : NSPrf Γ A) : NPrf Γ A := by
  induction h with
  | hyp h => exact .hyp h
  | refl t _ => exact NPrf.eqRefl t
  | step c a h _ _ ih₁ ih₂ =>
    exact NPrf.eqTrans (NPrf.eqSymm ih₂) (NPrf.eqTrans (NPrf.eqSymm (eqNf _))
      (NPrf.eqTrans (.iterSucc c a h) (NPrf.eqTrans (NPrf.eqCongr h (eqNf (iter c a h)))
        (NPrf.eqTrans (NPrf.eqCongr h ih₁) (eqNf _)))))
  | qE t _ _ ih₁ ih₂ => exact (equivFnf _).mp (.qE t ih₁ ((equivFnf _).mpr ih₂))
  | dE _ _ ih₁ ih₂ => exact .dE ih₁ ih₂
  | dICase B t _ _ ih =>
    exact .dICase B t ((equivFnf _).mpr
      (NPrf.cut1 ((equivFnf _).shift.mp NPrf.hyp0) (NPrf.wkUnder ih)))
  | qIInd s₁ s₂ _ _ _ ih => exact .qIInd s₁ s₂ ((equivFnf _).mpr ih)

theorem reflNf (t : Tm n) : NSPrf Γ (.eq (nf t) (nf t)) := .refl _ (nf_idempotent t)

/-- The pivot: from `x = y` and `x = z` infer `z = y`, by two Steps through
`I(S 0, x; v.v)`. -/
theorem pivot {x y z : Tm n} (h₁ : NSPrf Γ (.eq (nf x) (nf y)))
    (h₂ : NSPrf Γ (.eq (nf x) (nf z))) : NSPrf Γ (.eq (nf z) (nf y)) := by
  have k := NSPrf.step (Γ := Γ) zero (nf x) (Syn.var 0) (t := nf z)
    (by simpa only [nf_iter, nf_zero, smartI_zero, nf_idempotent] using h₂)
    (reflNf (iter (succ zero) (nf x) (Syn.var 0)))
  have k' := NSPrf.step (Γ := Γ) zero (nf x) (Syn.var 0) (t := nf y) (r := nf z)
    (by simpa only [nf_iter, nf_zero, smartI_zero, nf_idempotent] using h₁)
    (by simpa only [Syn.subst_var, Syn.inst_zero, nf_idempotent] using k)
  simpa only [Syn.subst_var, Syn.inst_zero, nf_idempotent] using k'

theorem symmNf {x y : Tm n} (h : NSPrf Γ (.eq (nf x) (nf y))) : NSPrf Γ (.eq (nf y) (nf x)) :=
  pivot (reflNf x) h

theorem transNf {x y z : Tm n} (h₁ : NSPrf Γ (.eq (nf x) (nf y)))
    (h₂ : NSPrf Γ (.eq (nf y) (nf z))) : NSPrf Γ (.eq (nf x) (nf z)) :=
  pivot h₂ (symmNf h₁)

/-- Successor computation, by Step on two reflexivities. -/
theorem iterSuccNf (c a : Tm n) (h : Tm (n + 1)) :
    NSPrf Γ (fnf (.eq (iter (succ c) a h) (Syn.subst (inst (iter c a h)) h))) := by
  have k := NSPrf.step (Γ := Γ) c a h (reflNf (iter c a h)) (reflNf (iter (succ c) a h))
  rw [nf_subst_congr (t := h) (t' := h) rfl (nf_inst (iter c a h))] at k
  exact k

/-- Transport in one term, by two Steps at the counter `0`. -/
theorem trOneNf (h : Tm (n + 1)) {s t u : Tm n} (h₁ : NSPrf Γ (.eq (nf s) (nf t)))
    (h₂ : NSPrf Γ (.eq (nf (Syn.subst (inst s) h)) (nf u))) :
    NSPrf Γ (.eq (nf u) (nf (Syn.subst (inst t) h))) := by
  have k := NSPrf.step (Γ := Γ) zero (nf s) h (t := nf s)
    (by simpa only [nf_iter, nf_zero, smartI_zero, nf_idempotent] using reflNf (Γ := Γ) s)
    (reflNf (iter (succ zero) (nf s) h))
  rw [nf_subst_congr (t := h) (t' := h) rfl (nf_inst s)] at k
  have k₃ := NSPrf.step (Γ := Γ) zero (nf s) h (t := nf t)
    (by simpa only [nf_iter, nf_zero, smartI_zero, nf_idempotent] using h₁) (transNf k h₂)
  rw [nf_subst_congr (t := h) (t' := h) rfl (nf_inst t)] at k₃
  exact k₃

/-- From zero-normal hypotheses only zero-normal formulas are derivable. -/
theorem normal (h : NSPrf Γ A) : (∀ B ∈ Γ, fnf B = B) → fnf A = A := by
  induction h with
  | hyp h => exact fun hΓ => hΓ _ h
  | refl t ht => exact fun _ => by simp only [fnf, ht]
  | step c a h _ _ _ ih₂ =>
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

end NSPrf

/-- Every kernel derivation becomes a derivation with reflexivity and Step when
its formulas are normalized. -/
theorem NPrf.toNS (h : NPrf Γ A) : NSPrf (Γ.map fnf) (fnf A) := by
  induction h with
  | hyp h => exact .hyp (List.mem_map_of_mem h)
  | iterZero a h => exact NSPrf.reflNf a
  | iterSucc c a h => exact NSPrf.iterSuccNf c a h
  | trOne h _ _ ih₁ ih₂ => exact NSPrf.trOneNf h ih₁ ih₂
  | @qE _ Γ B t _ _ ih₁ ih₂ =>
    have h₂ : NSPrf (Γ.map fnf) (fnf ((fnf B).subst (inst zero))) := by
      rw [fnf_subst_congr (σ' := inst zero) (fnf_idempotent B) (fun _ => rfl)]
      exact ih₂
    have r := NSPrf.qE (nf t) ih₁ h₂
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

/-- **Reflexivity and one successor step suffice on zero-normal terms.** -/
theorem nsprf_iff_nprf : NSPrf (Γ.map fnf) (fnf A) ↔ NPrf Γ A :=
  ⟨fun h => (equivFnf A).mpr (h.toNPrf.cut fun B hB => by
      obtain ⟨C, hC, rfl⟩ := List.mem_map.1 hB
      exact (equivFnf C).mp (.hyp hC)), NPrf.toNS⟩

/-- The same calculus proves the zero-normal form of a sequent exactly when
iPRA proves its reading. -/
theorem nsprf_iff_pra : NSPrf (Γ.map fnf) (fnf A) ↔ (Γ.map NFm.toPRA ⊢[PRAAx] A.toPRA) :=
  nsprf_iff_nprf.trans native_iff_pra

end LeanProofs.ConciseIPRA
