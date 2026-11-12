import ConciseIPRA.ZeroNormalization

/-!
# One computation rule: the kernel on zero-normal terms

The zero computation `I(0, a; u.h) = a` can be moved from the proof rules into
the syntax.  A term is *zero-normal* if no iterator in it has the literal `0`
as its counter; `nf` contracts every such iterator, and substitution followed
by `nf` is substitution inside the zero-normal terms (`ZeroNormalization`,
delivered in the package `Research/zero_normal`).

`NZPrf` is the kernel `NPrf` without the rule `iterZero`, with every
substitution of a rule replaced by its normalizing form.  It has seven rules:
hypothesis, successor computation, transport in one term, `QE`, `DE`, `D` by
cases and `Q` by progress.

* `NZPrf.normal`: from zero-normal hypotheses it derives zero-normal formulas
  only, so it is a calculus on the zero-normal syntax;
* `nzprf_iff_nprf`: `NPrf Γ A ↔ NZPrf (Γ.map fnf) (fnf A)`, where `fnf`
  normalizes the terms of a formula.  In particular the two calculi derive the
  same zero-normal sequents (`nzprf_iff_nprf_of_normal`);
* `nzprf_iff_pra`: the bi-interpretation with iPRA transfers.

Reflexivity, which the kernel obtains from the zero computation, comes from
successor computation: `I(S 0, t; u.u) = t` is an instance of it on normal
terms, because the right-hand side `I(0, t; u.u)` is contracted to `t`.
-/

namespace LeanProofs.ConciseIPRA

open Syn
open Tm (zero succ iter)
open scoped Fm

variable {n m : ℕ}

namespace ZeroNormalization

@[simp] theorem nf_var (i : Fin n) : nf (Syn.var i : Tm n) = Syn.var i := rfl
@[simp] theorem nf_zero : nf (zero : Tm n) = zero := rfl
@[simp] theorem nf_succ (t : Tm n) : nf (succ t) = succ (nf t) := rfl
@[simp] theorem nf_iter (c a : Tm n) (h : Tm (n + 1)) :
    nf (iter c a h) = smartI (nf c) (nf a) (nf h) := rfl
@[simp] theorem smartI_succ (c a : Tm n) (h : Tm (n + 1)) :
    smartI (succ c) a h = iter (succ c) a h := rfl

/-- The normal form of a substitution instance depends only on normal forms. -/
theorem nf_subst_congr {t t' : Tm n} {σ σ' : Fin n → Tm m} (ht : nf t = nf t')
    (hσ : ∀ i, nf (σ i) = nf (σ' i)) : nf (Syn.subst σ t) = nf (Syn.subst σ' t') := by
  rw [← nf_subst t σ, ← nf_subst t' σ', ht, funext hσ]

theorem fnf_subst_congr {A A' : NFm n} {σ σ' : Fin n → Tm m} (hA : fnf A = fnf A')
    (hσ : ∀ i, nf (σ i) = nf (σ' i)) : fnf (A.subst σ) = fnf (A'.subst σ') := by
  rw [← fnf_subst A σ, ← fnf_subst A' σ', hA, funext hσ]

theorem nf_inst (t : Tm n) (i : Fin (n + 1)) : nf (inst (nf t) i) = nf (inst t i) := by
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

theorem nf_up_congr {σ σ' : Fin n → Tm m} (h : ∀ i, nf (σ i) = nf (σ' i))
    (i : Fin (n + 1)) : nf (up σ i) = nf (up σ' i) :=
  (congrFun (nf_up σ) i).trans (by rw [funext h]; exact (congrFun (nf_up σ') i).symm)

theorem up_ren (ξ : Fin n → Fin m) :
    up (fun i => (Syn.var (ξ i) : Tm m)) = fun i => Syn.var (Tm.upRen ξ i) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

theorem nf_subst_var (t : Tm n) (ξ : Fin n → Fin m) :
    nf (Syn.subst (fun i => (Syn.var (ξ i) : Tm m)) t)
      = Syn.subst (fun i => (Syn.var (ξ i) : Tm m)) (nf t) := by
  show nf (Tm.sub (fun i => Tm.var (ξ i)) t) = Tm.sub (fun i => Tm.var (ξ i)) (nf t)
  rw [← Tm.ren_eq_sub, ← Tm.ren_eq_sub, nf_ren]

/-- Normalization of a formula commutes with renaming. -/
theorem fnf_ren (A : NFm n) : ∀ {m : ℕ} (ξ : Fin n → Fin m),
    fnf (A.subst fun i => (Syn.var (ξ i) : Tm m))
      = (fnf A).subst fun i => (Syn.var (ξ i) : Tm m) := by
  induction A with
  | eq s t => intro m ξ; simp only [NFm.subst_eq, fnf, nf_subst_var]
  | Q B ih => intro m ξ; simp only [NFm.subst_Q, fnf, up_ren, ih]
  | D B ih => intro m ξ; simp only [NFm.subst_D, fnf, up_ren, ih]

theorem fnf_shift (A : NFm n) : fnf A.shift = (fnf A).shift := fnf_ren A Fin.succ

theorem map_fnf_shift (Γ : List (NFm n)) :
    (Γ.map NFm.shift).map fnf = (Γ.map fnf).map NFm.shift := by
  rw [List.map_map, List.map_map]
  exact List.map_congr_left fun A _ => fnf_shift A

/-- A formula and its normal form are interderivable in the kernel. -/
theorem equivFnf (A : NFm n) : NEquiv A (fnf A) := fnf_native_roundTrip A

/-- A term is provably equal to its normal form in the kernel. -/
theorem eqNf {Γ : List (NFm n)} (t : Tm n) : NPrf Γ (.eq t (nf t)) :=
  NPrf.iff_teq.mpr (nf_correct t).ofNil

end ZeroNormalization

open ZeroNormalization

/-- Derivability in the kernel without the zero computation rule, on
zero-normal terms: every substitution of a rule is followed by `nf`. -/
inductive NZPrf : {n : ℕ} → List (NFm n) → NFm n → Prop
  | hyp {n : ℕ} {Γ : List (NFm n)} {A : NFm n} (h : A ∈ Γ) : NZPrf Γ A
  /-- `I(S c, a; u.h) = h[I(c, a; u.h)/u]`, the only computation rule. -/
  | iterSucc {n : ℕ} {Γ : List (NFm n)} (c a : Tm n) (h : Tm (n + 1)) :
      NZPrf Γ (fnf (.eq (iter (succ c) a h) (Syn.subst (inst (iter c a h)) h)))
  | trOne {n : ℕ} {Γ : List (NFm n)} (h : Tm (n + 1)) {s t u : Tm n}
      (h₁ : NZPrf Γ (.eq s t)) (h₂ : NZPrf Γ (.eq (nf (Syn.subst (inst s) h)) u)) :
      NZPrf Γ (.eq u (nf (Syn.subst (inst t) h)))
  | qE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 1)} (t : Tm n)
      (h₁ : NZPrf Γ (.Q B)) (h₂ : NZPrf Γ (fnf (B.subst (inst zero)))) :
      NZPrf Γ (fnf (B.subst (inst t)))
  | dE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 2)} {A : NFm n}
      (h₁ : NZPrf Γ (.D B)) (h₂ : NZPrf (.Q B :: Γ.map NFm.shift) A.shift) : NZPrf Γ A
  | dICase {n : ℕ} {Γ : List (NFm n)} (B : NFm (n + 2)) (t : Tm n) (hB : fnf B = B)
      (h : NZPrf ((fnf ((B.subst (up (inst t))).subst (inst zero))).shift :: Γ.map NFm.shift)
        (fnf ((B.subst (up (inst t))).subst (repl (succ (var 0)))))) :
      NZPrf Γ (.D B)
  | qIInd {n : ℕ} {Γ : List (NFm n)} (s₁ s₂ : Tm (n + 1)) (h₁ : nf s₁ = s₁) (h₂ : nf s₂ = s₂)
      (h : NZPrf (NFm.eq s₁ s₂ :: Γ.map NFm.shift)
        (fnf ((NFm.eq s₁ s₂).subst (repl (succ (var 0)))))) :
      NZPrf Γ (.Q (.eq s₁ s₂))

variable {Γ : List (NFm n)} {A : NFm n}

namespace NZPrf

/-- Every rule is a derived rule of the kernel, up to normal forms. -/
theorem toNPrf (h : NZPrf Γ A) : NPrf Γ A := by
  induction h with
  | hyp h => exact .hyp h
  | iterSucc c a h => exact (equivFnf _).mp (.iterSucc c a h)
  | trOne h _ _ ih₁ ih₂ =>
    exact NPrf.eqTrans (.trOne h ih₁ (NPrf.eqTrans (eqNf _) ih₂)) (eqNf _)
  | qE t _ _ ih₁ ih₂ => exact (equivFnf _).mp (.qE t ih₁ ((equivFnf _).mpr ih₂))
  | dE _ _ ih₁ ih₂ => exact .dE ih₁ ih₂
  | dICase B t _ _ ih =>
    exact .dICase B t ((equivFnf _).mpr
      (NPrf.cut1 ((equivFnf _).shift.mp NPrf.hyp0) (NPrf.wkUnder ih)))
  | qIInd s₁ s₂ _ _ _ ih => exact .qIInd s₁ s₂ ((equivFnf _).mpr ih)

/-- Reflexivity at a normal form, from successor computation. -/
theorem reflNf (t : Tm n) : NZPrf Γ (.eq (nf t) (nf t)) := by
  have e := NZPrf.iterSucc (Γ := Γ) zero (nf t) (Syn.var 0)
  simp only [fnf, nf_iter, nf_succ, nf_zero, nf_var, smartI_succ, smartI_zero, nf_idempotent,
    Syn.subst_var, Syn.inst_zero] at e
  have r := NZPrf.trOne (Syn.var 0) (u := nf t) e (by
    simpa only [nf_iter, nf_succ, nf_zero, nf_var, smartI_succ, nf_idempotent, Syn.subst_var,
      Syn.inst_zero] using e)
  simpa only [Syn.subst_var, Syn.inst_zero, nf_idempotent] using r

/-- From zero-normal hypotheses only zero-normal formulas are derivable. -/
theorem normal (h : NZPrf Γ A) : (∀ B ∈ Γ, fnf B = B) → fnf A = A := by
  induction h with
  | hyp h => exact fun hΓ => hΓ _ h
  | iterSucc c a h => exact fun _ => fnf_idempotent _
  | trOne h _ _ _ ih₂ =>
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

end NZPrf

/-- Every kernel derivation becomes a derivation without the zero computation
rule when its formulas are normalized. -/
theorem NPrf.toNZ (h : NPrf Γ A) : NZPrf (Γ.map fnf) (fnf A) := by
  induction h with
  | hyp h => exact .hyp (List.mem_map_of_mem h)
  | iterZero a h => exact NZPrf.reflNf a
  | iterSucc c a h => exact .iterSucc c a h
  | @trOne _ Γ h s t u _ _ ih₁ ih₂ =>
    have h₂ : NZPrf (Γ.map fnf) (.eq (nf (Syn.subst (inst (nf s)) (nf h))) (nf u)) := by
      rw [nf_subst_congr (nf_idempotent h) (nf_inst s)]
      exact ih₂
    have r := NZPrf.trOne (nf h) ih₁ h₂
    rw [nf_subst_congr (nf_idempotent h) (nf_inst t)] at r
    exact r
  | @qE _ Γ B t _ _ ih₁ ih₂ =>
    have h₂ : NZPrf (Γ.map fnf) (fnf ((fnf B).subst (inst zero))) := by
      rw [fnf_subst_congr (σ' := inst zero) (fnf_idempotent B) (fun _ => rfl)]
      exact ih₂
    have r := NZPrf.qE (nf t) ih₁ h₂
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

/-- **The zero computation rule can be moved into the syntax.**  The kernel
derives a sequent exactly when the calculus without that rule derives its
zero-normal form. -/
theorem nzprf_iff_nprf : NZPrf (Γ.map fnf) (fnf A) ↔ NPrf Γ A :=
  ⟨fun h => (equivFnf A).mpr (h.toNPrf.cut fun B hB => by
      obtain ⟨C, hC, rfl⟩ := List.mem_map.1 hB
      exact (equivFnf C).mp (.hyp hC)), NPrf.toNZ⟩

/-- On zero-normal sequents the two calculi derive the same. -/
theorem nzprf_iff_nprf_of_normal (hΓ : ∀ B ∈ Γ, fnf B = B) (hA : fnf A = A) :
    NZPrf Γ A ↔ NPrf Γ A := by
  have e : Γ.map fnf = Γ := by
    rw [List.map_congr_left hΓ, List.map_id']
  rw [← nzprf_iff_nprf, e, hA]

/-- The calculus without the zero computation rule proves the zero-normal form
of a sequent exactly when iPRA proves its reading. -/
theorem nzprf_iff_pra : NZPrf (Γ.map fnf) (fnf A) ↔ (Γ.map NFm.toPRA ⊢[PRAAx] A.toPRA) :=
  nzprf_iff_nprf.trans native_iff_pra

end LeanProofs.ConciseIPRA
