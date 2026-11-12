import ConciseIPRA.NativeOneIntro
import ConciseIPRA.NativeZeroNormal

/-!
# One evaluation rule on zero-normal terms

`ZEPrf` is the companion calculus `Z₁` of the package
`Research/equality_from_iteration`, on the zero-normal syntax of
`NativeZeroNormal`.  It has six rules: hypothesis, reflexivity, `QE`, `DE`,
the single introduction whose mode is chosen by the literal test of
`NativeOneIntro` (`NFm.start`), and one rule for arithmetic and equality,

  **UE**: from `I(c, a; u.h) = t` and `I(S c, a; u.h) = r` infer `r = h[t/u]`,

where every term is normalized after substitution.  At the counter `0` the
first premise reads `a = t`, because `I(0, a; u.h)` is `a` by the syntax.
There is no zero case, no computation axiom and no transport rule.

* `zeprf_iff_nprf`: `ZEPrf (Γ.map fnf) (fnf A) ↔ NPrf Γ A`;
* `ZEPrf.normal`: from zero-normal hypotheses only zero-normal formulas are
  derivable.

The equality rules are obtained as in the package: the pivot through the
frame `I(S 0, s; u.u)`, successor computation from two reflexivities, and
transport in a template `h` through `I(S 0, s; u.h)`.

The introduction by cases of an equation at the witness `0` is not an
instance of the single introduction, which is progressive there.  It is
derived as in `NativeOneIntro`, with the zero-normal term `I(S 0, 0; u.0)` in
place of `I(0, 0; u.0)` as the alias of `0`.  The derivation uses no
weakening and no cut.
-/

namespace LeanProofs.ConciseIPRA

open Syn
open Tm (zero succ iter)
open scoped Fm
open ZeroNormalization

variable {n m : ℕ}

/-- Derivability on zero-normal terms with reflexivity, the rule UE and the
single introduction. -/
inductive ZEPrf : {n : ℕ} → List (NFm n) → NFm n → Prop
  | hyp {n : ℕ} {Γ : List (NFm n)} {A : NFm n} (h : A ∈ Γ) : ZEPrf Γ A
  | refl {n : ℕ} {Γ : List (NFm n)} (t : Tm n) (ht : nf t = t) : ZEPrf Γ (.eq t t)
  /-- UE: from `I(c, a; u.h) = t` and `I(S c, a; u.h) = r` infer `r = h[t/u]`. -/
  | ue {n : ℕ} {Γ : List (NFm n)} (c a : Tm n) (h : Tm (n + 1)) {t r : Tm n}
      (h₁ : ZEPrf Γ (.eq (nf (iter c a h)) t))
      (h₂ : ZEPrf Γ (.eq (nf (iter (succ c) a h)) r)) :
      ZEPrf Γ (.eq r (nf (Syn.subst (inst t) h)))
  | qE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 1)} (t : Tm n)
      (h₁ : ZEPrf Γ (.Q B)) (h₂ : ZEPrf Γ (fnf (B.subst (inst zero)))) :
      ZEPrf Γ (fnf (B.subst (inst t)))
  | dE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 2)} {A : NFm n}
      (h₁ : ZEPrf Γ (.D B)) (h₂ : ZEPrf (.Q B :: Γ.map NFm.shift) A.shift) : ZEPrf Γ A
  /-- DI: from `B(t, η) ⊢ B(t, S z)` infer `D_{x,y} B`, where `η = z` for a
  literal equation at the literal witness `0` and `η = 0` otherwise. -/
  | dI {n : ℕ} {Γ : List (NFm n)} (B : NFm (n + 2)) (t : Tm n) (hB : fnf B = B)
      (ht : nf t = t)
      (h : ZEPrf (fnf ((B.subst (up (inst t))).subst (repl (NFm.start B t)))
          :: Γ.map NFm.shift)
        (fnf ((B.subst (up (inst t))).subst (repl (succ (var 0)))))) :
      ZEPrf Γ (.D B)

variable {Γ : List (NFm n)} {A : NFm n}

namespace ZEPrf

/-- Every rule is a derived rule of the kernel, up to normal forms. -/
theorem toNPrf (h : ZEPrf Γ A) : NPrf Γ A := by
  induction h with
  | hyp h => exact .hyp h
  | refl t _ => exact NPrf.eqRefl t
  | ue c a h _ _ ih₁ ih₂ =>
    exact NPrf.eqTrans (NPrf.eqSymm ih₂) (NPrf.eqTrans (NPrf.eqSymm (eqNf _))
      (NPrf.eqTrans (.iterSucc c a h)
        (NPrf.eqTrans (NPrf.eqCongr h (NPrf.eqTrans (eqNf _) ih₁)) (eqNf _))))
  | qE t _ _ ih₁ ih₂ => exact (equivFnf _).mp (.qE t ih₁ ((equivFnf _).mpr ih₂))
  | dE _ _ ih₁ ih₂ => exact .dE ih₁ ih₂
  | dI B t _ _ _ ih =>
    exact NPrf.ofDI B t ((equivFnf _).mpr
      (NPrf.cut1 ((equivFnf _).mp NPrf.hyp0) (NPrf.wkUnder ih)))

theorem reflNf (t : Tm n) : ZEPrf Γ (.eq (nf t) (nf t)) := .refl _ (nf_idempotent t)

/-- UE at the counter `0`: from `a = b` and `I(S 0, a; u.h) = r` infer
`r = h[b/u]`. -/
theorem stepZero (h : Tm (n + 1)) {a b r : Tm n} (h₁ : ZEPrf Γ (.eq (nf a) b))
    (h₂ : ZEPrf Γ (.eq (nf (iter (succ zero) a h)) r)) :
    ZEPrf Γ (.eq r (nf (Syn.subst (inst b) h))) :=
  .ue zero a h (by simpa only [nf_iter, nf_zero, smartI_zero] using h₁) h₂

/-- The pivot: from `x = y` and `x = z` infer `z = y`, by two evaluations
through `I(S 0, x; v.v)`. -/
theorem pivot {x y z : Tm n} (h₁ : ZEPrf Γ (.eq (nf x) (nf y)))
    (h₂ : ZEPrf Γ (.eq (nf x) (nf z))) : ZEPrf Γ (.eq (nf z) (nf y)) := by
  have k := stepZero (a := x) (Syn.var 0) h₂ (reflNf (iter (succ zero) x (Syn.var 0)))
  have k' := stepZero (a := x) (Syn.var 0) h₁ (r := nf z)
    (by simpa only [Syn.subst_var, Syn.inst_zero, nf_idempotent] using k)
  simpa only [Syn.subst_var, Syn.inst_zero, nf_idempotent] using k'

theorem symmNf {x y : Tm n} (h : ZEPrf Γ (.eq (nf x) (nf y))) : ZEPrf Γ (.eq (nf y) (nf x)) :=
  pivot (reflNf x) h

theorem transNf {x y z : Tm n} (h₁ : ZEPrf Γ (.eq (nf x) (nf y)))
    (h₂ : ZEPrf Γ (.eq (nf y) (nf z))) : ZEPrf Γ (.eq (nf x) (nf z)) :=
  pivot h₂ (symmNf h₁)

/-- Successor computation, by UE on two reflexivities. -/
theorem iterSuccNf (c a : Tm n) (h : Tm (n + 1)) :
    ZEPrf Γ (fnf (.eq (iter (succ c) a h) (Syn.subst (inst (iter c a h)) h))) := by
  have k := ZEPrf.ue (Γ := Γ) c a h (reflNf (iter c a h)) (reflNf (iter (succ c) a h))
  rw [nf_subst_congr (t := h) (t' := h) rfl (nf_inst (iter c a h))] at k
  exact k

/-- Transport in one term, by two evaluations at the counter `0`. -/
theorem trOneNf (h : Tm (n + 1)) {s t u : Tm n} (h₁ : ZEPrf Γ (.eq (nf s) (nf t)))
    (h₂ : ZEPrf Γ (.eq (nf (Syn.subst (inst s) h)) (nf u))) :
    ZEPrf Γ (.eq (nf u) (nf (Syn.subst (inst t) h))) := by
  have k := stepZero (a := s) h (reflNf (Γ := Γ) s) (reflNf (iter (succ zero) s h))
  rw [nf_subst_congr (t := h) (t' := h) rfl (nf_inst s)] at k
  have k₃ := stepZero (a := s) h h₁ (transNf k h₂)
  rw [nf_subst_congr (t := h) (t' := h) rfl (nf_inst t)] at k₃
  exact k₃

/-- From zero-normal hypotheses only zero-normal formulas are derivable. -/
theorem normal (h : ZEPrf Γ A) : (∀ B ∈ Γ, fnf B = B) → fnf A = A := by
  induction h with
  | hyp h => exact fun hΓ => hΓ _ h
  | refl t ht => exact fun _ => by simp only [fnf, ht]
  | ue c a h _ _ _ ih₂ =>
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
  | dI B t hB _ _ _ => exact fun _ => by simp only [fnf, hB]

end ZEPrf

/-- Derivability of the zero-normal form of a sequent.  The rules below are
stated for it with ordinary substitution, so that the derivations of
`NativeOneIntro` can be repeated. -/
abbrev ZN (Γ : List (NFm n)) (A : NFm n) : Prop := ZEPrf (Γ.map fnf) (fnf A)

namespace ZN

theorem hyp (h : A ∈ Γ) : ZN Γ A := ZEPrf.hyp (List.mem_map_of_mem h)

theorem eqSymm {s t : Tm n} (h : ZN Γ (.eq s t)) : ZN Γ (.eq t s) := ZEPrf.symmNf h

/-- Transport in an equation template, by two transports in one term. -/
theorem trEq (a b : Tm (n + 1)) {s t : Tm n} (h₁ : ZN Γ (.eq s t))
    (h₂ : ZN Γ (.eq (Syn.subst (inst s) a) (Syn.subst (inst s) b))) :
    ZN Γ (.eq (Syn.subst (inst t) a) (Syn.subst (inst t) b)) :=
  ZEPrf.trOneNf b h₁ (ZEPrf.trOneNf a h₁ h₂)

theorem trE {a b : Tm (n + 1)} (H : NFm (n + 1)) (hH : H = .eq a b) {s t : Tm n}
    {A A' : NFm n} (h₁ : ZN Γ (.eq s t)) (hA : H.subst (inst s) = A)
    (hA' : H.subst (inst t) = A') (h₂ : ZN Γ A) : ZN Γ A' := by
  subst hH hA hA'
  exact trEq a b h₁ h₂

theorem qE {B : NFm (n + 1)} (t : Tm n) (h₁ : ZN Γ (.Q B)) (h₂ : ZN Γ (B.subst (inst zero))) :
    ZN Γ (B.subst (inst t)) := by
  have h₂' : ZEPrf (Γ.map fnf) (fnf ((fnf B).subst (inst zero))) := by
    rw [fnf_subst_congr (σ' := inst zero) (fnf_idempotent B) (fun _ => rfl)]
    exact h₂
  have r := ZEPrf.qE (nf t) h₁ h₂'
  rw [fnf_subst_congr (fnf_idempotent B) (nf_inst t)] at r
  exact r

theorem dE {B : NFm (n + 2)} (h₁ : ZN Γ (.D B)) (h₂ : ZN (.Q B :: Γ.map NFm.shift) A.shift) :
    ZN Γ A := by
  have h : ZEPrf ((NFm.Q B :: Γ.map NFm.shift).map fnf) (fnf A.shift) := h₂
  rw [List.map_cons, map_fnf_shift, fnf_shift] at h
  exact ZEPrf.dE h₁ h

/-- The single introduction, at a witness whose normal form passes the same
literal test. -/
theorem dI (B : NFm (n + 2)) (t : Tm n) (hs : NFm.start (fnf B) (nf t) = NFm.start B t)
    (h : ZN ((B.subst (up (inst t))).subst (repl (NFm.start B t)) :: Γ.map NFm.shift)
      ((B.subst (up (inst t))).subst (repl (succ (Syn.var 0))))) : ZN Γ (.D B) := by
  have h' : ZEPrf (((B.subst (up (inst t))).subst (repl (NFm.start B t))
      :: Γ.map NFm.shift).map fnf)
      (fnf ((B.subst (up (inst t))).subst (repl (succ (Syn.var 0))))) := h
  rw [List.map_cons, map_fnf_shift] at h'
  have e : fnf ((fnf B).subst (up (inst (nf t)))) = fnf (B.subst (up (inst t))) :=
    fnf_subst_congr (fnf_idempotent B) (nf_up_congr (nf_inst t))
  refine ZEPrf.dI (fnf B) (nf t) (fnf_idempotent B) (nf_idempotent t) ?_
  rw [hs, fnf_subst_congr (σ' := repl (NFm.start B t)) e (fun _ => rfl),
    fnf_subst_congr (σ' := repl (succ (Syn.var 0))) e (fun _ => rfl)]
  exact h'

/-- The alias `I(S 0, 0; u.0)` of zero passes the literal test as a term that
is not `0`, before and after normalization. -/
theorem start_alias (B : NFm (n + 2)) :
    NFm.start (fnf B) (nf (iter (succ zero) zero zero : Tm n))
      = NFm.start B (iter (succ zero) zero zero) := by
  show NFm.start (fnf B) (iter (succ zero) zero zero) = _
  rw [NFm.start_iter, NFm.start_iter]

/-- The alias is provably zero. -/
theorem aliasEq : ZN Γ (.eq (iter (succ zero) zero zero) zero) :=
  ZEPrf.iterSuccNf zero zero zero

/-- `Q` by progress: the introduction at a dummy witness coordinate and the
witness `0`, followed by `dE`. -/
theorem qInd (s t : Tm (n + 1))
    (h : ZN (NFm.eq s t :: Γ.map NFm.shift) ((NFm.eq s t).subst (repl (succ (Syn.var 0))))) :
    ZN Γ (.Q (.eq s t)) := by
  have hD : ZN Γ (.D ((NFm.eq s t).subst (up (fun i => Syn.var i.succ)))) := by
    refine dI _ zero rfl ?_
    rw [show (NFm.eq s t).subst (up (fun i => Syn.var i.succ))
        = .eq (Syn.subst (up (fun i => Syn.var i.succ)) s)
          (Syn.subst (up (fun i => Syn.var i.succ)) t) from rfl,
      NFm.start_eq_zero, NFm.subst_repl_var,
      show (NFm.eq (Syn.subst (up (fun i => Syn.var i.succ)) s)
        (Syn.subst (up (fun i => Syn.var i.succ)) t)).subst (up (inst zero)) = .eq s t from
      NFm.subst_dummy_inst (.eq s t) zero]
    exact h
  exact dE hD (hyp List.mem_cons_self)

/-- `Q` by cases, at a dummy witness coordinate. -/
theorem dDummy (B : NFm (n + 1))
    (h : ZN ((B.subst (inst zero)).shift :: Γ.map NFm.shift)
      (B.subst (repl (succ (Syn.var 0))))) :
    ZN Γ (.D (B.subst (up (fun i => Syn.var i.succ)))) := by
  refine dI _ (iter (succ zero) zero zero) (start_alias _) ?_
  rw [NFm.start_iter, NFm.subst_dummy_inst, ← NFm.shift_subst_inst_zero]
  exact h

/-- **`D` by cases for a literal equation at the literal witness `0`.** -/
theorem dICaseEqZero (a b : Tm (n + 2))
    (h : ZN ((((NFm.eq a b).subst (up (inst zero))).subst (inst zero)).shift
        :: Γ.map NFm.shift)
      (((NFm.eq a b).subst (up (inst zero))).subst (repl (succ (Syn.var 0))))) :
    ZN Γ (.D (.eq a b)) := by
  -- `Q_y E(0, y)` as a hypothesis, under a new variable
  refine dE (dDummy _ h) ?_
  show ZN _ (NFm.D ((NFm.eq a b).subst (up (up (fun i => Syn.var i.succ)))))
  -- the introduction at the alias of zero
  refine dI _ (iter (succ zero) zero zero) (start_alias _) ?_
  rw [NFm.start_iter, NFm.subst_weak_inst, NFm.subst_weak_inst]
  have hc : Syn.shift (iter (succ zero) zero zero : Tm (n + 1)) = iter (succ zero) zero zero := by
    simp
  rw [hc]
  -- from `E(c, 0)` to `E(0, 0)`
  have h1 : ZN ((NFm.eq a b).subst (NFm.rho (iter (succ zero) zero zero) zero)
        :: (NFm.Q (((NFm.eq a b).subst (up (inst zero))).subst (up (fun i => Syn.var i.succ)))
          :: Γ.map NFm.shift).map NFm.shift)
      ((NFm.eq a b).subst (NFm.rho zero zero)) :=
    trE ((NFm.eq a b).subst (NFm.tau zero)) rfl aliasEq
      (NFm.subst_tau_inst _ _ _) (NFm.subst_tau_inst _ _ _) (hyp List.mem_cons_self)
  -- the closure gives `E(0, S z)`
  have hq : ZN ((NFm.eq a b).subst (NFm.rho (iter (succ zero) zero zero) zero)
        :: (NFm.Q (((NFm.eq a b).subst (up (inst zero))).subst (up (fun i => Syn.var i.succ)))
          :: Γ.map NFm.shift).map NFm.shift)
      (.Q ((((NFm.eq a b).subst (up (inst zero))).subst (up (fun i => Syn.var i.succ))).subst
        (up (fun i => Syn.var i.succ)))) :=
    hyp (List.mem_cons_of_mem _ List.mem_cons_self)
  rw [← NFm.subst_closure_inst] at h1
  have h2 := qE (succ (Syn.var 0)) hq h1
  rw [NFm.subst_closure_inst] at h2
  -- from `E(0, S z)` to `E(c, S z)`
  exact trE ((NFm.eq a b).subst (NFm.tau (succ (Syn.var 0)))) rfl
    (eqSymm aliasEq) (NFm.subst_tau_inst _ _ _) (NFm.subst_tau_inst _ _ _) h2

/-- **`D` by cases**, for every matrix and witness. -/
theorem dICase (B : NFm (n + 2)) (t : Tm n)
    (h : ZN (((B.subst (up (inst t))).subst (inst zero)).shift :: Γ.map NFm.shift)
      ((B.subst (up (inst t))).subst (repl (succ (Syn.var 0))))) : ZN Γ (.D B) := by
  by_cases hc : (∃ a b, B = NFm.eq a b) ∧ nf t = zero
  · obtain ⟨⟨a, b, rfl⟩, ht⟩ := hc
    refine dICaseEqZero a b ?_
    -- the premises at `t` and at `0` have the same normal form
    have e : fnf ((NFm.eq a b).subst (up (inst t)))
        = fnf ((NFm.eq a b).subst (up (inst zero))) :=
      fnf_subst_congr rfl (nf_up_congr fun i => by
        refine Fin.cases ?_ (fun j => ?_) i
        · show nf t = nf zero
          rw [ht]
          rfl
        · rfl)
    have h' : ZEPrf (((((NFm.eq a b).subst (up (inst t))).subst (inst zero)).shift
        :: Γ.map NFm.shift).map fnf)
        (fnf (((NFm.eq a b).subst (up (inst t))).subst (repl (succ (Syn.var 0))))) := h
    show ZEPrf (((((NFm.eq a b).subst (up (inst zero))).subst (inst zero)).shift
        :: Γ.map NFm.shift).map fnf)
        (fnf (((NFm.eq a b).subst (up (inst zero))).subst (repl (succ (Syn.var 0)))))
    rw [List.map_cons, fnf_shift, fnf_subst_congr (σ' := inst zero) e (fun _ => rfl),
      fnf_subst_congr (σ' := repl (succ (Syn.var 0))) e (fun _ => rfl)] at h'
    rw [List.map_cons, fnf_shift]
    exact h'
  · have h₂ : NFm.start B t = zero :=
      NFm.start_of_not fun k => hc ⟨k.1, by rw [k.2]; rfl⟩
    have h₁ : NFm.start (fnf B) (nf t) = zero := by
      refine NFm.start_of_not fun k => hc ⟨?_, k.2⟩
      obtain ⟨a, b, e⟩ := k.1
      cases B with
      | eq a' b' => exact ⟨a', b', rfl⟩
      | Q B' => cases e
      | D B' => cases e
    refine dI B t (h₁.trans h₂.symm) ?_
    rw [h₂, ← NFm.shift_subst_inst_zero]
    exact h

end ZN

/-- Every kernel derivation becomes a derivation of `ZEPrf` when its formulas
are normalized. -/
theorem NPrf.toZE (h : NPrf Γ A) : ZN Γ A := by
  induction h with
  | hyp h => exact ZN.hyp h
  | iterZero a h => exact ZEPrf.reflNf a
  | iterSucc c a h => exact ZEPrf.iterSuccNf c a h
  | trOne h _ _ ih₁ ih₂ => exact ZEPrf.trOneNf h ih₁ ih₂
  | qE t _ _ ih₁ ih₂ => exact ZN.qE t ih₁ ih₂
  | dE _ _ ih₁ ih₂ => exact ZN.dE ih₁ ih₂
  | dICase B t _ ih => exact ZN.dICase B t ih
  | qIInd s t _ ih => exact ZN.qInd s t ih

/-- **Six rules with one evaluation rule on zero-normal terms.**  The kernel
derives a sequent exactly when `ZEPrf` derives its zero-normal form. -/
theorem zeprf_iff_nprf : ZEPrf (Γ.map fnf) (fnf A) ↔ NPrf Γ A :=
  ⟨fun h => (equivFnf A).mpr (h.toNPrf.cut fun B hB => by
      obtain ⟨C, hC, rfl⟩ := List.mem_map.1 hB
      exact (equivFnf C).mp (.hyp hC)), NPrf.toZE⟩

/-- The same calculus proves the zero-normal form of a sequent exactly when
iPRA proves its reading. -/
theorem zeprf_iff_pra : ZEPrf (Γ.map fnf) (fnf A) ↔ (Γ.map NFm.toPRA ⊢[PRAAx] A.toPRA) :=
  zeprf_iff_nprf.trans native_iff_pra

end LeanProofs.ConciseIPRA
