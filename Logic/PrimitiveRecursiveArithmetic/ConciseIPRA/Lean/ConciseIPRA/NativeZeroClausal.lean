import ConciseIPRA.NativeUniformClauses
import ConciseIPRA.NativeZeroNormal

/-!
# Five rules on zero-normal terms with one evaluation scheme

`ZCPrf` is the calculus `C5` of the package
`Research/clausal_single_evaluation`.  Terms and formulas are zero-normal:
an iterator whose counter is the literal `0` is contracted, and every rule
normalizes its conclusion.  Contexts are lists of clauses, as in
`NativeClausal`.  There are five rules:

* **Refl**: `t = t`;
* **Eval**: from `I(c, a; u.h) = t` and `I(S c, a; u.h) = r` infer
  `r = h[t/u]`;
* **Use**, **Elim** and **Intro**, as in the clause calculus `CPrf`, the mode
  of Intro being read off the matrix and the witness: progress for a literal
  equation at the literal witness `0`, cases otherwise.

`zcprf_iff_nprf` proves that the kernel derives a sequent exactly when `ZCPrf`
derives the normal form of its `Q`-free form.

Soundness reads each rule in the kernel.  Completeness normalizes a derivation
of the raw clause calculus `CPrf`, rule by rule.  One case does not survive
normalization as it stands: an introduction by cases whose matrix is an
equation and whose witness `t` is not the literal `0` but has the normal form
`0`.  On normal terms that witness would select progress.  The introduction is
then made at the witness `w = I(S 0, 0; u.0)`, which is zero-normal, provably
`0` by one Eval, and not the literal `0`; the translation carries, as an
invariant on the contexts, that an assumption `E(t)` of the source may be
represented by the assumption `E(w)` of the target, and converts between the
two by equational reasoning from Eval wherever the assumption is used.

`ZVPrf` is the same calculus with the uniform clauses of
`NativeUniformClauses`: a clause has at most one antecedent, and reflexivity
is not a rule but the fixed clause `[; y. y = y]` of the context.  Its four
schemes Use, Step, Open and Close are those of the package
`Research/clause_contexts` (`zvprf_iff_zcprf`, `zvprf_iff_nprf`).
-/

namespace LeanProofs.ConciseIPRA

open Syn
open Tm (zero succ iter)
open scoped Fm
open ZeroNormalization

variable {n m : ℕ}

/-- A zero-normal term that is provably `0` and is not the literal `0`. -/
def Tm.wz : Tm n := iter (succ zero) zero zero

theorem Tm.nf_wz : nf (Tm.wz : Tm n) = Tm.wz := rfl

theorem Tm.shift_wz : Syn.shift (Tm.wz : Tm n) = Tm.wz := rfl

theorem Tm.wz_ne_zero : (Tm.wz : Tm n) ≠ zero := fun e => by cases e

namespace NFm

theorem fnf_fnf_subst (A : NFm n) (σ : Fin n → Tm m) :
    fnf ((fnf A).subst σ) = fnf (A.subst σ) :=
  fnf_subst_congr (fnf_idempotent A) fun _ => rfl

theorem fnf_fnf_subst₂ {k : ℕ} (A : NFm n) (σ : Fin n → Tm m) (τ : Fin m → Tm k) :
    fnf (((fnf A).subst σ).subst τ) = fnf ((A.subst σ).subst τ) :=
  fnf_subst_congr (fnf_fnf_subst A σ) fun _ => rfl

theorem qfree_fnf (A : NFm n) : (fnf A).QFree ↔ A.QFree := by
  induction A with
  | eq s t => exact Iff.rfl
  | Q B _ => exact Iff.rfl
  | D B ih => exact ih

/-- Normalization preserves the mode of the introduction, except at an
equation whose witness has the normal form `0` and is not the literal `0`. -/
theorem start_fnf {B : NFm (n + 2)} {t : Tm n}
    (h : ¬((∃ a b, B = NFm.eq a b) ∧ nf t = zero ∧ t ≠ zero)) :
    start (fnf B) (nf t) = start B t := by
  cases B with
  | eq a b =>
    by_cases ht : t = zero
    · subst ht; rfl
    · have hn : nf t ≠ zero := fun e => h ⟨⟨a, b, rfl⟩, e, ht⟩
      rw [start_of_not (fun k => ht k.2)]
      exact start_of_not (fun k => hn k.2)
  | Q B =>
    exact (start_of_not (B := .Q (fnf B)) (t := nf t) fun k => by
      obtain ⟨⟨a, b, e⟩, _⟩ := k; cases e).trans
      (start_of_not (B := .Q B) (t := t) fun k => by obtain ⟨⟨a, b, e⟩, _⟩ := k; cases e).symm
  | D B =>
    exact (start_of_not (B := .D (fnf B)) (t := nf t) fun k => by
      obtain ⟨⟨a, b, e⟩, _⟩ := k; cases e).trans
      (start_of_not (B := .D B) (t := t) fun k => by obtain ⟨⟨a, b, e⟩, _⟩ := k; cases e).symm

/-- The substitution that turns the witness of a matrix into a hole: the bound
variable becomes `η`, the witness becomes the variable `0`. -/
def holeS (η : Tm (n + 1)) : Fin (n + 2) → Tm (n + 2) :=
  Fin.cases (Syn.shift η) (Fin.cases (Syn.var 0) fun i => Syn.var i.succ.succ)

theorem subst_hole (B : NFm (n + 2)) (η : Tm (n + 1)) (t : Tm n) :
    (B.subst (holeS η)).subst (inst (Syn.shift t)) = (B.subst (up (inst t))).subst (repl η) := by
  rw [subst_subst, subst_subst]
  refine B.subst_ext fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [holeS]
  · refine Fin.cases ?_ (fun k => ?_) j <;> simp [holeS]

end NFm

namespace Cl

/-- The clause with both parts in zero-normal form. -/
def norm (c : Cl n) : Cl n := ⟨fnf c.ante, fnf c.cons⟩

theorem norm_shift (c : Cl n) : norm c.shift = (norm c).shift := by
  show (⟨fnf c.ante.shift, fnf (c.cons.subst (up fun i => Syn.var i.succ))⟩ : Cl _)
    = ⟨(fnf c.ante).shift, (fnf c.cons).subst (up fun i => Syn.var i.succ)⟩
  rw [fnf_shift, up_ren Fin.succ, fnf_ren]

theorem norm_asm (X : NFm n) : norm (asm X) = asm (fnf X) := by
  show (⟨fnf (.eq zero zero), fnf X.shift⟩ : Cl _) = ⟨.eq zero zero, (fnf X).shift⟩
  rw [fnf_shift]
  rfl

end Cl

/-- Derivability in the five-rule clause calculus on zero-normal terms. -/
inductive ZCPrf : {n : ℕ} → List (Cl n) → NFm n → Prop
  | refl {n : ℕ} {Γ : List (Cl n)} (t : Tm n) : ZCPrf Γ (.eq (nf t) (nf t))
  /-- Eval: from `I(c, a; u.h) = t` and `I(S c, a; u.h) = r` infer
  `r = h[t/u]`. -/
  | step {n : ℕ} {Γ : List (Cl n)} (c a : Tm n) (h : Tm (n + 1)) {t r : Tm n}
      (h₁ : ZCPrf Γ (.eq (nf (iter c a h)) t))
      (h₂ : ZCPrf Γ (.eq (nf (iter (succ c) a h)) r)) :
      ZCPrf Γ (.eq r (nf (Syn.subst (inst t) h)))
  | use {n : ℕ} {Γ : List (Cl n)} {c : Cl n} (t : Tm n) (hc : c ∈ Γ) (h : ZCPrf Γ c.ante) :
      ZCPrf Γ (fnf (c.cons.subst (inst t)))
  | elim {n : ℕ} {Γ : List (Cl n)} {B : NFm (n + 2)} {A : NFm n} (h₁ : ZCPrf Γ (.D B))
      (h₂ : ZCPrf (⟨fnf (B.subst (inst zero)), B⟩ :: Γ.map Cl.shift) A.shift) : ZCPrf Γ A
  | intro {n : ℕ} {Γ : List (Cl n)} (B : NFm (n + 2)) (t : Tm n) (hB : B.QFree)
      (hn : fnf B = B) (ht : nf t = t)
      (h : ZCPrf (Cl.asm (fnf ((B.subst (up (inst t))).subst (repl (NFm.start B t))))
          :: Γ.map Cl.shift)
        (fnf ((B.subst (up (inst t))).subst (repl (succ (var 0)))))) :
      ZCPrf Γ (.D B)

namespace ZCPrf

variable {Γ Δ : List (Cl n)} {A : NFm n}

/-- Every rule is a derived rule of the kernel, up to normal forms. -/
theorem toNPrf (h : ZCPrf Γ A) : NPrf (Γ.map Cl.toN) A := by
  induction h with
  | refl t => exact NPrf.eqRefl _
  | step c a h _ _ ih₁ ih₂ =>
    exact NPrf.eqTrans (NPrf.eqSymm ih₂) (NPrf.eqTrans (NPrf.eqSymm (eqNf _))
      (NPrf.eqTrans (.iterSucc c a h) (NPrf.eqTrans (NPrf.eqCongr h (eqNf (iter c a h)))
        (NPrf.eqTrans (NPrf.eqCongr h ih₁) (eqNf _)))))
  | @use _ Γ c t hc _ ih =>
    exact (equivFnf _).mp
      (NPrf.allE t (NPrf.impE (.hyp (List.mem_map_of_mem (f := Cl.toN) hc)) ih))
  | @elim _ Γ B A _ _ ih₁ ih₂ =>
    rw [List.map_cons, Cl.map_toN_shift] at ih₂
    refine .dE ih₁ (NPrf.cut1 ?_ (NPrf.wkUnder ih₂))
    show NPrf _ (NFm.imp (fnf (B.subst (inst zero))) (NFm.all B))
    exact NPrf.impI (NPrf.impE
      ((NPrf.qComp (NEquiv.refl B)).mpr (.hyp (List.mem_cons_of_mem _ List.mem_cons_self)))
      ((equivFnf _).mpr NPrf.hyp0))
  | @intro _ Γ B t _ _ _ _ ih =>
    rw [List.map_cons, Cl.map_toN_shift] at ih
    exact .ofDI B t ((equivFnf _).mpr
      (NPrf.cut1 (NPrf.asmClause ((equivFnf _).mp NPrf.hyp0)) (NPrf.wkUnder ih)))

/-! ### Equality from Eval -/

/-- The pivot: from `x = y` and `x = z` infer `z = y`, by two Evals through
`I(S 0, x; v.v)`. -/
theorem pivot {x y z : Tm n} (h₁ : ZCPrf Γ (.eq (nf x) (nf y)))
    (h₂ : ZCPrf Γ (.eq (nf x) (nf z))) : ZCPrf Γ (.eq (nf z) (nf y)) := by
  have k := ZCPrf.step (Γ := Γ) zero (nf x) (Syn.var 0) (t := nf z)
    (by simpa only [nf_iter, nf_zero, smartI_zero, nf_idempotent] using h₂)
    (.refl (iter (succ zero) (nf x) (Syn.var 0)))
  have k' := ZCPrf.step (Γ := Γ) zero (nf x) (Syn.var 0) (t := nf y) (r := nf z)
    (by simpa only [nf_iter, nf_zero, smartI_zero, nf_idempotent] using h₁)
    (by simpa only [Syn.subst_var, Syn.inst_zero, nf_idempotent] using k)
  simpa only [Syn.subst_var, Syn.inst_zero, nf_idempotent] using k'

theorem symmNf {x y : Tm n} (h : ZCPrf Γ (.eq (nf x) (nf y))) : ZCPrf Γ (.eq (nf y) (nf x)) :=
  pivot (.refl x) h

theorem transNf {x y z : Tm n} (h₁ : ZCPrf Γ (.eq (nf x) (nf y)))
    (h₂ : ZCPrf Γ (.eq (nf y) (nf z))) : ZCPrf Γ (.eq (nf x) (nf z)) :=
  pivot h₂ (symmNf h₁)

/-- Transport in one term, by two Evals at the counter `0`. -/
theorem trOneNf (h : Tm (n + 1)) {s t u : Tm n} (h₁ : ZCPrf Γ (.eq (nf s) (nf t)))
    (h₂ : ZCPrf Γ (.eq (nf (Syn.subst (inst s) h)) (nf u))) :
    ZCPrf Γ (.eq (nf u) (nf (Syn.subst (inst t) h))) := by
  have k := ZCPrf.step (Γ := Γ) zero (nf s) h (t := nf s)
    (by simpa only [nf_iter, nf_zero, smartI_zero, nf_idempotent] using ZCPrf.refl (Γ := Γ) s)
    (.refl (iter (succ zero) (nf s) h))
  rw [nf_subst_congr (t := h) (t' := h) rfl (nf_inst s)] at k
  have k₃ := ZCPrf.step (Γ := Γ) zero (nf s) h (t := nf t)
    (by simpa only [nf_iter, nf_zero, smartI_zero, nf_idempotent] using h₁) (transNf k h₂)
  rw [nf_subst_congr (t := h) (t' := h) rfl (nf_inst t)] at k₃
  exact k₃

/-- The nonliteral zero is `0`, by one Eval. -/
theorem wzEq : ZCPrf Γ (.eq (Tm.wz : Tm n) zero) :=
  ZCPrf.step (Γ := Γ) zero zero zero (.refl zero) (.refl Tm.wz)

/-- An instance of an equation may be moved along an equation of its
argument. -/
theorem convEq {E : NFm (n + 1)} (hE : ∃ a b, E = NFm.eq a b) {s t : Tm n}
    (he : ZCPrf Γ (.eq (nf s) (nf t))) (h : ZCPrf Γ (fnf (E.subst (inst s)))) :
    ZCPrf Γ (fnf (E.subst (inst t))) := by
  obtain ⟨a, b, rfl⟩ := hE
  have h' : ZCPrf Γ (.eq (nf (Syn.subst (inst s) a)) (nf (Syn.subst (inst s) b))) := h
  have ka := trOneNf a he (.refl (Syn.subst (inst s) a))
  have kb := trOneNf b he (.refl (Syn.subst (inst s) b))
  exact transNf (symmNf ka) (transNf h' kb)

end ZCPrf

/-! ### Completeness, by normalizing the raw clause calculus -/

/-- The invariant of the normalization: a clause of the source is normalized
in the target, or it is an assumption `E(t)` for an equation `E` and a term `t`
of normal form `0`, and the target has the assumption `E(w)`. -/
def Conv (Γ Δ : List (Cl n)) : Prop :=
  ∀ c ∈ Γ, Cl.norm c ∈ Δ ∨ ∃ (E : NFm (n + 1)) (t : Tm n), (∃ a b, E = NFm.eq a b) ∧
    nf t = zero ∧ c = Cl.asm (E.subst (inst t)) ∧ Cl.asm (fnf (E.subst (inst Tm.wz))) ∈ Δ

theorem Conv.lift {Γ Δ : List (Cl n)} (s : Conv Γ Δ) {c' d' : Cl (n + 1)}
    (h : Conv [c'] [d']) : Conv (c' :: Γ.map Cl.shift) (d' :: Δ.map Cl.shift) := by
  intro c hc
  rcases List.mem_cons.1 hc with rfl | hc
  · rcases h c List.mem_cons_self with hm | ⟨E, t, hE, ht, e, hm⟩
    · exact .inl (List.mem_singleton.1 hm ▸ List.mem_cons_self)
    · exact .inr ⟨E, t, hE, ht, e, List.mem_singleton.1 hm ▸ List.mem_cons_self⟩
  · obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.1 hc
    rcases s c₀ hc₀ with hm | ⟨E, t, ⟨a, b, rfl⟩, ht, rfl, hm⟩
    · exact .inl (List.mem_cons_of_mem _ (by
        rw [Cl.norm_shift]; exact List.mem_map_of_mem hm))
    · refine .inr ⟨(NFm.eq a b).subst (up fun i => Syn.var i.succ), Syn.shift t,
        ⟨_, _, NFm.subst_eq _ _ _⟩, by rw [nf_shift, ht]; rfl, ?_, ?_⟩
      · rw [Cl.asm_shift]
        exact congrArg Cl.asm (NFm.subst_inst (NFm.eq a b) _ t)
      · have k := List.mem_map_of_mem (f := Cl.shift) hm
        rw [Cl.asm_shift, ← fnf_shift] at k
        have e : ((NFm.eq a b).subst (inst Tm.wz)).shift
            = ((NFm.eq a b).subst (up fun i => Syn.var i.succ)).subst (inst Tm.wz) :=
          NFm.subst_inst (NFm.eq a b) _ Tm.wz
        rw [e] at k
        exact List.mem_cons_of_mem _ k

/-- Normalization of a derivation of the raw clause calculus. -/
theorem CPrf.toZC {Γ : List (Cl n)} {A : NFm n} (h : CPrf Γ A) :
    ∀ {Δ : List (Cl n)}, Conv Γ Δ → ZCPrf Δ (fnf A) := by
  induction h with
  | refl t => intro Δ _; exact .refl t
  | @evalZero _ Γ h a t r _ _ ih₁ ih₂ =>
    intro Δ s
    have k₂ : ZCPrf Δ (.eq (nf a) (nf r)) := ih₂ s
    exact ZCPrf.pivot (ih₁ s) k₂
  | @evalSucc _ Γ c a h t r _ _ ih₁ ih₂ =>
    intro Δ s
    have k := ZCPrf.step c a h (ih₁ s) (ih₂ s)
    rw [nf_subst_congr (t := h) (t' := h) rfl (nf_inst t)] at k
    exact k
  | @use _ Γ c t hc _ ih =>
    intro Δ s
    rcases s c hc with hm | ⟨E, t₀, hE, ht₀, rfl, hm⟩
    · have k := ZCPrf.use t hm (ih s)
      rwa [show (Cl.norm c).cons = fnf c.cons from rfl, NFm.fnf_fnf_subst] at k
    · show ZCPrf Δ (fnf ((E.subst (inst t₀)).shift.subst (inst t)))
      rw [NFm.subst_inst_shift]
      have k := ZCPrf.use (c := Cl.asm (fnf (E.subst (inst Tm.wz)))) zero hm (.refl zero)
      rw [show (Cl.asm (fnf (E.subst (inst Tm.wz)))).cons = (fnf (E.subst (inst Tm.wz))).shift
        from rfl, NFm.subst_inst_shift, fnf_idempotent] at k
      refine ZCPrf.convEq hE ?_ k
      rw [ht₀]
      exact ZCPrf.wzEq
  | @elim _ Γ B A _ _ ih₁ ih₂ =>
    intro Δ s
    refine .elim (B := fnf B) (ih₁ s) ?_
    rw [← fnf_shift]
    refine ih₂ (s.lift fun c hc => .inl ?_)
    rw [List.mem_singleton.1 hc, NFm.fnf_fnf_subst]
    exact List.mem_cons_self
  | @intro _ Γ B t hB _ ih =>
    intro Δ s
    by_cases hc : (∃ a b, B = NFm.eq a b) ∧ nf t = zero ∧ t ≠ zero
    · obtain ⟨hE, ht0, htz⟩ := hc
      rw [NFm.start_of_not (fun k => htz k.2)] at ih
      refine .intro (fnf B) Tm.wz ((NFm.qfree_fnf B).2 hB) (fnf_idempotent B) Tm.nf_wz ?_
      rw [NFm.start_of_not (fun k => Tm.wz_ne_zero k.2), NFm.fnf_fnf_subst₂,
        NFm.fnf_fnf_subst₂, ← NFm.subst_hole B zero Tm.wz,
        ← NFm.subst_hole B (succ (Syn.var 0)) Tm.wz, Tm.shift_wz]
      have hE₀ : ∃ a b, B.subst (NFm.holeS zero) = NFm.eq a b := by
        obtain ⟨a, b, rfl⟩ := hE; exact ⟨_, _, NFm.subst_eq _ _ _⟩
      have hE₁ : ∃ a b, B.subst (NFm.holeS (succ (Syn.var 0))) = NFm.eq a b := by
        obtain ⟨a, b, rfl⟩ := hE; exact ⟨_, _, NFm.subst_eq _ _ _⟩
      have k := ih (Δ := Cl.asm (fnf ((B.subst (NFm.holeS zero)).subst (inst Tm.wz)))
          :: Δ.map Cl.shift) (s.lift fun c hc => .inr ⟨B.subst (NFm.holeS zero), Syn.shift t,
            hE₀, by rw [nf_shift, ht0]; rfl, by
              rw [List.mem_singleton.1 hc, NFm.subst_hole], List.mem_cons_self⟩)
      rw [← NFm.subst_hole B (succ (Syn.var 0)) t] at k
      refine ZCPrf.convEq hE₁ ?_ k
      rw [nf_shift, ht0]
      exact ZCPrf.symmNf (x := Tm.wz) (y := zero) ZCPrf.wzEq
    · refine .intro (fnf B) (nf t) ((NFm.qfree_fnf B).2 hB) (fnf_idempotent B)
        (nf_idempotent t) ?_
      have e : ∀ η,
          fnf (((fnf B).subst (up (inst (nf t)))).subst (repl η))
            = fnf ((B.subst (up (inst t))).subst (repl η)) := fun η =>
        fnf_subst_congr (fnf_subst_congr (fnf_idempotent B) (nf_up_congr (nf_inst t)))
          fun _ => rfl
      rw [NFm.start_fnf hc, e, e]
      refine ih (s.lift fun c hc' => .inl ?_)
      rw [List.mem_singleton.1 hc', Cl.norm_asm]
      exact List.mem_cons_self

variable {Γ : List (NFm n)} {A : NFm n}

/-- **Five rules on zero-normal terms.**  The kernel derives a sequent exactly
when the calculus with Refl, one Eval scheme, Use, Elim and Intro derives the
normal form of its `Q`-free form. -/
theorem zcprf_iff_nprf :
    ZCPrf (Γ.map fun X => Cl.asm (fnf (NFm.unQ X))) (fnf (NFm.unQ A)) ↔ NPrf Γ A := by
  constructor
  · intro h
    refine (NEquiv.unQ A).mp ((equivFnf _).mpr (h.toNPrf.cut fun C hC => ?_))
    rw [List.map_map, List.mem_map] at hC
    obtain ⟨X, hX, rfl⟩ := hC
    exact NPrf.asmClause ((equivFnf _).mp ((NEquiv.unQ X).mpr (.hyp hX)))
  · intro h
    refine (cprf_iff_nprf.2 h).toZC fun c hc => .inl ?_
    rw [List.mem_map] at hc
    obtain ⟨X, hX, rfl⟩ := hc
    rw [Cl.norm_asm]
    exact List.mem_map_of_mem (f := fun X => Cl.asm (fnf (NFm.unQ X))) hX

/-- On `Q`-free sequents: the normal form of the sequent itself. -/
theorem zcprf_iff_nprf_of_qfree (hΓ : ∀ X ∈ Γ, X.QFree) (hA : A.QFree) :
    ZCPrf (Γ.map fun X => Cl.asm (fnf X)) (fnf A) ↔ NPrf Γ A := by
  have e : (Γ.map fun X => Cl.asm (fnf (NFm.unQ X))) = Γ.map fun X => Cl.asm (fnf X) :=
    List.map_congr_left fun X hX => by rw [NFm.unQ_of_qfree X (hΓ X hX)]
  rw [← zcprf_iff_nprf, e, NFm.unQ_of_qfree A hA]

/-! ### Four schemes and the reflexivity clause -/

/-- Derivability on zero-normal terms with uniform clause use and no
reflexivity rule. -/
inductive ZVPrf : {n : ℕ} → List (UCl n) → NFm n → Prop
  /-- Use: from the antecedents of a clause, none or one, infer an instance of
  its consequent. -/
  | use {n : ℕ} {Γ : List (UCl n)} {c : UCl n} (t : Tm n) (hc : c ∈ Γ)
      (h : ∀ A, c.ante = some A → ZVPrf Γ A) : ZVPrf Γ (fnf (c.cons.subst (inst t)))
  /-- Step. -/
  | step {n : ℕ} {Γ : List (UCl n)} (c a : Tm n) (h : Tm (n + 1)) {t r : Tm n}
      (h₁ : ZVPrf Γ (.eq (nf (iter c a h)) t))
      (h₂ : ZVPrf Γ (.eq (nf (iter (succ c) a h)) r)) :
      ZVPrf Γ (.eq r (nf (Syn.subst (inst t) h)))
  /-- Open. -/
  | elim {n : ℕ} {Γ : List (UCl n)} {B : NFm (n + 2)} {A : NFm n} (h₁ : ZVPrf Γ (.D B))
      (h₂ : ZVPrf (⟨some (fnf (B.subst (inst zero))), B⟩ :: Γ.map UCl.shift) A.shift) :
      ZVPrf Γ A
  /-- Close. -/
  | intro {n : ℕ} {Γ : List (UCl n)} (B : NFm (n + 2)) (t : Tm n) (hB : B.QFree)
      (hn : fnf B = B) (ht : nf t = t)
      (h : ZVPrf (UCl.asm (fnf ((B.subst (up (inst t))).subst (repl (NFm.start B t))))
          :: Γ.map UCl.shift)
        (fnf ((B.subst (up (inst t))).subst (repl (succ (var 0)))))) :
      ZVPrf Γ (.D B)

theorem ZVPrf.toZC {Δ : List (UCl n)} {A : NFm n} (h : ZVPrf Δ A) :
    ∀ {Γ : List (Cl n)}, (∀ c ∈ Δ, c = UCl.refl ∨ c.toCl ∈ Γ) → ZCPrf Γ A := by
  induction h with
  | @use _ Δ c t hc _ ih =>
    intro Γ s
    rcases s c hc with rfl | hm
    · exact .refl t
    · obtain ⟨a, b⟩ := c
      cases a with
      | none => exact .use (c := ⟨.eq zero zero, b⟩) t hm (.refl zero)
      | some A => exact .use (c := ⟨A, b⟩) t hm (ih A rfl s)
  | step c a h _ _ ih₁ ih₂ => intro Γ s; exact .step c a h (ih₁ s) (ih₂ s)
  | elim _ _ ih₁ ih₂ => intro Γ s; exact .elim (ih₁ s) (ih₂ (UCl.liftToCl s _))
  | intro B t hB hn ht _ ih => intro Γ s; exact .intro B t hB hn ht (ih (UCl.liftToCl s _))

theorem ZCPrf.toZV {Γ : List (Cl n)} {A : NFm n} (h : ZCPrf Γ A) :
    ∀ {Δ : List (UCl n)}, UCl.refl ∈ Δ →
      (∀ c ∈ Γ, ∃ d ∈ Δ, d.cons = c.cons ∧ ∀ A, d.ante = some A → A = c.ante) → ZVPrf Δ A := by
  induction h with
  | refl t =>
    intro Δ hr _
    exact ZVPrf.use (c := UCl.refl) t hr (fun A hA => by cases hA)
  | step c a h _ _ ih₁ ih₂ => intro Δ hr s; exact .step c a h (ih₁ hr s) (ih₂ hr s)
  | @use _ Γ c t hc _ ih =>
    intro Δ hr s
    obtain ⟨d, hd, hdc, hda⟩ := s c hc
    rw [← hdc]
    exact .use t hd (fun A hA => by rw [hda A hA]; exact ih hr s)
  | elim _ _ ih₁ ih₂ =>
    intro Δ hr s
    refine .elim (ih₁ hr s) (ih₂ (List.mem_cons_of_mem _ ?_) (UCl.liftOfCl s _ _ rfl ?_))
    · rw [← UCl.refl_shift]; exact List.mem_map_of_mem hr
    · intro A hA; exact (Option.some.inj hA).symm
  | intro B t hB hn ht _ ih =>
    intro Δ hr s
    refine .intro B t hB hn ht (ih (List.mem_cons_of_mem _ ?_) (UCl.liftOfCl s _ _ rfl ?_))
    · rw [← UCl.refl_shift]; exact List.mem_map_of_mem hr
    · intro A hA; cases hA

/-- With the reflexivity clause in the context, uniform clause use derives
what the five-rule calculus derives. -/
theorem zvprf_iff_zcprf :
    ZVPrf (UCl.refl :: Γ.map UCl.asm) A ↔ ZCPrf (Γ.map Cl.asm) A := by
  constructor
  · intro h
    refine h.toZC fun c hc => ?_
    rcases List.mem_cons.1 hc with rfl | hc
    · exact .inl rfl
    · obtain ⟨X, hX, rfl⟩ := List.mem_map.1 hc
      exact .inr (List.mem_map_of_mem (f := Cl.asm) hX)
  · intro h
    refine h.toZV List.mem_cons_self fun c hc => ?_
    obtain ⟨X, hX, rfl⟩ := List.mem_map.1 hc
    exact ⟨UCl.asm X, List.mem_cons_of_mem _ (List.mem_map_of_mem hX), rfl,
      fun A hA => by cases hA⟩

/-- **Four schemes on zero-normal terms.**  The kernel derives a sequent
exactly when Use, Step, Open and Close derive the normal form of its `Q`-free
form from the reflexivity clause and the corresponding assumptions. -/
theorem zvprf_iff_nprf :
    ZVPrf (UCl.refl :: (Γ.map fun X => fnf (NFm.unQ X)).map UCl.asm) (fnf (NFm.unQ A))
      ↔ NPrf Γ A := by
  rw [zvprf_iff_zcprf, List.map_map]
  exact zcprf_iff_nprf

end LeanProofs.ConciseIPRA
