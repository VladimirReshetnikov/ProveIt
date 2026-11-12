import ConciseIPRA.NativeSix
import ConciseIPRA.NativeClausal

/-!
# Five rules, closed under substitution

`KPrf` is the clause calculus of `NativeClausal` with the introduction of
`NativeDiagonal`: formulas are equations and `D` only, contexts are lists of
clauses `[A; y.B(y)]`, and the rules are

* **Refl**, **Eval** (two cases), **Use**, **Elim**, and
* **Intro**: from `B(t, η) ⊢ B(t, S z)` with `z` fresh infer `D_{x,y} B`, where
  `η = z` exactly when `B` is literally `I(y, y; u.h) = I(y, y; v.k)`.

No rule inspects a witness, a transport source or a normal form, so the
calculus is closed under substitution by a direct induction on derivations
(`KPrf.subst`), which the clause calculus `CPrf` with the witness-tested
introduction is not.  None of the delivered packages states this combination.

* `kprf_iff_nprf_of_qfree`: on `Q`-free sequents `KPrf` derives exactly what the
  kernel derives;
* `kprf_iff_nprf`: for arbitrary native sequents, with `Q_y B` rewritten as a
  `D` with an unused witness coordinate;
* `KPrf.qfree`: only `Q`-free formulas from `Q`-free clauses.

Completeness translates the six-rule calculus `SPrf` rule by rule.  In the
case of `DE` the `D` formula that stands for the opened `Q` is introduced in
whichever mode its matrix dictates: if the matrix is diagonal its base is a
theorem by computation, otherwise the base is the assumption of the rule.
-/

namespace LeanProofs.ConciseIPRA

open Syn
open Tm (zero succ iter)

variable {n m : ℕ}

namespace NFm

theorem isDiag_subst_up (B : NFm (n + 1)) (τ : Fin n → Tm m) :
    (B.subst (up τ)).isDiag = B.isDiag := by
  cases B with
  | eq s t =>
    show ((Syn.subst (up τ) s).isDiag && (Syn.subst (up τ) t).isDiag) = (s.isDiag && t.isDiag)
    rw [Tm.isDiag_subst_up, Tm.isDiag_subst_up]
  | Q B => rfl
  | D B => rfl

theorem dstart_unQ (B : NFm (n + 2)) : dstart (unQ B) = dstart B := by
  cases B <;> rfl

end NFm

/-- Derivability in the clause calculus with the diagonal introduction. -/
inductive KPrf : {n : ℕ} → List (Cl n) → NFm n → Prop
  | refl {n : ℕ} {Γ : List (Cl n)} (t : Tm n) : KPrf Γ (.eq t t)
  | evalZero {n : ℕ} {Γ : List (Cl n)} (h : Tm (n + 1)) {a t r : Tm n}
      (h₁ : KPrf Γ (.eq a t)) (h₂ : KPrf Γ (.eq (iter zero a h) r)) : KPrf Γ (.eq r t)
  | evalSucc {n : ℕ} {Γ : List (Cl n)} {c a : Tm n} {h : Tm (n + 1)} {t r : Tm n}
      (h₁ : KPrf Γ (.eq (iter c a h) t)) (h₂ : KPrf Γ (.eq (iter (succ c) a h) r)) :
      KPrf Γ (.eq r (Syn.subst (inst t) h))
  | use {n : ℕ} {Γ : List (Cl n)} {c : Cl n} (t : Tm n) (hc : c ∈ Γ) (h : KPrf Γ c.ante) :
      KPrf Γ (c.cons.subst (inst t))
  | elim {n : ℕ} {Γ : List (Cl n)} {B : NFm (n + 2)} {A : NFm n} (h₁ : KPrf Γ (.D B))
      (h₂ : KPrf (⟨B.subst (inst zero), B⟩ :: Γ.map Cl.shift) A.shift) : KPrf Γ A
  | intro {n : ℕ} {Γ : List (Cl n)} (B : NFm (n + 2)) (t : Tm n) (hB : B.QFree)
      (h : KPrf (Cl.asm ((B.subst (up (inst t))).subst (repl (NFm.dstart B)))
          :: Γ.map Cl.shift)
        ((B.subst (up (inst t))).subst (repl (succ (var 0))))) :
      KPrf Γ (.D B)

namespace KPrf

variable {Γ Δ : List (Cl n)} {A : NFm n}

theorem qfree (h : KPrf Γ A) : (∀ c ∈ Γ, c.ante.QFree ∧ c.cons.QFree) → A.QFree := by
  induction h with
  | refl t => exact fun _ => trivial
  | evalZero h _ _ _ _ => exact fun _ => trivial
  | evalSucc _ _ _ _ => exact fun _ => trivial
  | use t hc _ _ => exact fun hΓ => (NFm.qfree_subst _ _).2 (hΓ _ hc).2
  | @elim _ Γ B A _ _ ih₁ ih₂ =>
    intro hΓ
    have hB : B.QFree := ih₁ hΓ
    refine (NFm.qfree_subst A _).1 (ih₂ fun c hc => ?_)
    rcases List.mem_cons.1 hc with rfl | hc
    · exact ⟨(NFm.qfree_subst _ _).2 hB, hB⟩
    · obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
      exact ⟨(NFm.qfree_subst _ _).2 (hΓ d hd).1, (NFm.qfree_subst _ _).2 (hΓ d hd).2⟩
  | intro B t hB _ _ => exact fun _ => hB

theorem asmHyp {X : NFm n} (h : Cl.asm X ∈ Γ) : KPrf Γ X := by
  have k : KPrf Γ (X.shift.subst (inst zero)) := KPrf.use (c := Cl.asm X) zero h (.refl zero)
  rwa [NFm.subst_inst_shift] at k

/-! ### Structural rules -/

theorem weaken (h : KPrf Γ A) : ∀ {Δ : List (Cl n)}, Γ ⊆ Δ → KPrf Δ A := by
  induction h with
  | refl t => intro Δ _; exact .refl t
  | evalZero h _ _ ih₁ ih₂ => intro Δ s; exact .evalZero h (ih₁ s) (ih₂ s)
  | evalSucc _ _ ih₁ ih₂ => intro Δ s; exact .evalSucc (ih₁ s) (ih₂ s)
  | use t hc _ ih => intro Δ s; exact .use t (s hc) (ih s)
  | elim _ _ ih₁ ih₂ =>
    intro Δ s
    exact .elim (ih₁ s) (ih₂ (List.cons_subset_cons _ (List.map_subset _ s)))
  | intro B t hB _ ih =>
    intro Δ s
    exact .intro B t hB (ih (List.cons_subset_cons _ (List.map_subset _ s)))

theorem wk {c : Cl n} (h : KPrf Γ A) : KPrf (c :: Γ) A := h.weaken (List.subset_cons_self _ _)

/-- Substitution of terms for the free variables of a derivation, by direct
induction. -/
theorem subst (h : KPrf Γ A) : ∀ {m : ℕ} (σ : Fin n → Tm m),
    KPrf (Γ.map fun c => c.subst σ) (A.subst σ) := by
  induction h with
  | refl t => intro m σ; exact .refl _
  | evalZero h _ _ ih₁ ih₂ =>
    intro m σ
    have h₂ := ih₂ σ
    rw [NFm.subst_eq, Tm.subst_iter] at h₂
    exact .evalZero _ (ih₁ σ) h₂
  | evalSucc _ _ ih₁ ih₂ =>
    intro m σ
    have h₁ := ih₁ σ
    have h₂ := ih₂ σ
    rw [NFm.subst_eq, Tm.subst_iter] at h₁ h₂
    rw [NFm.subst_eq, Syn.subst_subst_inst]
    exact .evalSucc h₁ h₂
  | @use _ Γ c t hc _ ih =>
    intro m σ
    rw [NFm.subst_inst]
    exact .use (c := c.subst σ) _
      (List.mem_map_of_mem (f := fun c : Cl _ => c.subst σ) hc) (ih σ)
  | @elim _ Γ B A _ _ ih₁ ih₂ =>
    intro m σ
    have h := ih₂ (up σ)
    rw [List.map_cons, Cl.map_shift_subst, NFm.shift_subst_up] at h
    refine .elim (B := B.subst (up (up σ))) (ih₁ σ) ?_
    have e : (⟨B.subst (inst zero), B⟩ : Cl _).subst (up σ)
        = ⟨(B.subst (up (up σ))).subst (inst zero), B.subst (up (up σ))⟩ := by
      show (⟨(B.subst (inst zero)).subst (up σ), _⟩ : Cl _) = _
      rw [NFm.subst_inst]
      rfl
    rw [e] at h
    exact h
  | @intro _ Γ B t hB _ ih =>
    intro m σ
    have h := ih (up σ)
    rw [List.map_cons, Cl.map_shift_subst, Cl.asm_subst, NFm.subst_repl_succ,
      NFm.subst_repl_up _ (NFm.dstart B) σ, NFm.subst_up_inst, ← NFm.dstart_subst] at h
    exact .intro _ _ ((NFm.qfree_subst _ _).2 hB) h

theorem shift (h : KPrf Γ A) : KPrf (Γ.map Cl.shift) A.shift := h.subst _

theorem cutLift (h : ∀ c ∈ Γ, c ∈ Δ ∨ ∃ X, c = Cl.asm X ∧ KPrf Δ X) (d : Cl (n + 1)) :
    ∀ c ∈ d :: Γ.map Cl.shift,
      c ∈ d :: Δ.map Cl.shift ∨ ∃ X, c = Cl.asm X ∧ KPrf (d :: Δ.map Cl.shift) X := by
  intro c hc
  rcases List.mem_cons.1 hc with rfl | hc
  · exact .inl List.mem_cons_self
  · obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.1 hc
    rcases h c₀ hc₀ with h' | ⟨X, rfl, hX⟩
    · exact .inl (List.mem_cons_of_mem _ (List.mem_map_of_mem h'))
    · exact .inr ⟨X.shift, Cl.asm_shift X, hX.shift.wk⟩

theorem cut (h : KPrf Γ A) : ∀ {Δ : List (Cl n)},
    (∀ c ∈ Γ, c ∈ Δ ∨ ∃ X, c = Cl.asm X ∧ KPrf Δ X) → KPrf Δ A := by
  induction h with
  | refl t => intro Δ _; exact .refl t
  | evalZero h _ _ ih₁ ih₂ => intro Δ s; exact .evalZero h (ih₁ s) (ih₂ s)
  | evalSucc _ _ ih₁ ih₂ => intro Δ s; exact .evalSucc (ih₁ s) (ih₂ s)
  | @use _ Γ c t hc _ ih =>
    intro Δ s
    rcases s c hc with h' | ⟨X, rfl, hX⟩
    · exact .use t h' (ih s)
    · show KPrf Δ (X.shift.subst (inst t))
      rw [NFm.subst_inst_shift]
      exact hX
  | elim _ _ ih₁ ih₂ => intro Δ s; exact .elim (ih₁ s) (ih₂ (cutLift s _))
  | intro B t hB _ ih => intro Δ s; exact .intro B t hB (ih (cutLift s _))

/-! ### Equality, and the base of a diagonal matrix -/

theorem evalId {s t r : Tm n} (h₁ : KPrf Γ (.eq s t)) (h₂ : KPrf Γ (.eq s r)) :
    KPrf Γ (.eq r t) :=
  .evalZero (Syn.var 0) h₁ (.evalZero (Syn.var 0) h₂ (.refl _))

theorem eqSymm {s t : Tm n} (h : KPrf Γ (.eq s t)) : KPrf Γ (.eq t s) := evalId (.refl s) h

theorem eqTrans {s t u : Tm n} (h₁ : KPrf Γ (.eq s t)) (h₂ : KPrf Γ (.eq t u)) :
    KPrf Γ (.eq s u) :=
  evalId h₂ (eqSymm h₁)

theorem iterZero (a : Tm n) (h : Tm (n + 1)) : KPrf Γ (.eq (iter zero a h) a) :=
  .evalZero h (.refl a) (.refl _)

theorem diagTermZero {Γ : List (Cl (n + 1))} {s : Tm (n + 1)} (hs : s.isDiag = true) :
    KPrf Γ (.eq (Syn.subst (repl zero) s) zero) := by
  cases s with
  | var i => exact Bool.noConfusion hs
  | zero => exact Bool.noConfusion hs
  | succ t => exact Bool.noConfusion hs
  | iter c a h =>
    have hc : c.isV0 = true ∧ a.isV0 = true := by simpa [Tm.isDiag] using hs
    rw [Tm.eq_var0 hc.1, Tm.eq_var0 hc.2]
    exact iterZero zero _

/-- The base of a diagonal matrix is a theorem. -/
theorem diagBase {Γ : List (Cl (n + 1))} {X : NFm (n + 1)} (hX : X.isDiag = true) :
    KPrf Γ (X.subst (repl zero)) := by
  cases X with
  | eq s₁ s₂ =>
    have h : s₁.isDiag = true ∧ s₂.isDiag = true := by simpa [NFm.isDiag] using hX
    exact eqTrans (diagTermZero h.1) (eqSymm (diagTermZero h.2))
  | Q B => exact Bool.noConfusion hX
  | D B => exact Bool.noConfusion hX

/-! ### Soundness in the kernel -/

theorem toNPrf (h : KPrf Γ A) : NPrf (Γ.map Cl.toN) A := by
  induction h with
  | refl t => exact NPrf.eqRefl t
  | evalZero h _ _ ih₁ ih₂ =>
    exact NPrf.eqTrans (NPrf.eqSymm ih₂) (NPrf.eqTrans (.iterZero _ h) ih₁)
  | @evalSucc _ _ c a h t r _ _ ih₁ ih₂ =>
    exact NPrf.eqTrans (NPrf.eqSymm ih₂) (NPrf.eqTrans (.iterSucc c a h) (NPrf.eqCongr h ih₁))
  | @use _ Γ c t hc _ ih =>
    exact NPrf.allE t (NPrf.impE (.hyp (List.mem_map_of_mem (f := Cl.toN) hc)) ih)
  | @elim _ Γ B A _ _ ih₁ ih₂ =>
    rw [List.map_cons, Cl.map_toN_shift] at ih₂
    refine .dE ih₁ (NPrf.cut1 ((NPrf.qComp (NEquiv.refl B)).mpr NPrf.hyp0) (NPrf.wkUnder ih₂))
  | @intro _ Γ B t _ _ ih =>
    rw [List.map_cons, Cl.map_toN_shift] at ih
    exact .ofDIG B t (NPrf.cut1 (NPrf.asmClause NPrf.hyp0) (NPrf.wkUnder ih))

end KPrf

/-! ### Completeness, from the six-rule calculus with the diagonal introduction -/

theorem SPrf.toKPrf {Γ : List (NFm n)} {A : NFm n} (h : SPrf Γ A) :
    KPrf (Γ.map fun X => Cl.asm (NFm.unQ X)) (NFm.unQ A) := by
  induction h with
  | hyp h =>
    exact KPrf.asmHyp (List.mem_map_of_mem (f := fun X => Cl.asm (NFm.unQ X)) h)
  | refl t => exact .refl t
  | evalZero h _ _ ih₁ ih₂ => exact .evalZero h ih₁ ih₂
  | evalSucc _ _ ih₁ ih₂ => exact .evalSucc ih₁ ih₂
  | @qE _ Γ B t _ _ ih₁ ih₂ =>
    rw [NFm.unQ_subst] at ih₂ ⊢
    refine .elim ih₁ ?_
    have hp := (ih₂.shift).wk
      (c := (⟨((NFm.unQ B).subst (up fun i => Syn.var i.succ)).subst (inst zero),
        (NFm.unQ B).subst (up fun i => Syn.var i.succ)⟩ : Cl _))
    rw [NFm.shift_subst_inst_zero, ← NFm.subst_dummy_up_inst] at hp
    have hu : KPrf (_ :: (Γ.map fun X => Cl.asm (NFm.unQ X)).map Cl.shift)
        (((NFm.unQ B).subst (up fun i => Syn.var i.succ)).subst (inst (Syn.shift t))) :=
      KPrf.use (c := ⟨_, _⟩) (Syn.shift t) List.mem_cons_self hp
    rw [NFm.subst_dummy_up_inst _ (Syn.shift t), ← NFm.shift_subst_inst] at hu
    exact hu
  | @dE _ Γ B A _ _ ih₁ ih₂ =>
    rw [List.map_cons, Cl.map_asm_unQ_shift, NFm.unQ_shift] at ih₂
    refine .elim ih₁ ?_
    have hD : KPrf ((⟨(NFm.unQ B).subst (inst zero), NFm.unQ B⟩ : Cl _)
          :: (Γ.map fun X => Cl.asm (NFm.unQ X)).map Cl.shift)
        (.D ((NFm.unQ B).subst (up fun i => Syn.var i.succ))) := by
      refine .intro _ zero ((NFm.qfree_subst _ _).2 (NFm.qfree_unQ B)) ?_
      rw [NFm.subst_dummy_inst]
      -- the base, in whichever mode the matrix dictates
      have hb : KPrf (Cl.asm ((NFm.unQ B).subst
              (repl (NFm.dstart ((NFm.unQ B).subst (up fun i => Syn.var i.succ)))))
            :: ((⟨(NFm.unQ B).subst (inst zero), NFm.unQ B⟩ : Cl _)
              :: (Γ.map fun X => Cl.asm (NFm.unQ X)).map Cl.shift).map Cl.shift)
          ((NFm.unQ B).subst (inst zero)).shift := by
        rw [NFm.shift_subst_inst_zero]
        by_cases hd : ((NFm.unQ B).subst (up fun i => Syn.var i.succ)).isDiag = true
        · exact KPrf.diagBase (by rwa [NFm.isDiag_subst_up] at hd)
        · have k := KPrf.asmHyp (Γ := Cl.asm ((NFm.unQ B).subst
              (repl (NFm.dstart ((NFm.unQ B).subst (up fun i => Syn.var i.succ)))))
            :: ((⟨(NFm.unQ B).subst (inst zero), NFm.unQ B⟩ : Cl _)
              :: (Γ.map fun X => Cl.asm (NFm.unQ X)).map Cl.shift).map Cl.shift)
            List.mem_cons_self
          rw [NFm.dstart, if_neg hd] at k ⊢
          exact k
      have hu : KPrf (Cl.asm ((NFm.unQ B).subst
              (repl (NFm.dstart ((NFm.unQ B).subst (up fun i => Syn.var i.succ)))))
            :: ((⟨(NFm.unQ B).subst (inst zero), NFm.unQ B⟩ : Cl _)
              :: (Γ.map fun X => Cl.asm (NFm.unQ X)).map Cl.shift).map Cl.shift)
          (((NFm.unQ B).subst (up fun i => Syn.var i.succ)).subst
            (inst (succ (Syn.var 0)))) :=
        KPrf.use (c := (⟨(NFm.unQ B).subst (inst zero), NFm.unQ B⟩ : Cl _).shift)
          (succ (Syn.var 0)) (List.mem_cons_of_mem _ List.mem_cons_self) hb
      rwa [NFm.subst_dummy_up_inst _ (succ (Syn.var 0))] at hu
    refine ih₂.cut fun c hc => ?_
    rcases List.mem_cons.1 hc with rfl | hc
    · exact .inr ⟨_, rfl, hD⟩
    · exact .inl (List.mem_cons_of_mem _ hc)
  | @dI _ Γ B t _ ih =>
    rw [List.map_cons, Cl.map_asm_unQ_shift] at ih
    simp only [NFm.unQ_subst] at ih
    refine .intro (NFm.unQ B) t (NFm.qfree_unQ B) ?_
    rw [NFm.dstart_unQ]
    exact ih

variable {Γ : List (NFm n)} {A : NFm n}

/-- **Five rules, closed under substitution, and the kernel.** -/
theorem kprf_iff_nprf : KPrf (Γ.map fun X => Cl.asm (NFm.unQ X)) (NFm.unQ A) ↔ NPrf Γ A := by
  refine ⟨fun h => (NEquiv.unQ A).mp (h.toNPrf.cut fun C hC => ?_),
    fun h => (SPrf.ofGPrf h.toGPrf).toKPrf⟩
  rw [List.map_map, List.mem_map] at hC
  obtain ⟨X, hX, rfl⟩ := hC
  exact NPrf.asmClause ((NEquiv.unQ X).mpr (.hyp hX))

/-- On `Q`-free sequents `KPrf` derives exactly what the kernel derives. -/
theorem kprf_iff_nprf_of_qfree (hΓ : ∀ X ∈ Γ, X.QFree) (hA : A.QFree) :
    KPrf (Γ.map Cl.asm) A ↔ NPrf Γ A := by
  have e : (Γ.map fun X => Cl.asm (NFm.unQ X)) = Γ.map Cl.asm :=
    List.map_congr_left fun X hX => by rw [NFm.unQ_of_qfree X (hΓ X hX)]
  rw [← kprf_iff_nprf, e, NFm.unQ_of_qfree A hA]

end LeanProofs.ConciseIPRA
