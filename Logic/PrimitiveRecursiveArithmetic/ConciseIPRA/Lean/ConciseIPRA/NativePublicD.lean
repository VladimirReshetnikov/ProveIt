import ConciseIPRA.NativePublic

/-!
# A public language without `Q`

In the guarded packages a public formula is built from equations and the
paired binder `D` only; `Q` is an administrative resource that appears in
contexts, never in a goal.  `NativePublic` keeps `Q` as a formula.  This
module removes it.

`NFm.pubD` translates a native formula into one that has no `Q`:

* an equation `s = t` becomes `D_{x,y} (I(y, 0; u.s) = I(y, 0; u.t))`, the
  paired closure of its gate, with `x` unused;
* `Q_y B` becomes `D_{x,y} B'` with `x` unused, where `B'` is the translation
  of `B`;
* `D_{x,y} B` becomes `D_{x,y} B'`.

Every atomic matrix of a translated formula is guarded
(`NFm.pubD_guarded`), no `Q` occurs in it (`NFm.pubD_noQ`), and it is
interderivable with the original formula in the kernel (`NEquiv.pubD`).

* `pgprf_pubD_iff`: `PGPrf (Γ.map pubD) (pubD A) ↔ NPrf Γ A`.

So the calculus with the root-determined introduction and transport at
iterator sources only is equivalent to the kernel on the language of the
packages: paired binders over guarded equations.  `Q` still occurs in the
contexts of derivations, as the hypothesis that `DE` introduces.

The proof follows `NPrf.toPG`.  A paired closure with an unused witness is
opened by `DE` and closed by the introduction at the witness `0`
(`PGPrf.dumE`, `PGPrf.dumI`, `PGPrf.atomE`, `PGPrf.atomI`).
-/

namespace LeanProofs.ConciseIPRA

open Syn
open scoped Fm
open Tm (zero succ iter)

variable {n m : ℕ}

namespace NFm

theorem subst_up_dummy (X : NFm (n + 1)) (σ : Fin n → Tm m) :
    (X.subst (up σ)).subst (up fun i => Syn.var i.succ)
      = (X.subst (up fun i => Syn.var i.succ)).subst (up (up σ)) := by
  rw [subst_subst, subst_subst]
  refine X.subst_ext fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · simp only [up_succ, Syn.shift_var, Syn.subst_var, Syn.subst_up_shift]
    rfl

/-- The translation into the language of paired binders over guarded
equations. -/
def pubD : {n : ℕ} → NFm n → NFm n
  | _, .eq s t => .D (gate (Syn.var 0) (NFm.eq s t).shift.shift)
  | _, .Q B => .D ((pubD B).subst (up fun i => Syn.var i.succ))
  | _, .D B => .D (pubD B)

theorem pubD_subst (A : NFm n) : ∀ {m : ℕ} (σ : Fin n → Tm m),
    (A.subst σ).pubD = A.pubD.subst σ := by
  induction A with
  | eq s t =>
    intro m σ
    show NFm.D (gate (Syn.var 0) ((NFm.eq s t).subst σ).shift.shift)
      = (NFm.D (gate (Syn.var 0) (NFm.eq s t).shift.shift)).subst σ
    rw [subst_D, gate_subst, Syn.subst_var, Syn.up_zero, shift_subst_up, shift_subst_up]
  | Q B ih =>
    intro m σ
    show NFm.D (((B.subst (up σ)).pubD).subst (up fun i => Syn.var i.succ))
      = NFm.D ((B.pubD.subst (up fun i => Syn.var i.succ)).subst (up (up σ)))
    rw [ih, subst_up_dummy]
  | D B ih =>
    intro m σ
    show NFm.D ((B.subst (up (up σ))).pubD) = NFm.D (B.pubD.subst (up (up σ)))
    rw [ih]

theorem pubD_shift (A : NFm n) : A.shift.pubD = A.pubD.shift := pubD_subst A _

theorem map_pubD_shift (Γ : List (NFm n)) :
    (Γ.map NFm.shift).map pubD = (Γ.map pubD).map NFm.shift := by
  rw [List.map_map, List.map_map]
  exact List.map_congr_left fun A _ => pubD_shift A

theorem pubD_isEq (A : NFm n) : A.pubD.isEq = false := by
  cases A <;> rfl

theorem eta_pubD {k : ℕ} (A : NFm k) (a : Tm n) : eta A.pubD a = zero := by
  unfold eta
  rw [pubD_isEq]
  rfl

/-- The formula has no `Q`. -/
def NoQ : {n : ℕ} → NFm n → Prop
  | _, .eq _ _ => True
  | _, .Q _ => False
  | _, .D B => NoQ B

theorem NoQ.subst {A : NFm n} (h : A.NoQ) : ∀ {m : ℕ} (σ : Fin n → Tm m), (A.subst σ).NoQ := by
  induction A with
  | eq s t => intro m σ; exact trivial
  | Q B _ => exact False.elim h
  | D B ih => intro m σ; exact ih h _

/-- No `Q` occurs in a translated formula. -/
theorem pubD_noQ (A : NFm n) : A.pubD.NoQ := by
  induction A with
  | eq s t => exact trivial
  | Q B ih => exact ih.subst _
  | D B ih => exact ih

theorem _root_.LeanProofs.ConciseIPRA.Tm.IsIter.subst {t : Tm n} (h : t.IsIter)
    (σ : Fin n → Tm m) : (Syn.subst σ t).IsIter := by
  cases t with
  | var i => exact h.elim
  | zero => exact h.elim
  | succ t => exact h.elim
  | iter c a g => exact trivial

/-- The guarded shape is kept by a substitution that fixes the bound
variable. -/
theorem _root_.LeanProofs.ConciseIPRA.Tm.IsGuard.subst_up {t : Tm (n + 1)} (h : t.IsGuard)
    (σ : Fin n → Tm m) : (Syn.subst (up σ) t).IsGuard := by
  cases t with
  | var i => exact h.elim
  | zero => exact h.elim
  | succ t => exact h.elim
  | iter c a g =>
    cases c with
    | var i =>
      cases a with
      | zero =>
        have hi : i = 0 := Fin.ext h
        subst hi
        exact rfl
      | var j => exact h.elim
      | succ a => exact h.elim
      | iter c' a' g' => exact h.elim
    | zero => exact h.elim
    | succ c => exact h.elim
    | iter c' a' g' => exact h.elim

theorem Guarded.subst_up {B : NFm (n + 1)} (h : B.Guarded) (σ : Fin n → Tm m) :
    (B.subst (up σ)).Guarded := by
  cases B with
  | eq s t => exact ⟨h.1.subst_up σ, h.2.subst_up σ⟩
  | Q B' => exact h.elim
  | D B' => exact h.elim

/-- The public language over guarded matrices is closed under substitution. -/
theorem PublicBy.subst {A : NFm n} (h : A.PublicBy @Guarded) :
    ∀ {m : ℕ} (σ : Fin n → Tm m), (A.subst σ).PublicBy @Guarded := by
  induction A with
  | eq s t => intro m σ; exact ⟨h.1.subst σ, h.2.subst σ⟩
  | Q B ih =>
    intro m σ
    rcases h with h | ⟨h₁, h₂⟩
    · exact Or.inl (h.subst_up σ)
    · exact Or.inr ⟨by rw [isEq_subst]; exact h₁, ih h₂ _⟩
  | D B ih =>
    intro m σ
    rcases h with h | ⟨h₁, h₂⟩
    · exact Or.inl (h.subst_up (up σ))
    · exact Or.inr ⟨by rw [isEq_subst]; exact h₁, ih h₂ _⟩

/-- Every atomic matrix of a translated formula is guarded. -/
theorem pubD_guarded (A : NFm n) : A.pubD.PublicBy @Guarded := by
  induction A with
  | eq s t => exact Or.inl ⟨rfl, rfl⟩
  | Q B ih => exact Or.inr ⟨by rw [isEq_subst]; exact pubD_isEq B, ih.subst _⟩
  | D B ih => exact Or.inr ⟨pubD_isEq B, ih⟩

end NFm

/-- A formula is interderivable with its `Q`-free translation, in the kernel. -/
theorem NEquiv.pubD (A : NFm n) : NEquiv A.pubD A := by
  induction A with
  | eq s t => exact NEquiv.dGate (.eq s t)
  | Q B ih => exact (NEquiv.dDummy _).trans (NEquiv.Q ih)
  | D B ih => exact NEquiv.D ih

namespace PGPrf

variable {Γ : List (NFm n)}

/-- A paired closure with an unused witness gives the closure. -/
theorem dumE {X : NFm (n + 1)} (h : PGPrf Γ (.D (X.subst (up fun i => Syn.var i.succ)))) :
    PGPrf Γ (.Q X) := by
  refine .dE h ?_
  show PGPrf (.Q (X.subst (up fun i => Syn.var i.succ)) :: Γ.map NFm.shift)
    (.Q (X.subst (up fun i => Syn.var i.succ)))
  exact hyp0

/-- The closure of a compound matrix gives the paired closure with an unused
witness. -/
theorem dumI {X : NFm (n + 1)} (hX : X.isEq = false) (h : PGPrf Γ (.Q X)) :
    PGPrf Γ (.D (X.subst (up fun i => Syn.var i.succ))) := by
  refine .dI _ zero ?_
  have e : NFm.eta (X.subst (up fun i => Syn.var i.succ)) (Syn.var 0 : Tm (n + 1)) = zero := by
    unfold NFm.eta
    rw [NFm.isEq_subst, hX]
    rfl
  rw [e, NFm.subst_dummy_inst]
  exact qStep X h.shift.wk hyp0

/-- Opening the paired gate of an equation: the wrapped equation. -/
theorem atomE {s t : Tm n} (h : PGPrf Γ (NFm.eq s t).pubD) :
    PGPrf Γ (.eq (Tm.wr s) (Tm.wr t)) := by
  refine .dE h ?_
  have k := gateE (s := Syn.shift s) (t := Syn.shift t)
    (Γ := (NFm.Q (NFm.gate (Syn.var 0) (NFm.eq s t).shift.shift)) :: Γ.map NFm.shift) hyp0
  show PGPrf _ (.eq (Syn.shift (Tm.wr s)) (Syn.shift (Tm.wr t)))
  rw [Tm.shift_wr, Tm.shift_wr]
  exact k

/-- Closing a wrapped equation: the paired gate. -/
theorem atomI {s t : Tm n} (h : PGPrf Γ (.eq (Tm.wr s) (Tm.wr t))) :
    PGPrf Γ (NFm.eq s t).pubD := by
  have hQ := gateI h
  refine .dI _ zero ?_
  rw [show NFm.eta (NFm.gate (Syn.var 0) (NFm.eq s t).shift.shift) (Syn.var 0 : Tm (n + 1))
      = Syn.var 0 from rfl, NFm.subst_repl_var, NFm.gate_subst, Syn.subst_var, Syn.up_zero,
    NFm.shift_subst_up, NFm.subst_inst_shift]
  refine qStep _ hQ.shift.wk ?_
  rw [NFm.gate_shift_repl]
  exact gateZero _ _

end PGPrf

variable {Γ : List (NFm n)} {A : NFm n}

/-- Every kernel derivation becomes a derivation of `PGPrf` between the
`Q`-free translations. -/
theorem NPrf.toPGD (h : NPrf Γ A) : PGPrf (Γ.map NFm.pubD) A.pubD := by
  induction h with
  | hyp h => exact .hyp (List.mem_map_of_mem h)
  | iterZero a h => exact PGPrf.atomI (PGPrf.wrCong zero a h (.iterZero a h))
  | iterSucc c a h => exact PGPrf.atomI (PGPrf.wrCong (succ c) a h (.iterSucc c a h))
  | trOne h _ _ ih₁ ih₂ =>
    exact PGPrf.atomI (PGPrf.trW h (PGPrf.atomE ih₁) (PGPrf.atomE ih₂))
  | qE t _ _ ih₁ ih₂ =>
    rw [NFm.pubD_subst] at ih₂ ⊢
    exact .qE t (PGPrf.dumE ih₁) ih₂
  | @dE _ Γ B A _ _ ih₁ ih₂ =>
    rw [List.map_cons, NFm.map_pubD_shift, NFm.pubD_shift] at ih₂
    refine .dE ih₁ (ih₂.cut fun C hC => ?_)
    rcases List.mem_cons.1 hC with rfl | hC
    · exact PGPrf.dumI (NFm.pubD_isEq B) PGPrf.hyp0
    · exact .hyp (List.mem_cons_of_mem _ hC)
  | @dICase _ Γ B t _ ih =>
    rw [List.map_cons, NFm.map_pubD_shift, NFm.pubD_shift] at ih
    simp only [NFm.pubD_subst] at ih
    refine .dI B.pubD t ?_
    rw [NFm.eta_pubD, ← NFm.shift_subst_inst_zero]
    exact ih
  | @qIInd n Γ s t _ ih =>
    rw [List.map_cons, NFm.map_pubD_shift, NFm.pubD_subst] at ih
    -- equation induction on the wrapped matrix
    have hM : PGPrf (Γ.map NFm.pubD) (.Q (.eq (Tm.wr s) (Tm.wr t))) := by
      refine PGPrf.qIProg _ _ ?_
      have c := ih.cut
        (Δ := NFm.eq (Tm.wr s) (Tm.wr t) :: (Γ.map NFm.pubD).map NFm.shift)
        fun C hC => by
          rcases List.mem_cons.1 hC with rfl | hC
          · exact PGPrf.atomI PGPrf.hyp0
          · exact .hyp (List.mem_cons_of_mem _ hC)
      rw [← NFm.pubD_subst] at c
      have c' : PGPrf (NFm.eq (Tm.wr s) (Tm.wr t) :: (Γ.map NFm.pubD).map NFm.shift)
          (.eq (Tm.wr (Syn.subst (repl (succ (Syn.var 0))) s))
            (Tm.wr (Syn.subst (repl (succ (Syn.var 0))) t))) := PGPrf.atomE c
      show PGPrf _ (.eq (Syn.subst (repl (succ (Syn.var 0))) (Tm.wr s))
        (Syn.subst (repl (succ (Syn.var 0))) (Tm.wr t)))
      rw [Tm.subst_wr, Tm.subst_wr]
      exact c'
    -- the closure of the translated matrix, by cases, then the unused witness
    refine PGPrf.dumI (NFm.pubD_isEq _) (PGPrf.qICases _ (NFm.pubD_isEq _) ?_)
    rw [← NFm.pubD_subst, ← NFm.pubD_subst, ← NFm.pubD_shift]
    have b : PGPrf ((((NFm.eq s t).subst (inst zero)).shift.pubD)
          :: (Γ.map NFm.pubD).map NFm.shift)
        (.eq (Tm.wr (Syn.shift (Syn.subst (inst zero) s)))
          (Tm.wr (Syn.shift (Syn.subst (inst zero) t)))) := PGPrf.atomE PGPrf.hyp0
    have h0 : PGPrf ((((NFm.eq s t).subst (inst zero)).shift.pubD)
          :: (Γ.map NFm.pubD).map NFm.shift)
        ((NFm.eq (Tm.wr s) (Tm.wr t)).subst (repl zero)) := by
      rw [← NFm.shift_subst_inst_zero]
      show PGPrf _ (.eq (Syn.shift (Syn.subst (inst zero) (Tm.wr s)))
        (Syn.shift (Syn.subst (inst zero) (Tm.wr t))))
      rw [Tm.subst_wr, Tm.subst_wr, Tm.shift_wr, Tm.shift_wr]
      exact b
    have r : PGPrf ((((NFm.eq s t).subst (inst zero)).shift.pubD)
          :: (Γ.map NFm.pubD).map NFm.shift)
        (.eq (Syn.subst (repl (succ (Syn.var 0))) (Tm.wr s))
          (Syn.subst (repl (succ (Syn.var 0))) (Tm.wr t))) :=
      PGPrf.qStep (.eq (Tm.wr s) (Tm.wr t)) hM.shift.wk h0
    rw [Tm.subst_wr, Tm.subst_wr] at r
    exact PGPrf.atomI r

/-- **A public language without `Q`.**  On formulas built from paired binders
over guarded equations, the calculus with the root-determined introduction
and transport at iterator sources only derives the translation of a sequent
exactly when the kernel derives the sequent. -/
theorem pgprf_pubD_iff : PGPrf (Γ.map NFm.pubD) A.pubD ↔ NPrf Γ A :=
  ⟨fun h => (NEquiv.pubD A).mp (h.toNPrf.cut fun B hB => by
      obtain ⟨C, hC, rfl⟩ := List.mem_map.1 hB
      exact (NEquiv.pubD C).mpr (.hyp hC)), NPrf.toPGD⟩

/-- The same calculus derives the `Q`-free translation of a sequent exactly
when iPRA proves its reading. -/
theorem pgprf_pubD_iff_pra :
    PGPrf (Γ.map NFm.pubD) A.pubD ↔ (Γ.map NFm.toPRA ⊢[PRAAx] A.toPRA) :=
  pgprf_pubD_iff.trans native_iff_pra

end LeanProofs.ConciseIPRA
