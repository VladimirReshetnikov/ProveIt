import ConciseIPRA.NativeOpenClauses

/-!
# Three rule families with clauses and a deterministic discharge

`XCPrf` is the calculus of the packages `Research/first_instance` and
`Research/clause_discharge` in their own form.  Formulas, clauses and the
fixed reflexivity clause are those of `NativeNameClauses`.  There are three
rule families:

* **Use** and **Intro**, as in `NativeNameClauses`;
* **Discharge**: from `D_{x,y} B` and one derivation of `F` under the clause
  `[B(b, 0); y.B(b, y)]` with `b` fresh, infer the full normal form of
  `F[r/b]`, which must not mention `b`.  The term `r` is read off two rows of
  the matrix: if `B(b, 0)` is literally `0 = 0` and `B(b, 1)` is literally
  `b = r`, then `r` is that term, and otherwise `r` is `b` (`NFm.owit`).

Compared with Name there is no supplied term and no premise `b = t`.  Compared
with Open (`NativeOpenClauses`) the clause is opened at the fresh variable and
the selected witness is substituted in the exported formula.

* `XCPrf.qfree`: from `Q`-free clauses only `Q`-free formulas are derivable;
* `xcprf_iff_nprf`: the kernel derives a sequent exactly when `XCPrf` derives
  the full normal form of its `Q`-free form from the reflexivity clause and
  the corresponding assumptions;
* `xcprf_iff_nprf_of_qfree`, `xcprf_iff_pra`.

Soundness: Discharge is Name at the selected witness, whose equation `b = r`
is the second row of the clause (`XCPrf.toWD`).  Completeness: when the
exported formula does not mention `b`, the substitution does nothing, so the
ordinary elimination of `D` is a derived rule (`XCPrf.dE`), and the six-rule
calculus `F6Prf` is translated rule by rule (`F6Prf.toXC`).  Transport is the
packet of `NativeOpenClauses`: its rows at `b` select `T`, and the row
`H(b) = U` is exported as `H(T) = U`.
-/

namespace LeanProofs.ConciseIPRA

open Syn
open scoped Fm
open Tm (zero succ iter)

variable {n m : ℕ}

theorem NFm.shift_subst_repl (A : NFm n) (w : Tm (n + 1)) : A.shift.subst (repl w) = A.shift := by
  unfold NFm.shift
  rw [NFm.subst_subst]
  exact A.subst_ext fun i => by simp

/-- Derivability with Use, Intro and Discharge on full normal forms. -/
inductive XCPrf : {n : ℕ} → List (UCl n) → NFm n → Prop
  /-- Use: from the antecedent of a clause, if it has one, infer the full
  normal form of an instance of its consequent. -/
  | use {n : ℕ} {Γ : List (UCl n)} {c : UCl n} (t : Tm n) (hc : c ∈ Γ)
      (h : ∀ A, c.ante = some A → XCPrf Γ A) : XCPrf Γ (c.cons.subst (inst t)).full
  /-- Intro: from `B(t, η) ⊢ B(t, S z)` with `z` fresh infer `D_{x,y} B`. -/
  | intro {n : ℕ} {Γ : List (UCl n)} (B : NFm (n + 2)) (t : Tm n) (hB : B.full = B)
      (hQ : B.QFree) (ht : t.full = t)
      (h : XCPrf (UCl.asm ((B.subst (up (inst t))).subst (repl (NFm.start B t))).full
          :: Γ.map UCl.shift)
        ((B.subst (up (inst t))).subst (repl (succ (var 0)))).full) :
      XCPrf Γ (.D B)
  /-- Discharge: from `D_{x,y} B` and `F` under the clause `[B(b, 0); y.B(b, y)]`
  with `b` fresh, infer `F[r/b]`, which does not mention `b`, where `r` is the
  witness read off the rows of `B`. -/
  | dis {n : ℕ} {Γ : List (UCl n)} {B : NFm (n + 2)} {A : NFm n} (F : NFm (n + 1))
      (h₁ : XCPrf Γ (.D B)) (h₂ : XCPrf (UCl.clo B :: Γ.map UCl.shift) F)
      (hA : (F.subst (repl (NFm.owit B))).full = A.shift) : XCPrf Γ A

namespace XCPrf

variable {Γ Δ : List (UCl n)} {A : NFm n}

/-- From `Q`-free clauses only `Q`-free formulas are derivable. -/
theorem qfree (h : XCPrf Γ A) :
    (∀ c ∈ Γ, (∀ X, c.ante = some X → X.QFree) ∧ c.cons.QFree) → A.QFree := by
  induction h with
  | use t hc _ _ =>
    exact fun hΓ => (NFm.qfree_full _).2 ((NFm.qfree_subst _ _).2 (hΓ _ hc).2)
  | intro B t hB hQ ht _ _ => exact fun _ => hQ
  | @dis _ Γ B A F _ _ hA ih₁ ih₂ =>
    intro hΓ
    have hB : B.QFree := ih₁ hΓ
    have hF : F.QFree := ih₂ fun c hc => by
      rcases List.mem_cons.1 hc with rfl | hc
      · refine ⟨fun X hX => ?_, hB⟩
        have e : (B.subst (inst zero)).full = X := Option.some.inj hX
        rw [← e]
        exact (NFm.qfree_full _).2 ((NFm.qfree_subst _ _).2 hB)
      · obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
        refine ⟨fun X hX => ?_, (NFm.qfree_subst _ _).2 (hΓ d hd).2⟩
        obtain ⟨X₀, hX₀, rfl⟩ := Option.map_eq_some_iff.1 hX
        exact (NFm.qfree_subst _ _).2 ((hΓ d hd).1 X₀ hX₀)
    have k := (NFm.qfree_full _).2 ((NFm.qfree_subst F (repl (NFm.owit B))).2 hF)
    rw [hA] at k
    exact (NFm.qfree_subst A _).1 k

/-- Reflexivity, by the fixed clause. -/
theorem refl (hr : UCl.refl ∈ Γ) (t : Tm n) : XCPrf Γ (.eq t.full t.full) :=
  XCPrf.use (c := UCl.refl) t hr (fun A hA => by cases hA)

/-- An ordinary assumption of the context holds. -/
theorem asmHyp {X : NFm n} (hX : X.full = X) (h : UCl.asm X ∈ Γ) : XCPrf Γ X := by
  have k := XCPrf.use (c := UCl.asm X) zero h (fun A hA => by cases hA)
  have e : ((UCl.asm X).cons.subst (inst zero)).full = X := by
    show (X.shift.subst (inst zero)).full = X
    rw [NFm.subst_inst_shift, hX]
  rwa [e] at k

/-! ### Structural rules -/

theorem weaken (h : XCPrf Γ A) : ∀ {Δ : List (UCl n)}, Γ ⊆ Δ → XCPrf Δ A := by
  induction h with
  | use t hc _ ih => intro Δ s; exact .use t (s hc) fun A hA => ih A hA s
  | intro B t hB hQ ht _ ih =>
    intro Δ s
    exact .intro B t hB hQ ht (ih (List.cons_subset_cons _ (List.map_subset _ s)))
  | dis F _ _ hA ih₁ ih₂ =>
    intro Δ s
    exact .dis F (ih₁ s) (ih₂ (List.cons_subset_cons _ (List.map_subset _ s))) hA

theorem wk {c : UCl n} (h : XCPrf Γ A) : XCPrf (c :: Γ) A :=
  h.weaken (List.subset_cons_self _ _)

/-- Renaming of the free variables of a derivation. -/
theorem ren (h : XCPrf Γ A) : ∀ {m : ℕ} (ξ : Fin n → Fin m),
    XCPrf (Γ.map fun c => c.subst fun i => (Syn.var (ξ i) : Tm m))
      (A.subst fun i => (Syn.var (ξ i) : Tm m)) := by
  induction h with
  | @use _ Γ c t hc _ ih =>
    intro m ξ
    rw [← NFm.full_rn _ ξ, NFm.subst_inst]
    refine .use (c := c.subst fun i => (Syn.var (ξ i) : Tm m)) _
      (List.mem_map_of_mem (f := fun c : UCl _ => c.subst fun i => (Syn.var (ξ i) : Tm m)) hc)
      fun A hA => ?_
    obtain ⟨A₀, hA₀, rfl⟩ := Option.map_eq_some_iff.1 hA
    exact ih A₀ hA₀ ξ
  | @intro _ Γ B t hB hQ ht _ ih =>
    intro m ξ
    have h := ih (Tm.upRen ξ)
    rw [List.map_cons, UCl.asm_subst, ← NFm.full_rn _ (Tm.upRen ξ),
      ← NFm.full_rn _ (Tm.upRen ξ), ← Tm.up_rn, UCl.map_shift_subst, NFm.subst_repl_succ,
      NFm.subst_repl_up _ (NFm.start B t), NFm.subst_up_inst, ← NFm.start_rn] at h
    refine .intro _ _ ?_ ((NFm.qfree_subst _ _).2 hQ) ?_ h
    · rw [Tm.up_rn ξ, Tm.up_rn, NFm.full_rn, hB]
    · rw [Tm.full_rn, ht]
  | @dis _ Γ B A F _ _ hA ih₁ ih₂ =>
    intro m ξ
    have h₂ := ih₂ (Tm.upRen ξ)
    rw [List.map_cons, UCl.clo_subst_rn, ← Tm.up_rn, UCl.map_shift_subst] at h₂
    refine .dis (F.subst (up fun i => (Syn.var (ξ i) : Tm m))) (ih₁ ξ) h₂ ?_
    rw [NFm.owit_rn, ← NFm.subst_repl_up, Tm.up_rn, NFm.full_rn, hA, ← Tm.up_rn,
      NFm.shift_subst_up]

theorem shift (h : XCPrf Γ A) : XCPrf (Γ.map UCl.shift) A.shift := h.ren Fin.succ

/-! ### Derived rules -/

/-- The ordinary elimination of `D`: when the exported formula does not mention
the fresh variable, the substitution of the selected witness does nothing. -/
theorem dE {B : NFm (n + 2)} (h₁ : XCPrf Γ (.D B))
    (h₂ : XCPrf (UCl.clo B :: Γ.map UCl.shift) A.shift) (hA : A.full = A) : XCPrf Γ A :=
  .dis A.shift h₁ h₂ (by rw [NFm.shift_subst_repl, NFm.full_shift, hA])

/-- Introduction of the `D` formula that stands for `Q`, by cases. -/
theorem qI (M : NFm (n + 1)) (hM : M.full = M) (hQ : M.QFree)
    (h : XCPrf (UCl.asm (M.subst (repl zero)).full :: Γ.map UCl.shift)
      (M.subst (repl (succ (Syn.var 0)))).full) :
    XCPrf Γ (.D (M.subst (up fun i => Syn.var i.succ))) := by
  refine .intro _ (succ zero) (by rw [NFm.full_dummy, hM]) ((NFm.qfree_subst _ _).2 hQ) rfl ?_
  rw [NFm.start_of_not (fun h => by cases h.2), NFm.subst_dummy_inst]
  exact h

/-- The closure clause of a matrix gives the `D` formula that stands for `Q`. -/
theorem ofClause (M : NFm (n + 1)) (hM : M.full = M) (hQ : M.QFree) (hc : UCl.clo M ∈ Γ) :
    XCPrf Γ (.D (M.subst (up fun i => Syn.var i.succ))) := by
  refine qI M hM hQ ?_
  have ha : XCPrf (UCl.asm (M.subst (repl zero)).full :: Γ.map UCl.shift)
      (M.subst (inst zero)).full.shift := by
    rw [← NFm.full_shift, NFm.shift_subst_inst_zero]
    exact asmHyp (NFm.full_idem _) List.mem_cons_self
  have k : XCPrf (UCl.asm (M.subst (repl zero)).full :: Γ.map UCl.shift)
      ((M.subst (up fun i => Syn.var i.succ)).subst (inst (succ (Syn.var 0)))).full :=
    XCPrf.use (c := (UCl.clo M).shift)
      (succ (Syn.var 0)) (List.mem_cons_of_mem _ (List.mem_map_of_mem hc)) (fun A hA => by
        have e : (M.subst (inst zero)).full.shift = A := Option.some.inj hA
        rw [← e]
        exact ha)
  rwa [NFm.subst_dummy_up_inst _ (succ (Syn.var 0))] at k

/-- `QE`, for the `D` formula that stands for `Q`. -/
theorem qE (M : NFm (n + 1)) (t : Tm n)
    (h₁ : XCPrf Γ (.D (M.subst (up fun i => Syn.var i.succ))))
    (h₂ : XCPrf Γ (M.subst (inst zero)).full) : XCPrf Γ (M.subst (inst t)).full := by
  refine dE h₁ ?_ (NFm.full_idem _)
  have ha : XCPrf (UCl.clo (M.subst (up fun i => Syn.var i.succ)) :: Γ.map UCl.shift)
      ((M.subst (up fun i => Syn.var i.succ)).subst (inst zero)).full := by
    rw [NFm.subst_dummy_up_inst, ← NFm.shift_subst_inst_zero, NFm.full_shift]
    exact h₂.shift.wk
  have k : XCPrf (UCl.clo (M.subst (up fun i => Syn.var i.succ)) :: Γ.map UCl.shift)
      ((M.subst (up fun i => Syn.var i.succ)).subst (inst (Syn.shift t))).full :=
    XCPrf.use (c := UCl.clo _) (Syn.shift t) List.mem_cons_self (fun A hA => by
      have e : ((M.subst (up fun i => Syn.var i.succ)).subst (inst zero)).full = A :=
        Option.some.inj hA
      rw [← e]
      exact ha)
  rwa [NFm.subst_dummy_up_inst _ (Syn.shift t), ← NFm.shift_subst_inst, NFm.full_shift] at k

/-- Numerical cases, for a normal matrix. -/
theorem cases (M : NFm (n + 1)) (hM : M.full = M) (hQ : M.QFree) (t : Tm n)
    (h0 : XCPrf Γ (M.subst (inst zero)).full)
    (hS : XCPrf (UCl.asm (M.subst (repl zero)).full :: Γ.map UCl.shift)
      (M.subst (repl (succ (Syn.var 0)))).full) : XCPrf Γ (M.subst (inst t)).full :=
  qE M t (qI M hM hQ hS) h0

/-- **The packet with Discharge.**  Transport without the crossing: the rows of
the packet at a fresh `b` are `0 = 0` and `b = T`, so Discharge selects `T`,
and the row `H(b) = U` is exported as `H(T) = U`. -/
theorem packet (hr : UCl.refl ∈ Γ) (S T U : Tm n) (H : Tm (n + 1))
    (h₁ : XCPrf Γ (.eq S.full T.full))
    (h₂ : XCPrf Γ (.eq (Syn.subst (inst S) H).full U.full)) :
    XCPrf Γ (.eq (Syn.subst (inst T) H).full U.full) := by
  have row : ∀ c : Tm (n + 1), ((NFm.opkt H T U).full.subst (inst c)).full
      = ((NFm.opkt H T U).subst (inst c)).full := fun c =>
    NFm.full_subst_congr (NFm.full_idem _) fun _ => rfl
  have hD : XCPrf Γ (.D (NFm.opkt H T U).full) := by
    refine .intro _ S.full (NFm.full_idem _) trivial (Tm.full_idem _) ?_
    have eA : (((NFm.opkt H T U).full.subst (up (inst S.full))).subst
          (repl (succ (Syn.var 0)))).full
        = ((NFm.pktF (Syn.subst (inst S) H) U T S).full.subst
            (inst (Tm.npar (succ (Syn.var 0))))).full := by
      rw [NFm.full_subst_congr (A' := (NFm.opkt H T U).subst (up (inst S)))
          (σ' := repl (succ (Syn.var 0)))
          (NFm.full_subst_congr (NFm.full_idem _) (Tm.full_up_congr (Tm.full_inst S)))
          (fun _ => rfl),
        NFm.opkt_wit,
        NFm.full_subst_congr (A' := NFm.pktF (Syn.subst (inst S) H) U T S)
          (σ' := inst (Tm.npar (succ (Syn.var 0)))) (NFm.full_idem _) (fun _ => rfl),
        NFm.pktF_inst]
      show NFm.eq (Tm.full _) (Tm.full _) = NFm.eq (Tm.full _) (Tm.full _)
      rw [Tm.full_sel_succ' (c := succ (Syn.var 0)) (x := Syn.var 0) rfl,
        Tm.full_sel_succ' (c := succ (Syn.var 0)) (x := Syn.var 0) rfl]
    rw [eA]
    refine cases (NFm.pktF (Syn.subst (inst S) H) U T S).full (NFm.full_idem _) trivial _ ?_ ?_
    · rw [NFm.full_subst_congr (A' := NFm.pktF (Syn.subst (inst S) H) U T S) (σ' := inst zero)
        (NFm.full_idem _) (fun _ => rfl), NFm.pktF_zero]
      exact h₂.shift.wk
    · rw [NFm.full_subst_congr (A' := NFm.pktF (Syn.subst (inst S) H) U T S)
        (σ' := repl (succ (Syn.var 0))) (NFm.full_idem _) (fun _ => rfl), NFm.pktF_succ]
      exact h₁.shift.wk.shift.wk
  have hw : NFm.owit (NFm.opkt H T U).full = Syn.shift T.full :=
    NFm.owit_eq ⟨(row zero).trans (NFm.opkt_row0 H T U),
      (row (succ zero)).trans (NFm.opkt_row1 H T U)⟩
  have k : XCPrf (UCl.clo (NFm.opkt H T U).full :: Γ.map UCl.shift)
      ((NFm.opkt H T U).full.subst (inst (succ (succ zero)))).full :=
    XCPrf.use (c := UCl.clo _) (succ (succ zero)) List.mem_cons_self (fun A hA => by
      have e : ((NFm.opkt H T U).full.subst (inst zero)).full = A := Option.some.inj hA
      rw [← e, row, NFm.opkt_row0]
      exact XCPrf.refl (UCl.refl_mem_lift hr _) zero)
  rw [row, NFm.opkt_row2] at k
  refine .dis _ hD k ?_
  rw [hw, NFm.pkt_export]

/-- Symmetry: transport at the template `x`. -/
theorem symm (hr : UCl.refl ∈ Γ) {a c : Tm n} (h : XCPrf Γ (.eq a.full c.full)) :
    XCPrf Γ (.eq c.full a.full) :=
  packet hr a c a (Syn.var 0) h (XCPrf.refl hr a)

/-- Transport in one term, as in the kernel. -/
theorem trOne (hr : UCl.refl ∈ Γ) (S T U : Tm n) (H : Tm (n + 1))
    (h₁ : XCPrf Γ (.eq S.full T.full))
    (h₂ : XCPrf Γ (.eq (Syn.subst (inst S) H).full U.full)) :
    XCPrf Γ (.eq U.full (Syn.subst (inst T) H).full) :=
  symm hr (packet hr S T U H h₁ h₂)

/-! ### Soundness -/

/-- Discharge is Name at the selected witness: its equation is the second row
of the clause when the test succeeds, and reflexivity otherwise. -/
theorem toWD (h : XCPrf Γ A) : UCl.refl ∈ Γ → WDPrf Γ A := by
  induction h with
  | use t hc _ ih => exact fun hr => .use t hc fun A hA => ih A hA hr
  | intro B t hB hQ ht _ ih =>
    exact fun hr => .intro B t hB hQ ht (ih (UCl.refl_mem_lift hr _))
  | @dis _ Γ B A F _ _ hA ih₁ ih₂ =>
    intro hr
    have hr' := UCl.refl_mem_lift hr (UCl.clo B)
    refine .name F (NFm.owit B) (ih₁ hr) ?_ (ih₂ hr') hA
    by_cases h : ∃ r, NFm.OTest B r
    · obtain ⟨e0, e1⟩ := NFm.owit_spec h
      have k : WDPrf (UCl.clo B :: Γ.map UCl.shift) (B.subst (inst (succ zero))).full :=
        WDPrf.use (c := UCl.clo B) (succ zero) List.mem_cons_self (fun X hX => by
          have e : (B.subst (inst zero)).full = X := Option.some.inj hX
          rw [← e, e0]
          exact WDPrf.refl hr' zero)
      rwa [e1] at k
    · rw [NFm.owit_neg h]
      have r := WDPrf.refl hr' (Syn.var 0)
      rwa [Tm.full_var] at r

/-- The invariant of the translation from the six-rule calculus, under one more
variable and one more clause. -/
theorem lift {Γ : List (NFm n)} (s : ∀ X ∈ Γ, XCPrf Δ (NFm.unQ X).full) {X' : NFm (n + 1)}
    {c' : UCl (n + 1)} (h' : XCPrf (c' :: Δ.map UCl.shift) (NFm.unQ X').full) :
    ∀ X ∈ X' :: Γ.map NFm.shift, XCPrf (c' :: Δ.map UCl.shift) (NFm.unQ X).full := by
  intro X hX
  rcases List.mem_cons.1 hX with rfl | hX
  · exact h'
  · obtain ⟨X₀, hX₀, rfl⟩ := List.mem_map.1 hX
    rw [NFm.unQ_shift, NFm.full_shift]
    exact (s X₀ hX₀).shift.wk

end XCPrf

/-! ### Completeness, from the six-rule calculus -/

/-- Every derivation of the six-rule calculus on full normal forms, with
formulas as hypotheses and `Q` in the language, is a derivation with Use,
Intro and Discharge. -/
theorem F6Prf.toXC {Γ : List (NFm n)} {A : NFm n} (h : F6Prf Γ A) :
    ∀ {Δ : List (UCl n)}, UCl.refl ∈ Δ → (∀ X ∈ Γ, XCPrf Δ (NFm.unQ X).full) →
      XCPrf Δ (NFm.unQ A).full := by
  induction h with
  | hyp h => intro Δ _ sΓ; exact sΓ _ h
  | refl t =>
    intro Δ hr _
    show XCPrf Δ (.eq t.full.full t.full.full)
    rw [Tm.full_idem]
    exact XCPrf.refl hr t
  | @trOne _ Γ h s t u _ _ ih₁ ih₂ =>
    intro Δ hr sΓ
    have h₁ : XCPrf Δ (.eq s.full t.full) := ih₁ hr sΓ
    have h₂ : XCPrf Δ (.eq (Syn.subst (inst s) h).full.full u.full) := ih₂ hr sΓ
    rw [Tm.full_idem] at h₂
    show XCPrf Δ (.eq u.full (Syn.subst (inst t) h).full.full)
    rw [Tm.full_idem]
    exact XCPrf.trOne hr s t u h h₁ h₂
  | @qE _ Γ B t _ _ ih₁ ih₂ =>
    intro Δ hr sΓ
    have e : ∀ u : Tm _, (NFm.unQ (B.subst (inst u)).full).full
        = ((NFm.unQ B).full.subst (inst u)).full := fun u => by
      rw [NFm.unQ_full, NFm.full_idem, NFm.unQ_subst]
      exact NFm.full_subst_congr (NFm.full_idem _).symm fun _ => rfl
    have h₁ : XCPrf Δ (.D ((NFm.unQ B).full.subst (up fun i => Syn.var i.succ))) := by
      rw [← NFm.full_dummy]
      exact ih₁ hr sΓ
    rw [e]
    exact XCPrf.qE _ t h₁ (by rw [← e]; exact ih₂ hr sΓ)
  | @dE _ Γ B A _ _ ih₁ ih₂ =>
    intro Δ hr sΓ
    have h₁ : XCPrf Δ (.D (NFm.unQ B).full) := ih₁ hr sΓ
    refine XCPrf.dE h₁ ?_ (NFm.full_idem _)
    have k := ih₂ (Δ := UCl.clo (NFm.unQ B).full :: Δ.map UCl.shift) (UCl.refl_mem_lift hr _)
      (XCPrf.lift sΓ (X' := .Q B) (by
        show XCPrf _ (.D ((NFm.unQ B).subst (up fun i => Syn.var i.succ)).full)
        rw [NFm.full_dummy]
        exact XCPrf.ofClause _ (NFm.full_idem _)
          ((NFm.qfree_full _).2 (NFm.qfree_unQ B)) List.mem_cons_self))
    rwa [NFm.unQ_shift, NFm.full_shift] at k
  | @dI _ Γ B t hB ht _ ih =>
    intro Δ hr sΓ
    have hB' : (NFm.unQ B).full = NFm.unQ B := by rw [← NFm.unQ_full, hB]
    have e : ∀ {k : ℕ} (ρ : Fin _ → Tm k),
        (NFm.unQ ((B.subst (up (inst t))).subst ρ).full).full
          = (((NFm.unQ B).subst (up (inst t))).subst ρ).full := fun ρ => by
      rw [NFm.unQ_full, NFm.full_idem, NFm.unQ_subst, NFm.unQ_subst]
    show XCPrf Δ (.D (NFm.unQ B).full)
    rw [hB']
    refine .intro (NFm.unQ B) t hB' (NFm.qfree_unQ B) ht ?_
    rw [NFm.start_unQ]
    have k := ih (UCl.refl_mem_lift hr
        (UCl.asm (((NFm.unQ B).subst (up (inst t))).subst (repl (NFm.start B t))).full))
      (XCPrf.lift sΓ (by rw [e]; exact XCPrf.asmHyp (NFm.full_idem _) List.mem_cons_self))
    rwa [e] at k

variable {Γ : List (NFm n)} {A : NFm n}

/-- **Three rule families with a deterministic discharge.**  The kernel derives
a sequent exactly when Use, Intro and Discharge derive the full normal form of
its `Q`-free form from the reflexivity clause and the corresponding
assumptions. -/
theorem xcprf_iff_nprf :
    XCPrf (UCl.refl :: Γ.map fun X => UCl.asm (NFm.unQ X).full) (NFm.unQ A).full ↔ NPrf Γ A := by
  constructor
  · intro h
    exact wdprf_iff_nprf.1 (h.toWD List.mem_cons_self)
  · intro h
    have k := (f6prf_iff_nprf.2 h).toXC
      (Δ := UCl.refl :: Γ.map fun X => UCl.asm (NFm.unQ X).full) List.mem_cons_self
      fun Y hY => by
        obtain ⟨X, hX, rfl⟩ := List.mem_map.1 hY
        rw [NFm.unQ_full, NFm.full_idem]
        exact XCPrf.asmHyp (NFm.full_idem _) (List.mem_cons_of_mem _
          (List.mem_map_of_mem (f := fun X => UCl.asm (NFm.unQ X).full) hX))
    rwa [NFm.unQ_full, NFm.full_idem] at k

/-- On `Q`-free sequents Use, Intro and Discharge derive exactly what the kernel
derives, up to full normal forms. -/
theorem xcprf_iff_nprf_of_qfree (hΓ : ∀ X ∈ Γ, X.QFree) (hA : A.QFree) :
    XCPrf (UCl.refl :: Γ.map fun X => UCl.asm X.full) A.full ↔ NPrf Γ A := by
  have e : (Γ.map fun X => UCl.asm (NFm.unQ X).full) = Γ.map fun X => UCl.asm X.full :=
    List.map_congr_left fun X hX => by rw [NFm.unQ_of_qfree X (hΓ X hX)]
  rw [← xcprf_iff_nprf, e, NFm.unQ_of_qfree A hA]

/-- Use, Intro and Discharge prove a sequent in this form exactly when iPRA
proves its reading. -/
theorem xcprf_iff_pra :
    XCPrf (UCl.refl :: Γ.map fun X => UCl.asm (NFm.unQ X).full) (NFm.unQ A).full
      ↔ (Γ.map NFm.toPRA ⊢[PRAAx] A.toPRA) :=
  xcprf_iff_nprf.trans native_iff_pra

end LeanProofs.ConciseIPRA
