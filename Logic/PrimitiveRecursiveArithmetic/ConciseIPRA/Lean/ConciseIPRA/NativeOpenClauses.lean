import ConciseIPRA.NativeNameClauses
import ConciseIPRA.NativeModels

/-!
# Three rule families with clauses and an inferred witness

`OCPrf` is the calculus of the packages `Research/inferred_witness` and
`Research/deterministic_opening` in their own form.  Formulas are equations
and `D` over terms in full normal form, a context is a list of clauses with at
most one antecedent, and every context contains the fixed reflexivity clause.
There are three rule families:

* **Use** and **Intro**, as in `NativeNameClauses`;
* **Open**: from `D_{x,y} B` and a derivation of `A` under the clause
  `[B(r, 0); y.B(r, y)]`, infer `A`, where `r` is read off two rows of the
  matrix at a fresh `b`: if `B(b, 0)` is literally `0 = 0` and `B(b, 1)` is
  literally `b = r`, then `r` is that term, and otherwise `r` is `b`
  (`NFm.owit`, `NativeInferredWitness`).

No replacement term and no equality proof are supplied, and there is no
transport rule, no computation rule and no `Q`.

* `OCPrf.qfree`: from `Q`-free clauses only `Q`-free formulas are derivable;
* `ocprf_iff_nprf`: the kernel derives a sequent exactly when `OCPrf` derives
  the full normal form of its `Q`-free form from the reflexivity clause and
  the corresponding assumptions;
* `ocprf_iff_nprf_of_qfree`, `ocprf_iff_pra`.

Soundness is `NPrf.owitQ`.  For completeness a kernel derivation is translated
under an arbitrary substitution (`NPrf.toOC`), since ordinary elimination of
`D` is not a derived rule: at `DE` the branch is translated under the
substitution that sends the fresh variable to the selected witness.  The rules
of the kernel are recovered as follows.

* Transport.  The packet `NFm.opkt` has the rows `0 = 0`, `x = T` and
  `H(x) = U`.  It is introduced at the witness `S` from `S = T` and
  `H(S) = U`; at a fresh `b` its first two rows are literally `0 = 0` and
  `b = T`, so Open selects `T`, and the third row of the opened clause is
  `H(T) = U` (`OCPrf.packet`).  Symmetry is the instance at the template `x`.
* `QE`.  `Q_y M` is `D_{x,y} M` with `x` unused; no row of such a matrix is
  `b = r`, so Open is the ordinary opening (`NFm.not_otest_dummy`,
  `OCPrf.qE`).
* `DI` by cases for an equation at the literal `0`, where Intro takes the
  progress step, uses the matrix `B(tz(x), y)` with the neutral term
  `tz(x) = I(x, 0; u.0)`.  The test fails on it, which is proved by evaluation
  in the natural numbers: the value of `tz(x)` is `0` for every `x`, so the
  value of a row does not depend on `x`, and the row is not `x = r`
  (`NFm.not_otest_tz`).
* `QI` by progress is one Intro at the literal `0`.

Renaming of derivations is a direct induction, because the selected witness
commutes with renaming (`NFm.owit_rn`).
-/

namespace LeanProofs.ConciseIPRA

open Syn
open scoped Fm
open Tm (zero succ iter)

variable {n m : ℕ}

namespace Tm

theorem rn_eq_zero {a : Tm n} {ξ : Fin n → Fin m}
    (h : Syn.subst (fun i => (Syn.var (ξ i) : Tm m)) a = zero) : a = zero := by
  cases a with
  | var i => change Tm.var (ξ i) = Tm.zero at h; cases h
  | zero => rfl
  | succ t => change Tm.succ _ = Tm.zero at h; cases h
  | iter c a h' => change Tm.iter _ _ _ = Tm.zero at h; cases h

theorem uprn_eq_var {a : Tm (n + 1)} {ξ : Fin n → Fin m}
    (h : Syn.subst (fun i => (Syn.var (Tm.upRen ξ i) : Tm (m + 1))) a = Syn.var 0) :
    a = Syn.var 0 := by
  cases a with
  | var i =>
    change Tm.var (Tm.upRen ξ i) = Tm.var 0 at h
    have e := Tm.var.inj h
    revert e
    refine Fin.cases (fun _ => rfl) (fun j e => ?_) i
    rw [Tm.upRen_succ] at e
    exact absurd e (Fin.succ_ne_zero _)
  | zero => change Tm.zero = Tm.var 0 at h; cases h
  | succ t => change Tm.succ _ = Tm.var 0 at h; cases h
  | iter c a h' => change Tm.iter _ _ _ = Tm.var 0 at h; cases h

end Tm

namespace NFm

theorem rn_eq_eq {X : NFm n} {ξ : Fin n → Fin m} {a c : Tm m}
    (h : X.subst (fun i => (Syn.var (ξ i) : Tm m)) = .eq a c) :
    ∃ a' c', X = .eq a' c' ∧ Syn.subst (fun i => (Syn.var (ξ i) : Tm m)) a' = a
      ∧ Syn.subst (fun i => (Syn.var (ξ i) : Tm m)) c' = c := by
  cases X with
  | eq a' c' =>
    change NFm.eq (Syn.subst _ a') (Syn.subst _ c') = _ at h
    exact ⟨a', c', rfl, (NFm.eq.inj h).1, (NFm.eq.inj h).2⟩
  | Q B => change NFm.Q _ = _ at h; cases h
  | D B => change NFm.D _ = _ at h; cases h

/-- A row of a renamed matrix is the renamed row. -/
theorem full_row_rn (B : NFm (n + 2)) (ξ : Fin n → Fin m) (t : Tm (n + 1)) :
    ((B.subst (up (up fun i => (Syn.var (ξ i) : Tm m)))).subst
        (inst (Syn.subst (up fun i => (Syn.var (ξ i) : Tm m)) t))).full
      = (B.subst (inst t)).full.subst (up fun i => (Syn.var (ξ i) : Tm m)) := by
  rw [← NFm.subst_inst, Tm.up_rn, NFm.full_rn]

theorem OTest.rn {B : NFm (n + 2)} {r : Tm (n + 1)} (h : OTest B r) (ξ : Fin n → Fin m) :
    OTest (B.subst (up (up fun i => (Syn.var (ξ i) : Tm m))))
      (Syn.subst (up fun i => (Syn.var (ξ i) : Tm m)) r) := by
  have e0 := full_row_rn B ξ zero
  have e1 := full_row_rn B ξ (succ zero)
  rw [h.1] at e0
  rw [h.2] at e1
  exact ⟨e0, e1⟩

theorem OTest.of_rn {B : NFm (n + 2)} {ξ : Fin n → Fin m} {r' : Tm (m + 1)}
    (h : OTest (B.subst (up (up fun i => (Syn.var (ξ i) : Tm m)))) r') : ∃ r, OTest B r := by
  have e0 := (full_row_rn B ξ zero).symm.trans h.1
  have e1 := (full_row_rn B ξ (succ zero)).symm.trans h.2
  rw [Tm.up_rn] at e0 e1
  obtain ⟨a₀, c₀, hX₀, ha₀, hc₀⟩ := rn_eq_eq e0
  obtain ⟨a₁, c₁, hX₁, ha₁, -⟩ := rn_eq_eq e1
  refine ⟨c₁, ?_, ?_⟩
  · rw [hX₀, Tm.rn_eq_zero ha₀, Tm.rn_eq_zero hc₀]
  · rw [hX₁, Tm.uprn_eq_var ha₁]

/-- The selected witness is determined by the rows. -/
theorem owit_eq {B : NFm (n + 2)} {r : Tm (n + 1)} (h : OTest B r) : owit B = r :=
  (NFm.eq.inj ((owit_spec ⟨r, h⟩).2.symm.trans h.2)).2

/-- The selected witness commutes with renaming. -/
theorem owit_rn (B : NFm (n + 2)) (ξ : Fin n → Fin m) :
    owit (B.subst (up (up fun i => (Syn.var (ξ i) : Tm m))))
      = Syn.subst (up fun i => (Syn.var (ξ i) : Tm m)) (owit B) := by
  by_cases h : ∃ r, OTest B r
  · exact owit_eq ((owit_spec h).rn ξ)
  · rw [owit_neg h, owit_neg fun ⟨r', h'⟩ => h h'.of_rn]
    simp

/-- The matrix at the selected witness, as a full normal form. -/
noncomputable def osel (B : NFm (n + 2)) : NFm (n + 2) := (B.subst (up (repl (owit B)))).full

theorem osel_neg {B : NFm (n + 2)} (h : ¬∃ r, OTest B r) : osel B = B.full := by
  rw [osel, owit_neg h, show (repl (Syn.var 0) : Fin (n + 1) → Tm (n + 1)) = Syn.var from
    funext fun i => by refine Fin.cases ?_ (fun j => ?_) i <;> simp, Syn.up_var, NFm.subst_id]

theorem osel_rn (B : NFm (n + 2)) (ξ : Fin n → Fin m) :
    osel (B.subst (up (up fun i => (Syn.var (ξ i) : Tm m))))
      = (osel B).subst (up (up fun i => (Syn.var (ξ i) : Tm m))) := by
  have e : (B.subst (up (repl (owit B)))).subst (up (up fun i => (Syn.var (ξ i) : Tm m)))
      = (B.subst (up (up fun i => (Syn.var (ξ i) : Tm m)))).subst
          (up (repl (Syn.subst (up fun i => (Syn.var (ξ i) : Tm m)) (owit B)))) := by
    rw [NFm.subst_subst, NFm.subst_subst, Syn.up_comp, Syn.up_comp]
    refine congrArg (fun r => B.subst (up r)) (funext fun i => ?_)
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · rw [repl_succ, Syn.subst_var, up_succ, Syn.subst_repl_shift]
  unfold osel
  rw [owit_rn, ← e, Tm.up_rn ξ, Tm.up_rn, NFm.full_rn]

end NFm

namespace UCl

/-- The closure clause `[M(0); y.M(y)]` of a matrix. -/
def clo (M : NFm (n + 1)) : UCl n := ⟨some (M.subst (inst zero)).full, M⟩

theorem clo_subst_rn (M : NFm (n + 1)) (ξ : Fin n → Fin m) :
    (clo M).subst (fun i => (Syn.var (ξ i) : Tm m))
      = clo (M.subst (up fun i => (Syn.var (ξ i) : Tm m))) := by
  show (⟨some ((M.subst (inst zero)).full.subst _), M.subst (up _)⟩ : UCl _) = _
  rw [← NFm.full_rn _ ξ, NFm.subst_inst]
  rfl

end UCl

/-- Derivability with Use, Intro and Open on full normal forms. -/
inductive OCPrf : {n : ℕ} → List (UCl n) → NFm n → Prop
  /-- Use: from the antecedent of a clause, if it has one, infer the full
  normal form of an instance of its consequent. -/
  | use {n : ℕ} {Γ : List (UCl n)} {c : UCl n} (t : Tm n) (hc : c ∈ Γ)
      (h : ∀ A, c.ante = some A → OCPrf Γ A) : OCPrf Γ (c.cons.subst (inst t)).full
  /-- Intro: from `B(t, η) ⊢ B(t, S z)` with `z` fresh infer `D_{x,y} B`. -/
  | intro {n : ℕ} {Γ : List (UCl n)} (B : NFm (n + 2)) (t : Tm n) (hB : B.full = B)
      (hQ : B.QFree) (ht : t.full = t)
      (h : OCPrf (UCl.asm ((B.subst (up (inst t))).subst (repl (NFm.start B t))).full
          :: Γ.map UCl.shift)
        ((B.subst (up (inst t))).subst (repl (succ (var 0)))).full) :
      OCPrf Γ (.D B)
  /-- Open: from `D_{x,y} B` and a derivation of `A` under the closure clause
  of `B` at the witness read off its rows, infer `A`. -/
  | opn {n : ℕ} {Γ : List (UCl n)} {B : NFm (n + 2)} {A : NFm n} (h₁ : OCPrf Γ (.D B))
      (h₂ : OCPrf (UCl.clo (NFm.osel B) :: Γ.map UCl.shift) A.shift) : OCPrf Γ A

namespace OCPrf

variable {Γ Δ : List (UCl n)} {A : NFm n}

/-- Reflexivity, by the fixed clause. -/
theorem refl (hr : UCl.refl ∈ Γ) (t : Tm n) : OCPrf Γ (.eq t.full t.full) :=
  OCPrf.use (c := UCl.refl) t hr (fun A hA => by cases hA)

/-- An ordinary assumption of the context holds. -/
theorem asmHyp {X : NFm n} (hX : X.full = X) (h : UCl.asm X ∈ Γ) : OCPrf Γ X := by
  have k := OCPrf.use (c := UCl.asm X) zero h (fun A hA => by cases hA)
  have e : ((UCl.asm X).cons.subst (inst zero)).full = X := by
    show (X.shift.subst (inst zero)).full = X
    rw [NFm.subst_inst_shift, hX]
  rwa [e] at k

/-! ### Structural rules -/

theorem weaken (h : OCPrf Γ A) : ∀ {Δ : List (UCl n)}, Γ ⊆ Δ → OCPrf Δ A := by
  induction h with
  | use t hc _ ih => intro Δ s; exact .use t (s hc) fun A hA => ih A hA s
  | intro B t hB hQ ht _ ih =>
    intro Δ s
    exact .intro B t hB hQ ht (ih (List.cons_subset_cons _ (List.map_subset _ s)))
  | opn _ _ ih₁ ih₂ =>
    intro Δ s
    exact .opn (ih₁ s) (ih₂ (List.cons_subset_cons _ (List.map_subset _ s)))

theorem wk {c : UCl n} (h : OCPrf Γ A) : OCPrf (c :: Γ) A :=
  h.weaken (List.subset_cons_self _ _)

/-- Renaming of the free variables of a derivation. -/
theorem ren (h : OCPrf Γ A) : ∀ {m : ℕ} (ξ : Fin n → Fin m),
    OCPrf (Γ.map fun c => c.subst fun i => (Syn.var (ξ i) : Tm m))
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
  | @opn _ Γ B A _ _ ih₁ ih₂ =>
    intro m ξ
    have h₂ := ih₂ (Tm.upRen ξ)
    rw [List.map_cons, UCl.clo_subst_rn, ← Tm.up_rn, UCl.map_shift_subst, NFm.shift_subst_up,
      ← NFm.osel_rn] at h₂
    exact .opn (ih₁ ξ) h₂

theorem shift (h : OCPrf Γ A) : OCPrf (Γ.map UCl.shift) A.shift := h.ren Fin.succ

end OCPrf

namespace NFm

/-- A matrix with a dummy witness coordinate never selects a term. -/
theorem not_otest_dummy (M : NFm (n + 1)) :
    ¬∃ r, OTest (M.subst (up fun i => Syn.var i.succ)) r := by
  rintro ⟨r, -, h⟩
  rw [NFm.subst_dummy_up_inst, show (succ zero : Tm (n + 1)) = Syn.shift (succ zero) from rfl,
    ← NFm.shift_subst_inst, NFm.full_shift] at h
  generalize (M.subst (inst (succ zero))).full = X at h
  cases X with
  | eq a c =>
    change NFm.eq (Syn.shift a) (Syn.shift c) = _ at h
    have e := (NFm.eq.inj h).1
    cases a with
    | var j => change Tm.var j.succ = Tm.var 0 at e; exact Fin.succ_ne_zero j (Tm.var.inj e)
    | zero => change Tm.zero = Tm.var 0 at e; cases e
    | succ t => change Tm.succ _ = Tm.var 0 at e; cases e
    | iter c a h' => change Tm.iter _ _ _ = Tm.var 0 at e; cases e
  | Q B => change NFm.Q _ = _ at h; cases h
  | D B => change NFm.D _ = _ at h; cases h

theorem osel_dummy (M : NFm (n + 1)) :
    osel (M.subst (up fun i => Syn.var i.succ)) = M.full.subst (up fun i => Syn.var i.succ) := by
  rw [osel_neg (not_otest_dummy M), NFm.full_dummy]

end NFm

namespace OCPrf

variable {Γ Δ : List (UCl n)} {A : NFm n}

/-! ### Derived rules -/

/-- Introduction of the `D` formula that stands for `Q`, by cases. -/
theorem qI (M : NFm (n + 1)) (hM : M.full = M) (hQ : M.QFree)
    (h : OCPrf (UCl.asm (M.subst (repl zero)).full :: Γ.map UCl.shift)
      (M.subst (repl (succ (Syn.var 0)))).full) :
    OCPrf Γ (.D (M.subst (up fun i => Syn.var i.succ))) := by
  refine .intro _ (succ zero) (by rw [NFm.full_dummy, hM]) ((NFm.qfree_subst _ _).2 hQ) rfl ?_
  rw [NFm.start_of_not (fun h => by cases h.2), NFm.subst_dummy_inst]
  exact h

/-- The closure clause of a matrix gives the `D` formula that stands for `Q`. -/
theorem ofClause (M : NFm (n + 1)) (hM : M.full = M) (hQ : M.QFree) (hc : UCl.clo M ∈ Γ) :
    OCPrf Γ (.D (M.subst (up fun i => Syn.var i.succ))) := by
  refine qI M hM hQ ?_
  have ha : OCPrf (UCl.asm (M.subst (repl zero)).full :: Γ.map UCl.shift)
      (M.subst (inst zero)).full.shift := by
    rw [← NFm.full_shift, NFm.shift_subst_inst_zero]
    exact asmHyp (NFm.full_idem _) List.mem_cons_self
  have k : OCPrf (UCl.asm (M.subst (repl zero)).full :: Γ.map UCl.shift)
      ((M.subst (up fun i => Syn.var i.succ)).subst (inst (succ (Syn.var 0)))).full :=
    OCPrf.use (c := (UCl.clo M).shift)
      (succ (Syn.var 0)) (List.mem_cons_of_mem _ (List.mem_map_of_mem hc))
      (fun A hA => by obtain rfl := Option.some.inj hA; exact ha)
  rwa [NFm.subst_dummy_up_inst _ (succ (Syn.var 0))] at k

/-- `QE`, for the `D` formula that stands for `Q`: on a matrix with a dummy
witness coordinate the test fails, and Open is the ordinary opening. -/
theorem qE (M : NFm (n + 1)) (t : Tm n)
    (h₁ : OCPrf Γ (.D (M.subst (up fun i => Syn.var i.succ))))
    (h₂ : OCPrf Γ (M.subst (inst zero)).full) : OCPrf Γ (M.subst (inst t)).full := by
  refine .opn h₁ ?_
  rw [NFm.osel_dummy]
  have e : ∀ c : Tm (n + 1), ((M.full.subst (up fun i => Syn.var i.succ)).subst (inst c)).full
      = (M.subst (repl c)).full := fun c => by
    rw [NFm.subst_dummy_up_inst]
    exact NFm.full_subst_congr (NFm.full_idem _) fun _ => rfl
  have ha : OCPrf (UCl.clo (M.full.subst (up fun i => Syn.var i.succ)) :: Γ.map UCl.shift)
      ((M.full.subst (up fun i => Syn.var i.succ)).subst (inst zero)).full := by
    rw [e, ← NFm.shift_subst_inst_zero, NFm.full_shift]
    exact h₂.shift.wk
  have k : OCPrf (UCl.clo (M.full.subst (up fun i => Syn.var i.succ)) :: Γ.map UCl.shift)
      ((M.full.subst (up fun i => Syn.var i.succ)).subst (inst (Syn.shift t))).full :=
    OCPrf.use (c := UCl.clo _) (Syn.shift t) List.mem_cons_self
      (fun A hA => by obtain rfl := Option.some.inj hA; exact ha)
  rwa [e, ← NFm.shift_subst_inst, NFm.full_shift] at k

/-- Numerical cases, for a normal matrix. -/
theorem cases (M : NFm (n + 1)) (hM : M.full = M) (hQ : M.QFree) (t : Tm n)
    (h0 : OCPrf Γ (M.subst (inst zero)).full)
    (hS : OCPrf (UCl.asm (M.subst (repl zero)).full :: Γ.map UCl.shift)
      (M.subst (repl (succ (Syn.var 0)))).full) : OCPrf Γ (M.subst (inst t)).full :=
  qE M t (qI M hM hQ hS) h0

/-! ### Soundness in the kernel -/

theorem toNPrf (h : OCPrf Γ A) : NPrf (Γ.map fun c => c.toCl.toN) A := by
  induction h with
  | @use _ Γ c t hc _ ih =>
    refine (equivFull _).mp (NPrf.allE t (NPrf.impE
      (.hyp (List.mem_map_of_mem (f := fun c : UCl _ => c.toCl.toN) hc)) ?_))
    obtain ⟨a, b⟩ := c
    cases a with
    | none => exact NPrf.eqRefl zero
    | some X => exact ih X rfl
  | @intro _ Γ B t _ _ _ _ ih =>
    rw [List.map_cons, UCl.map_toN_shift] at ih
    exact .ofDI B t ((equivFull _).mpr
      (NPrf.cut1 (NPrf.asmClause ((equivFull _).mp NPrf.hyp0)) (NPrf.wkUnder ih)))
  | @opn _ Γ B A _ _ ih₁ ih₂ =>
    rw [List.map_cons, UCl.map_toN_shift] at ih₂
    have cl : NPrf (.Q B :: (Γ.map fun c => c.toCl.toN).map NFm.shift)
        (NFm.imp ((NFm.osel B).subst (inst zero)).full (NFm.all (NFm.osel B))) :=
      NPrf.impI (NPrf.impE ((NPrf.qComp (NEquiv.refl _)).mpr (NPrf.owitQ B NPrf.hyp0)).wk
        ((equivFull _).mpr NPrf.hyp0))
    exact .dE ih₁ (NPrf.cut1 cl (NPrf.wkUnder ih₂))

end OCPrf

/-! ### The packet for Open -/

namespace NFm

/-- The matrix of the packet for Open.  Its rows at `y = 0, 1, 2` are `0 = 0`,
`x = T` and `H(x) = U`: the second row is the one that Open reads. -/
def opkt (H : Tm (n + 1)) (T U : Tm n) : NFm (n + 2) :=
  .eq (Tm.sel (Syn.var 0) zero (Tm.sel (Tm.npar (Syn.var 0))
        (Syn.subst (Fin.cases (Syn.var 1) fun i => Syn.var i.succ.succ) H) (Syn.var 1)))
    (Tm.sel (Syn.var 0) zero (Tm.sel (Tm.npar (Syn.var 0)) (Syn.shift (Syn.shift U))
        (Syn.shift (Syn.shift T))))

theorem opkt_inst (H : Tm (n + 1)) (T U : Tm n) (c : Tm (n + 1)) :
    (opkt H T U).subst (inst c)
      = .eq (Tm.sel c zero (Tm.sel (Tm.npar c) H (Syn.var 0)))
          (Tm.sel c zero (Tm.sel (Tm.npar c) (Syn.shift U) (Syn.shift T))) := by
  simp [opkt, Tm.subst_hole1]

theorem opkt_row0 (H : Tm (n + 1)) (T U : Tm n) :
    ((opkt H T U).subst (inst zero)).full = .eq zero zero := by
  rw [opkt_inst]
  rfl

theorem opkt_row1 (H : Tm (n + 1)) (T U : Tm n) :
    ((opkt H T U).subst (inst (succ zero))).full = .eq (Syn.var 0) (Syn.shift T.full) := by
  rw [opkt_inst]
  show NFm.eq (Tm.full _) (Tm.full _) = _
  rw [Tm.full_sel_succ' (c := succ zero) (x := zero) rfl,
    Tm.full_sel_succ' (c := succ zero) (x := zero) rfl,
    Tm.full_sel_succ' (c := Tm.npar (succ zero)) (x := zero) Tm.full_npar_one,
    Tm.full_sel_succ' (c := Tm.npar (succ zero)) (x := zero) Tm.full_npar_one, Tm.full_shift]
  rfl

theorem opkt_row2 (H : Tm (n + 1)) (T U : Tm n) :
    ((opkt H T U).subst (inst (succ (succ zero)))).full = .eq H.full (Syn.shift U.full) := by
  rw [opkt_inst]
  show NFm.eq (Tm.full _) (Tm.full _) = _
  rw [Tm.full_sel_succ' (c := succ (succ zero)) (x := succ zero) rfl,
    Tm.full_sel_succ' (c := succ (succ zero)) (x := succ zero) rfl,
    Tm.full_sel_zero' (c := Tm.npar (succ (succ zero))) Tm.full_npar_two,
    Tm.full_sel_zero' (c := Tm.npar (succ (succ zero))) Tm.full_npar_two, Tm.full_shift]

theorem opkt_wit (H : Tm (n + 1)) (S T U : Tm n) :
    ((opkt H T U).subst (up (inst S))).subst (repl (succ (Syn.var 0)))
      = .eq (Tm.sel (succ (Syn.var 0)) zero (Tm.sel (Tm.npar (succ (Syn.var 0)))
            (Syn.shift (Syn.subst (inst S) H)) (Syn.shift S)))
          (Tm.sel (succ (Syn.var 0)) zero (Tm.sel (Tm.npar (succ (Syn.var 0)))
            (Syn.shift U) (Syn.shift T))) := by
  simp [opkt, Tm.subst_hole2, Syn.subst_up_shift]

/-- A numeral row of a matrix at a substituted witness. -/
theorem full_row_repl (P : NFm (n + 2)) (w c : Tm (n + 1)) (hc : Syn.subst (repl w) c = c) :
    ((P.subst (up (repl w))).full.subst (inst c)).full
      = ((P.subst (inst c)).full.subst (repl w)).full := by
  have e : (P.subst (up (repl w))).subst (inst c) = (P.subst (inst c)).subst (repl w) := by
    rw [NFm.subst_subst, NFm.subst_subst]
    refine P.subst_ext fun i => ?_
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [hc]
    · simp
  exact (NFm.full_subst_congr (NFm.full_idem _) fun _ => rfl).trans
    ((congrArg NFm.full e).trans (NFm.full_subst_congr (NFm.full_idem _).symm fun _ => rfl))

/-- The row `H(x) = U` at the witness `T`. -/
theorem pkt_export (H : Tm (n + 1)) (T U : Tm n) :
    ((NFm.eq H.full (Syn.shift U.full)).subst (repl (Syn.shift T.full))).full
      = (NFm.eq (Syn.subst (inst T) H).full U.full).shift := by
  rw [NFm.full_subst_congr (A' := .eq H (Syn.shift U)) (σ' := repl (Syn.shift T))
      (by simp only [NFm.full, Tm.full_idem, Tm.full_shift]) (fun i => by
        refine Fin.cases ?_ (fun j => ?_) i
        · simp
        · rfl),
    ← NFm.shift_subst_inst, NFm.full_shift]
  simp only [NFm.subst_eq, NFm.full, Syn.subst_inst_shift]

end NFm

namespace OCPrf

variable {Γ Δ : List (UCl n)} {A : NFm n}

/-- **The packet for Open.**  Transport without the crossing: the packet is
introduced at the witness `S` from the two given equations, by cases on a
parity; its rows at a fresh `b` are `0 = 0` and `b = T`, so Open selects `T`,
and the third row of the opened clause is `H(T) = U`. -/
theorem packet (hr : UCl.refl ∈ Γ) (S T U : Tm n) (H : Tm (n + 1))
    (h₁ : OCPrf Γ (.eq S.full T.full))
    (h₂ : OCPrf Γ (.eq (Syn.subst (inst S) H).full U.full)) :
    OCPrf Γ (.eq (Syn.subst (inst T) H).full U.full) := by
  have row : ∀ c : Tm (n + 1), ((NFm.opkt H T U).full.subst (inst c)).full
      = ((NFm.opkt H T U).subst (inst c)).full := fun c =>
    NFm.full_subst_congr (NFm.full_idem _) fun _ => rfl
  have hD : OCPrf Γ (.D (NFm.opkt H T U).full) := by
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
  have r0 : ((NFm.osel (NFm.opkt H T U).full).subst (inst zero)).full = .eq zero zero := by
    unfold NFm.osel
    rw [hw, NFm.full_row_repl _ _ zero rfl, row, NFm.opkt_row0]
    rfl
  have r2 : ((NFm.osel (NFm.opkt H T U).full).subst (inst (succ (succ zero)))).full
      = (NFm.eq (Syn.subst (inst T) H).full U.full).shift := by
    unfold NFm.osel
    rw [hw, NFm.full_row_repl _ _ (succ (succ zero)) rfl, row, NFm.opkt_row2, NFm.pkt_export]
  refine .opn hD ?_
  have k : OCPrf (UCl.clo (NFm.osel (NFm.opkt H T U).full) :: Γ.map UCl.shift)
      ((NFm.osel (NFm.opkt H T U).full).subst (inst (succ (succ zero)))).full :=
    OCPrf.use (c := UCl.clo _) (succ (succ zero)) List.mem_cons_self (fun A hA => by
      have e : ((NFm.osel (NFm.opkt H T U).full).subst (inst zero)).full = A :=
        Option.some.inj hA
      rw [← e, r0]
      exact OCPrf.refl (UCl.refl_mem_lift hr _) zero)
  rwa [r2] at k

/-- Symmetry: transport at the template `x`. -/
theorem symm (hr : UCl.refl ∈ Γ) {a c : Tm n} (h : OCPrf Γ (.eq a.full c.full)) :
    OCPrf Γ (.eq c.full a.full) :=
  packet hr a c a (Syn.var 0) h (OCPrf.refl hr a)

/-- Transport in one term, as in the kernel. -/
theorem trOne (hr : UCl.refl ∈ Γ) (S T U : Tm n) (H : Tm (n + 1))
    (h₁ : OCPrf Γ (.eq S.full T.full))
    (h₂ : OCPrf Γ (.eq (Syn.subst (inst S) H).full U.full)) :
    OCPrf Γ (.eq U.full (Syn.subst (inst T) H).full) :=
  symm hr (packet hr S T U H h₁ h₂)

end OCPrf

/-! ### The test fails on the auxiliary matrix of an introduction at `0` -/

theorem Tm.val_full (t : Tm n) (ρ : Fin n → ℕ) : t.full.val .std ρ = t.val .std ρ := by
  have h : t.val .std ρ = t.full.val .std ρ :=
    (NPrf.eqFull (Γ := []) t).sound_std ρ (fun _ hX => nomatch hX)
  exact h.symm

theorem Tm.tz_val (v : ℕ) (ρ : Fin n → ℕ) :
    (Tm.tz : Tm (n + 1)).val .std (Fin.cases v ρ) = 0 := by
  cases v <;> rfl

/-- For an equation `B`, the matrix `B(tz(x), y)` never selects a term: its
row at `1` has a value that does not depend on the fresh variable, since
`tz(x)` has the value `0` everywhere, so that row is not `x = r`. -/
theorem NFm.not_otest_tz (B : NFm (n + 2)) (hE : ∃ a b, B = .eq a b) :
    ¬∃ r, OTest (B.subst (up (repl Tm.tz))).full r := by
  obtain ⟨a, c, rfl⟩ := hE
  rintro ⟨r, -, h⟩
  change NFm.eq (Syn.subst (inst (succ zero)) (Syn.subst (up (repl Tm.tz)) a).full).full _
    = NFm.eq (Syn.var 0) r at h
  have e := (NFm.eq.inj h).1
  have key : ∀ v : ℕ, a.val .std (Fin.cases 1 (Fin.cases 0 fun _ => 0)) = v := by
    intro v
    have k : (Syn.subst (inst (succ zero)) (Syn.subst (up (repl Tm.tz)) a).full).full.val .std
          (Fin.cases v fun _ => 0)
        = (Syn.var 0 : Tm (n + 1)).val .std (Fin.cases v fun _ => 0) := by rw [e]
    rw [Tm.val_full, Tm.val_subst, Tm.val_inst, Tm.val_full, Tm.val_subst, Tm.val_up,
      Tm.val_repl, Tm.tz_val] at k
    exact k
  exact absurd ((key 0).symm.trans (key 1)) (by decide)

namespace OCPrf

variable {Γ Δ : List (UCl n)} {A : NFm n}

/-! ### The introductions of the kernel -/

/-- `DI` by cases for an equation at the literal witness `0`, where Intro
would take the progress step.  The witness `1` of `D_{x,y} B(tz(x), y)` gives
the case step; that formula is opened at its fresh variable, since the test
fails on it, and `D_{x,y} B` is introduced at the neutral witness `tz(b)`. -/
theorem dIZero (B : NFm (n + 2)) (hB : B.full = B) (hQ : B.QFree) (hE : ∃ a b, B = .eq a b)
    (h : OCPrf (UCl.asm ((B.subst (up (inst zero))).subst (repl zero)).full :: Γ.map UCl.shift)
      ((B.subst (up (inst zero))).subst (repl (succ (Syn.var 0)))).full) : OCPrf Γ (.D B) := by
  have hD : OCPrf Γ (.D (B.subst (up (repl Tm.tz))).full) := by
    refine .intro _ (succ zero) (NFm.full_idem _)
      ((NFm.qfree_full _).2 ((NFm.qfree_subst _ _).2 hQ)) rfl ?_
    rw [NFm.start_of_not (fun k => by cases k.2), NFm.full_tz_inst B (t := zero) rfl,
      NFm.full_tz_inst B (t := zero) rfl]
    exact h
  refine .opn hD ?_
  rw [NFm.osel_neg (NFm.not_otest_tz B hE), NFm.full_idem]
  have hB'' : (B.subst (up (up fun i => Syn.var i.succ))).full
      = B.subst (up (up fun i => Syn.var i.succ)) := by
    rw [Tm.up_rn Fin.succ, Tm.up_rn, NFm.full_rn, hB]
  show OCPrf _ (.D (B.subst (up (up fun i => Syn.var i.succ))))
  refine .intro _ (Tm.tz : Tm (n + 1)).full hB'' ((NFm.qfree_subst _ _).2 hQ)
    (Tm.full_idem _) ?_
  rw [NFm.start_of_not (fun k => Tm.tz_full_ne k.2), NFm.full_tz_goal, NFm.full_tz_goal]
  have e : ∀ c : Tm (n + 2),
      (((B.subst (up (repl Tm.tz))).full.subst (up fun i => Syn.var i.succ)).subst (inst c)).full
        = ((B.subst (up (repl Tm.tz))).subst (repl c)).full := by
    intro c
    rw [NFm.subst_dummy_up_inst]
    exact NFm.full_subst_congr (NFm.full_idem _) fun _ => rfl
  have ha : OCPrf (UCl.asm ((B.subst (up (repl Tm.tz))).subst (repl zero)).full
        :: (UCl.clo (B.subst (up (repl Tm.tz))).full :: Γ.map UCl.shift).map UCl.shift)
      ((B.subst (up (repl Tm.tz))).full.subst (inst zero)).full.shift := by
    rw [← NFm.full_shift, NFm.shift_subst_inst_zero,
      NFm.full_subst_congr (A' := B.subst (up (repl Tm.tz))) (σ' := repl zero)
        (NFm.full_idem _) (fun _ => rfl)]
    exact asmHyp (NFm.full_idem _) List.mem_cons_self
  have k : OCPrf (UCl.asm ((B.subst (up (repl Tm.tz))).subst (repl zero)).full
        :: (UCl.clo (B.subst (up (repl Tm.tz))).full :: Γ.map UCl.shift).map UCl.shift)
      (((B.subst (up (repl Tm.tz))).full.subst (up fun i => Syn.var i.succ)).subst
        (inst (succ (Syn.var 0)))).full :=
    OCPrf.use (c := (UCl.clo (B.subst (up (repl Tm.tz))).full).shift) (succ (Syn.var 0))
      (List.mem_cons_of_mem _ (List.mem_map_of_mem List.mem_cons_self)) (fun A hA => by
        have e' : ((B.subst (up (repl Tm.tz))).full.subst (inst zero)).full.shift = A :=
          Option.some.inj hA
        rw [← e']
        exact ha)
  rwa [e] at k

/-- Introduction of `D` by cases, as in the kernel. -/
theorem dICase (B : NFm (n + 2)) (hB : B.full = B) (hQ : B.QFree) (t : Tm n) (ht : t.full = t)
    (h : OCPrf (UCl.asm ((B.subst (up (inst t))).subst (repl zero)).full :: Γ.map UCl.shift)
      ((B.subst (up (inst t))).subst (repl (succ (Syn.var 0)))).full) : OCPrf Γ (.D B) := by
  by_cases hc : (∃ a b, B = NFm.eq a b) ∧ t = zero
  · obtain ⟨hE, rfl⟩ := hc
    exact dIZero B hB hQ hE h
  · refine .intro B t hB hQ ht ?_
    rw [NFm.start_of_not hc]
    exact h

/-- Progress for an equation: Intro at the literal `0`, with a dummy witness
coordinate. -/
theorem qIInd (a b : Tm (n + 1)) (ha : a.full = a) (hb : b.full = b)
    (h : OCPrf (UCl.asm (.eq a b) :: Γ.map UCl.shift)
      ((NFm.eq a b).subst (repl (succ (Syn.var 0)))).full) :
    OCPrf Γ (.D ((NFm.eq a b).subst (up fun i => Syn.var i.succ))) := by
  have hE : (NFm.eq a b).full = .eq a b := by simp only [NFm.full, ha, hb]
  refine .intro _ zero (by rw [NFm.full_dummy, hE]) trivial rfl ?_
  rw [show NFm.start ((NFm.eq a b).subst (up fun i => Syn.var i.succ)) (zero : Tm n) = Syn.var 0
    from rfl, NFm.subst_dummy_inst, NFm.subst_repl_var, hE]
  exact h

/-- From `Q`-free clauses only `Q`-free formulas are derivable. -/
theorem qfree (h : OCPrf Γ A) :
    (∀ c ∈ Γ, (∀ X, c.ante = some X → X.QFree) ∧ c.cons.QFree) → A.QFree := by
  induction h with
  | use t hc _ _ =>
    exact fun hΓ => (NFm.qfree_full _).2 ((NFm.qfree_subst _ _).2 (hΓ _ hc).2)
  | intro B t hB hQ ht _ _ => exact fun _ => hQ
  | @opn _ Γ B A _ _ ih₁ ih₂ =>
    intro hΓ
    have hB : B.QFree := ih₁ hΓ
    have hO : (NFm.osel B).QFree := (NFm.qfree_full _).2 ((NFm.qfree_subst _ _).2 hB)
    refine (NFm.qfree_subst A _).1 (ih₂ fun c hc => ?_)
    rcases List.mem_cons.1 hc with rfl | hc
    · refine ⟨fun X hX => ?_, hO⟩
      have e : ((NFm.osel B).subst (inst zero)).full = X := Option.some.inj hX
      rw [← e]
      exact (NFm.qfree_full _).2 ((NFm.qfree_subst _ _).2 hO)
    · obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
      refine ⟨fun X hX => ?_, (NFm.qfree_subst _ _).2 (hΓ d hd).2⟩
      obtain ⟨X₀, hX₀, rfl⟩ := Option.map_eq_some_iff.1 hX
      exact (NFm.qfree_subst _ _).2 ((hΓ d hd).1 X₀ hX₀)

end OCPrf

/-! ### Completeness, from the kernel -/

/-- Every kernel derivation, under any substitution, becomes a derivation with
Use, Intro and Open of the `Q`-free form in full normal form, once the
reflexivity clause is in the context and every hypothesis is derivable.  At
`DE` the branch is translated under the substitution that sends the fresh
variable to the selected witness, whatever it is. -/
theorem NPrf.toOC {Γ : List (NFm n)} {A : NFm n} (h : NPrf Γ A) :
    ∀ {m : ℕ} (σ : Fin n → Tm m) {Δ : List (UCl m)}, UCl.refl ∈ Δ →
      (∀ X ∈ Γ, OCPrf Δ (NFm.unQ (X.subst σ)).full) → OCPrf Δ (NFm.unQ (A.subst σ)).full := by
  induction h with
  | hyp h => intro m σ Δ _ sΓ; exact sΓ _ h
  | iterZero a h => intro m σ Δ hr _; exact OCPrf.refl hr (Syn.subst σ a)
  | iterSucc c a h =>
    intro m σ Δ hr _
    simp only [NFm.subst_eq, NFm.unQ, NFm.full, Tm.subst_iter, Tm.subst_succ,
      Syn.subst_subst_inst]
    rw [Tm.full_iterSucc]
    exact OCPrf.refl hr _
  | @trOne _ Γ h s t u _ _ ih₁ ih₂ =>
    intro m σ Δ hr sΓ
    have h₁ := ih₁ σ hr sΓ
    have h₂ := ih₂ σ hr sΓ
    simp only [NFm.subst_eq, NFm.unQ, NFm.full, Syn.subst_subst_inst] at h₁ h₂ ⊢
    exact OCPrf.trOne hr _ _ _ _ h₁ h₂
  | @qE _ Γ B t _ _ ih₁ ih₂ =>
    intro m σ Δ hr sΓ
    have e : ∀ u : Tm _, (NFm.unQ ((B.subst (inst u)).subst σ)).full
        = ((NFm.unQ (B.subst (up σ))).full.subst (inst (Syn.subst σ u))).full := fun u => by
      rw [NFm.subst_inst, NFm.unQ_subst]
      exact NFm.full_subst_congr (NFm.full_idem _).symm fun _ => rfl
    have h₁ : OCPrf Δ
        (.D ((NFm.unQ (B.subst (up σ))).full.subst (up fun i => Syn.var i.succ))) := by
      rw [← NFm.full_dummy]
      exact ih₁ σ hr sΓ
    have h₂ := ih₂ σ hr sΓ
    rw [e] at h₂ ⊢
    exact OCPrf.qE _ _ h₁ h₂
  | @dE n' Γ B A _ _ ih₁ ih₂ =>
    intro m σ Δ hr sΓ
    have h₁ : OCPrf Δ (.D (NFm.unQ (B.subst (up (up σ)))).full) := ih₁ σ hr sΓ
    refine .opn h₁ ?_
    obtain ⟨w, hw⟩ : ∃ w, NFm.owit (NFm.unQ (B.subst (up (up σ)))).full = w := ⟨_, rfl⟩
    have e₁ : ∀ X : NFm n', X.shift.subst (fun i => Syn.subst (repl w) (up σ i))
        = (X.subst σ).shift := by
      intro X
      unfold NFm.shift
      rw [NFm.subst_subst, NFm.subst_subst]
      refine X.subst_ext fun i => ?_
      simp
      rfl
    have hM : NFm.osel (NFm.unQ (B.subst (up (up σ)))).full
        = (NFm.unQ (B.subst (up fun i => Syn.subst (repl w) (up σ i)))).full := by
      unfold NFm.osel
      rw [hw, NFm.full_subst_congr (A' := NFm.unQ (B.subst (up (up σ)))) (σ' := up (repl w))
        (NFm.full_idem _) (fun _ => rfl), ← NFm.unQ_subst, NFm.subst_subst, Syn.up_comp]
    rw [hM]
    have k := ih₂ (fun i => Syn.subst (repl w) (up σ i))
      (Δ := UCl.clo (NFm.unQ (B.subst (up fun i => Syn.subst (repl w) (up σ i)))).full
        :: Δ.map UCl.shift)
      (UCl.refl_mem_lift hr _) (fun X hX => by
        rcases List.mem_cons.1 hX with rfl | hX
        · show OCPrf _ (.D ((NFm.unQ (B.subst (up fun i => Syn.subst (repl w) (up σ i)))).subst
            (up fun i => Syn.var i.succ)).full)
          rw [NFm.full_dummy]
          exact OCPrf.ofClause _ (NFm.full_idem _)
            ((NFm.qfree_full _).2 (NFm.qfree_unQ _)) List.mem_cons_self
        · obtain ⟨X₀, hX₀, rfl⟩ := List.mem_map.1 hX
          rw [e₁, NFm.unQ_shift, NFm.full_shift]
          exact (sΓ X₀ hX₀).shift.wk)
    rwa [e₁, NFm.unQ_shift, NFm.full_shift] at k
  | @dICase _ Γ B t _ ih =>
    intro m σ Δ hr sΓ
    have e : ∀ {k : ℕ} (ρ : Fin (m + 1) → Tm k),
        (((NFm.unQ (B.subst (up (up σ)))).full.subst (up (inst (Syn.subst σ t).full))).subst
            ρ).full
          = (NFm.unQ (((B.subst (up (up σ))).subst (up (inst (Syn.subst σ t)))).subst ρ)).full :=
      fun ρ => by
        rw [NFm.unQ_subst ((B.subst (up (up σ))).subst (up (inst (Syn.subst σ t)))) ρ,
          NFm.unQ_subst (B.subst (up (up σ))) (up (inst (Syn.subst σ t)))]
        exact NFm.full_subst_congr (NFm.full_subst_congr (NFm.full_idem _)
          (Tm.full_up_congr (Tm.full_inst _))) fun _ => rfl
    show OCPrf Δ (.D (NFm.unQ (B.subst (up (up σ)))).full)
    refine OCPrf.dICase _ (NFm.full_idem _) ((NFm.qfree_full _).2 (NFm.qfree_unQ _)) _
      (Tm.full_idem (Syn.subst σ t)) ?_
    rw [e, e]
    have k := ih (up σ)
      (Δ := UCl.asm (NFm.unQ (((B.subst (up (up σ))).subst (up (inst (Syn.subst σ t)))).subst
        (repl zero))).full :: Δ.map UCl.shift)
      (UCl.refl_mem_lift hr _) (fun X hX => by
        rcases List.mem_cons.1 hX with rfl | hX
        · rw [NFm.shift_subst_up, NFm.subst_inst, Tm.subst_zero, NFm.subst_up_inst,
            NFm.shift_subst_inst_zero]
          exact OCPrf.asmHyp (NFm.full_idem _) List.mem_cons_self
        · obtain ⟨X₀, hX₀, rfl⟩ := List.mem_map.1 hX
          rw [NFm.shift_subst_up, NFm.unQ_shift, NFm.full_shift]
          exact (sΓ X₀ hX₀).shift.wk)
    rwa [NFm.subst_repl_succ, NFm.subst_up_inst] at k
  | @qIInd _ Γ s₁ s₂ _ ih =>
    intro m σ Δ hr sΓ
    show OCPrf Δ (.D ((NFm.eq (Syn.subst (up σ) s₁) (Syn.subst (up σ) s₂)).subst
      (up fun i => Syn.var i.succ)).full)
    rw [NFm.full_dummy]
    show OCPrf Δ (.D ((NFm.eq (Syn.subst (up σ) s₁).full (Syn.subst (up σ) s₂).full).subst
      (up fun i => Syn.var i.succ)))
    refine OCPrf.qIInd _ _ (Tm.full_idem _) (Tm.full_idem _) ?_
    have k := ih (up σ)
      (Δ := UCl.asm (.eq (Syn.subst (up σ) s₁).full (Syn.subst (up σ) s₂).full)
        :: Δ.map UCl.shift)
      (UCl.refl_mem_lift hr _) (fun X hX => by
        rcases List.mem_cons.1 hX with rfl | hX
        · exact OCPrf.asmHyp (NFm.full_idem _) List.mem_cons_self
        · obtain ⟨X₀, hX₀, rfl⟩ := List.mem_map.1 hX
          rw [NFm.shift_subst_up, NFm.unQ_shift, NFm.full_shift]
          exact (sΓ X₀ hX₀).shift.wk)
    rw [NFm.subst_repl_succ] at k
    rw [NFm.full_subst_congr (A' := (NFm.eq s₁ s₂).subst (up σ)) (σ' := repl (succ (Syn.var 0)))
      (by simp only [NFm.subst_eq, NFm.full, Tm.full_idem]) (fun _ => rfl)]
    exact k

variable {Γ : List (NFm n)} {A : NFm n}

/-- **Three rule families with an inferred witness.**  The kernel derives a
sequent exactly when Use, Intro and Open derive the full normal form of its
`Q`-free form from the reflexivity clause and the corresponding assumptions. -/
theorem ocprf_iff_nprf :
    OCPrf (UCl.refl :: Γ.map fun X => UCl.asm (NFm.unQ X).full) (NFm.unQ A).full ↔ NPrf Γ A := by
  constructor
  · intro h
    refine (NEquiv.unQ A).mp ((equivFull _).mpr (h.toNPrf.cut fun C hC => ?_))
    rw [List.map_cons, List.mem_cons] at hC
    rcases hC with rfl | hC
    · exact NPrf.impI (NPrf.allI (NPrf.eqRefl _))
    · rw [List.map_map, List.mem_map] at hC
      obtain ⟨X, hX, rfl⟩ := hC
      exact NPrf.asmClause ((equivFull _).mp ((NEquiv.unQ X).mpr (.hyp hX)))
  · intro h
    have k := h.toOC Syn.var
      (Δ := UCl.refl :: Γ.map fun X => UCl.asm (NFm.unQ X).full) List.mem_cons_self
      fun X hX => by
        rw [NFm.subst_id]
        exact OCPrf.asmHyp (NFm.full_idem _) (List.mem_cons_of_mem _
          (List.mem_map_of_mem (f := fun X => UCl.asm (NFm.unQ X).full) hX))
    rwa [NFm.subst_id] at k

/-- On `Q`-free sequents Use, Intro and Open derive exactly what the kernel
derives, up to full normal forms. -/
theorem ocprf_iff_nprf_of_qfree (hΓ : ∀ X ∈ Γ, X.QFree) (hA : A.QFree) :
    OCPrf (UCl.refl :: Γ.map fun X => UCl.asm X.full) A.full ↔ NPrf Γ A := by
  have e : (Γ.map fun X => UCl.asm (NFm.unQ X).full) = Γ.map fun X => UCl.asm X.full :=
    List.map_congr_left fun X hX => by rw [NFm.unQ_of_qfree X (hΓ X hX)]
  rw [← ocprf_iff_nprf, e, NFm.unQ_of_qfree A hA]

/-- Use, Intro and Open prove a sequent in this form exactly when iPRA proves
its reading. -/
theorem ocprf_iff_pra :
    OCPrf (UCl.refl :: Γ.map fun X => UCl.asm (NFm.unQ X).full) (NFm.unQ A).full
      ↔ (Γ.map NFm.toPRA ⊢[PRAAx] A.toPRA) :=
  ocprf_iff_nprf.trans native_iff_pra

end LeanProofs.ConciseIPRA
